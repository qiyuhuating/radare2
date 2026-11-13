/* radare - LGPL - Copyright 2026 - pancake, phix33 */

// Region-AST structuring pass for the native pdc decompiler.
// Builds an if/else/loop/switch region tree over the function CFG using the
// dominator/post-dominator trees and DFS back edges. The `pdct` command dumps
// it; the structured pdc renderer (pdc.structured) consumes the tree.

#include <r_core.h>
#include "pdc_ast.h"
#include <errno.h>

typedef struct {
	RAnal *anal;
	RAnalFunction *fcn;
	RGraph *cfg;
	RGraphNode *entry;
	RGraph *dom_tree; // owned; built on the first CFG back edge
	HtUU *dom_pre; // lazily built dominator-tree DFS entry time
	HtUU *dom_post; // dominator-tree DFS exit time
	ut64 dom_tick;
	HtUU *ipdom;	// block addr => immediate post-dominator addr (UT64_MAX => exit)
	HtUP *loops;	// natural-loop header addr => HtUU* member set
	HtUU *cur_loop;	// members of the innermost loop being walked (NULL outside one)
	HtUU *emitted;	// block addr => 1 (each block heads a region at most once)
	HtUU *reachable; // opt-in: only emit nodes reachable via known CFG edges
	HtUU *decisions; // proven branch block address => surviving target
	HtUP *owned; // exact function block addresses, optional pruning mode
	int build_calls;
	int cap;
} PdcCtx;

static PdcRegion *region_new(PdcRegionType type, ut64 addr) {
	PdcRegion *r = R_NEW0 (PdcRegion);
	r->type = type;
	r->addr = addr;
	r->exit = UT64_MAX;
	RVecPdcRegionPtr_init (&r->children);
	return r;
}

static void region_free(PdcRegion *r) {
	if (!r) {
		return;
	}
	PdcRegion **it;
	R_VEC_FOREACH (&r->children, it) {
		region_free (*it);
	}
	RVecPdcRegionPtr_fini (&r->children);
	free (r);
}

static void region_add_child(PdcRegion *parent, PdcRegion *child, PdcRole role) {
	if (child) {
		child->role = role;
		RVecPdcRegionPtr_push_back (&parent->children, &child);
	}
}

// the conditional headed by addr, or NULL when neither arm yields a region
static PdcRegion *region_cond(ut64 addr, PdcRegion *then_r, PdcRegion *else_r) {
	if (then_r && else_r) {
		PdcRegion *r = region_new (PDC_R_IFELSE, addr);
		region_add_child (r, then_r, PDC_ROLE_JUMP);
		region_add_child (r, else_r, PDC_ROLE_FAIL);
		return r;
	}
	if (!then_r && !else_r) {
		return NULL;
	}
	PdcRegion *r = region_new (PDC_R_IF, addr);
	region_add_child (r, then_r? then_r: else_r, then_r? PDC_ROLE_JUMP: PDC_ROLE_FAIL);
	return r;
}

static ut64 htuu_get(HtUU *m, ut64 key, ut64 dflt) {
	bool found = false;
	const ut64 v = ht_uu_find (m, key, &found);
	return found? v: dflt;
}

static void ensure_dom_intervals(PdcCtx *ctx);

// DFS intervals make each dominance query constant time.
static bool dominates(PdcCtx *ctx, ut64 a, ut64 b) {
	if (!ctx->dom_pre) {
		ensure_dom_intervals (ctx);
	}
	if (!ctx->dom_pre || !ctx->dom_post) {
		return false;
	}
	const ut64 ap = htuu_get (ctx->dom_pre, a, UT64_MAX);
	const ut64 bp = htuu_get (ctx->dom_pre, b, UT64_MAX);
	if (ap == UT64_MAX || bp == UT64_MAX) {
		return false;
	}
	return ap <= bp && htuu_get (ctx->dom_post, b, UT64_MAX) <= htuu_get (ctx->dom_post, a, 0);
}

// grow the natural loop of a dominating header: header plus every node that
// reaches the latch without passing through the header
static void back_edge_cb(const RGraphEdge *e, RGraphVisitor *vis) {
	PdcCtx *ctx = vis->data;
	RAnalBlock *hb = e->to? e->to->data: NULL;
	RAnalBlock *tb = e->from? e->from->data: NULL;
	if (!hb || !tb || !dominates (ctx, hb->addr, tb->addr)) {
		return;
	}
	HtUU *set = ht_up_find (ctx->loops, hb->addr, NULL);
	if (!set) {
		set = ht_uu_new0 ();
		ht_uu_update (set, hb->addr, 1);
		ht_up_update (ctx->loops, hb->addr, set);
	}
	if (htuu_get (set, tb->addr, 0)) {
		return;
	}
	ht_uu_update (set, tb->addr, 1);
	RList *wl = r_list_new ();
	r_list_push (wl, e->from);
	RGraphNode *n;
	while ((n = r_list_pop (wl))) {
		RGraphNode **pit;
		R_VEC_FOREACH (&n->in_nodes, pit) {
			RAnalBlock *pb = (*pit)->data;
			if (pb && !htuu_get (set, pb->addr, 0)) {
				ht_uu_update (set, pb->addr, 1);
				r_list_push (wl, *pit);
			}
		}
	}
	r_list_free (wl);
}

static bool free_loop_set_cb(void *user, const ut64 k, const void *v) {
	ht_uu_free ((HtUU *)v);
	return true;
}

// dom/pdom tree node data is the *CFG* graph node, whose data is the RAnalBlock
static RAnalBlock *treenode_block(RGraphNode *tn) {
	RGraphNode *cnode = tn? (RGraphNode *)tn->data: NULL;
	return cnode? (RAnalBlock *)cnode->data: NULL;
}

static void mark_dom_enter(RGraphNode *n, RGraphVisitor *vis) {
	PdcCtx *ctx = vis->data;
	RAnalBlock *bb = treenode_block (n);
	if (bb) {
		ht_uu_update (ctx->dom_pre, bb->addr, ++ctx->dom_tick);
	}
}

static void mark_dom_leave(RGraphNode *n, RGraphVisitor *vis) {
	PdcCtx *ctx = vis->data;
	RAnalBlock *bb = treenode_block (n);
	if (bb) {
		ht_uu_update (ctx->dom_post, bb->addr, ++ctx->dom_tick);
	}
}

// No interval index is needed in an acyclic function.
static void ensure_dom_intervals(PdcCtx *ctx) {
	if (!ctx->dom_tree) {
		ctx->dom_tree = r_graph_dom_tree (ctx->cfg, ctx->entry);
		if (!ctx->dom_tree) {
			return;
		}
	}
	ctx->dom_pre = ht_uu_new0 ();
	ctx->dom_post = ht_uu_new0 ();
	if (!ctx->dom_pre || !ctx->dom_post) {
		return;
	}
	RGraphVisitor dom_vis = { .discover_node = mark_dom_enter,
		.finish_node = mark_dom_leave, .data = ctx };
	RListIter *it;
	RGraphNode *n;
	r_list_foreach (ctx->dom_tree->nodes, it, n) {
		if (RVecGraphNodePtr_empty (&n->in_nodes)) {
			r_graph_dfs_node (ctx->dom_tree, n, &dom_vis);
			break;
		}
	}
}

// fill dst[block addr] = tree-parent block addr (UT64_MAX for the root / sink)
static void collect_idom(HtUU *dst, RGraph *tree) {
	RListIter *it;
	RGraphNode *tn;
	r_list_foreach (tree->nodes, it, tn) {
		RAnalBlock *bb = treenode_block (tn);
		if (!bb) {
			continue;
		}
		ut64 parent = UT64_MAX;
		if (!RVecGraphNodePtr_empty (&tn->in_nodes)) {
			RGraphNode **p = RVecGraphNodePtr_at (&tn->in_nodes, 0);
			RAnalBlock *pb = p? treenode_block (*p): NULL;
			if (pb) {
				parent = pb->addr;
			}
		}
		ht_uu_update (dst, bb->addr, parent);
	}
}

static bool block_is_exit(RAnalBlock *bb) {
	return bb->jump == UT64_MAX && bb->fail == UT64_MAX
		&& (!bb->switch_op || r_list_empty (bb->switch_op->cases));
}

static PdcRegion *region_seq(PdcCtx *ctx, ut64 addr, ut64 stop);
static PdcRegion *build_region(PdcCtx *ctx, ut64 cur, ut64 stop, ut64 *next);
static PdcRegion *build_switch(PdcCtx *ctx, RAnalBlock *bb, ut64 *next);

// first post-dominator of h outside the loop: where control merges after it
static ut64 loop_exit_addr(PdcCtx *ctx, HtUU *set, ut64 h) {
	ut64 x = htuu_get (ctx->ipdom, h, UT64_MAX);
	int guard = ctx->cap;
	while (x != UT64_MAX && htuu_get (set, x, 0) && guard-- > 0) {
		x = htuu_get (ctx->ipdom, x, UT64_MAX);
	}
	return x;
}

static PdcRegion *build_loop(PdcCtx *ctx, RAnalBlock *bb, HtUU *set, ut64 *next) {
	const ut64 h = bb->addr;
	const ut64 j = bb->jump;
	const ut64 f = bb->fail;
	const bool j_in = j != UT64_MAX && htuu_get (set, j, 0);
	const bool f_in = f != UT64_MAX && htuu_get (set, f, 0);
	ut64 body_start = UT64_MAX;
	ut64 exit = UT64_MAX;
	PdcRegionType lt = PDC_R_DOWHILE;
	// a dispatcher header loops over its own jump table, not a j/f test
	const bool sw_head = bb->switch_op && !r_list_empty (bb->switch_op->cases);
	if (!sw_head && j != UT64_MAX && f != UT64_MAX && j_in != f_in) {
		body_start = j_in? j: f;
		exit = j_in? f: j;
		if (body_start != h) {
			lt = PDC_R_WHILE;
		}
	} else {
		// header does not test the exit: one-way, or both successors stay in
		body_start = j_in? j: (f_in? f: UT64_MAX);
		exit = loop_exit_addr (ctx, set, h);
	}
	PdcRegion *loop = region_new (lt, h);
	loop->exit = exit;
	HtUU *prev = ctx->cur_loop;
	ctx->cur_loop = set;
	if (sw_head) {
		ut64 swnext = UT64_MAX;
		region_add_child (loop, build_switch (ctx, bb, &swnext), PDC_ROLE_HEAD);
	} else if (j_in && f_in) {
		// both edges stay inside, so the header's own conditional is the body
		PdcRegion *then_r = region_seq (ctx, j, h);	// order is load-bearing
		PdcRegion *else_r = region_seq (ctx, f, h);
		region_add_child (loop, region_cond (h, then_r, else_r), PDC_ROLE_HEAD);
	} else if (body_start != UT64_MAX && body_start != h) {
		region_add_child (loop, region_seq (ctx, body_start, h),
			(body_start == j)? PDC_ROLE_JUMP: PDC_ROLE_FAIL);
	}
	ctx->cur_loop = prev;
	*next = exit;
	return loop;
}

static PdcRegion *build_switch(PdcCtx *ctx, RAnalBlock *bb, ut64 *next) {
	const ut64 join = htuu_get (ctx->ipdom, bb->addr, UT64_MAX);
	PdcRegion *sw = region_new (PDC_R_SWITCH, bb->addr);
	sw->exit = join;
	HtUU *seen = ht_uu_new0 ();
	RListIter *it;
	RAnalCaseOp *co;
	r_list_foreach (bb->switch_op->cases, it, co) {
		if (co->jump == UT64_MAX || htuu_get (seen, co->jump, 0)) {
			continue;
		}
		ht_uu_update (seen, co->jump, 1);
		region_add_child (sw, region_seq (ctx, co->jump, join), PDC_ROLE_CASE);
	}
	const ut64 defv = bb->switch_op->def_val;
	if (valid_addr (defv) && !htuu_get (seen, defv, 0)) {
		region_add_child (sw, region_seq (ctx, defv, join), PDC_ROLE_CASE);
	}
	ht_uu_free (seen);
	*next = join;
	return sw;
}

// build the region headed by cur; *next is where control continues after it
static PdcRegion *build_region(PdcCtx *ctx, ut64 cur, ut64 stop, ut64 *next) {
	*next = UT64_MAX;
	if (cur == UT64_MAX || cur == stop) {
		return NULL;
	}
	if (++ctx->build_calls > ctx->cap || htuu_get (ctx->emitted, cur, 0)) {
		return region_new (PDC_R_GOTO, cur);
	}
	RAnalBlock *bb = ctx->owned? ht_up_find (ctx->owned, cur, NULL): r_anal_get_block_at (ctx->anal, cur);
	// Only exact block starts owned by this function qualify in pruning mode.
	if (!bb || (!ctx->owned && !r_anal_function_contains (ctx->fcn, cur))
			|| (ctx->reachable && !htuu_get (ctx->reachable, cur, 0))) {
		return region_new (PDC_R_GOTO, cur);
	}
	ht_uu_update (ctx->emitted, cur, 1);
	const ut64 decided = ctx->decisions? htuu_get (ctx->decisions, cur, UT64_MAX): UT64_MAX;
	if (decided != UT64_MAX) {
		*next = decided;
		return region_new (PDC_R_BB, cur);
	}

	HtUU *loop_set = ht_up_find (ctx->loops, cur, NULL);
	if (loop_set) {
		return build_loop (ctx, bb, loop_set, next);
	}
	if (bb->switch_op && !r_list_empty (bb->switch_op->cases)) {
		return build_switch (ctx, bb, next);
	}
	if (bb->jump != UT64_MAX && bb->fail != UT64_MAX) {
		const ut64 join = htuu_get (ctx->ipdom, cur, UT64_MAX);
		PdcRegion *then_r = (bb->jump == join)? NULL: region_seq (ctx, bb->jump, join);
		PdcRegion *else_r = (bb->fail == join)? NULL: region_seq (ctx, bb->fail, join);
		*next = join;
		PdcRegion *r = region_cond (cur, then_r, else_r);
		return r? r: region_new (PDC_R_BB, cur);
	}
	// one-way (continue the enclosing seq) or return block; a block may carry
	// only a fail edge (fall-through split) with no jump
	*next = (bb->jump != UT64_MAX)? bb->jump: bb->fail;
	return region_new (PDC_R_BB, cur);
}

static PdcRegion *region_seq(PdcCtx *ctx, ut64 addr, ut64 stop) {
	PdcRegion *seq = region_new (PDC_R_SEQ, addr);
	ut64 cur = addr;
	int guard = ctx->cap;
	while (cur != UT64_MAX && cur != stop && guard-- > 0) {
		// leaving the loop or hitting an owned block ends the run with a jump
		const bool left = ctx->cur_loop && !htuu_get (ctx->cur_loop, cur, 0);
		if (left || htuu_get (ctx->emitted, cur, 0)) {
			region_add_child (seq, region_new (PDC_R_GOTO, cur), PDC_ROLE_SEQ);
			break;
		}
		ut64 next = UT64_MAX;
		PdcRegion *r = build_region (ctx, cur, stop, &next);
		if (!r) {
			break;
		}
		region_add_child (seq, r, PDC_ROLE_SEQ);
		cur = next;
	}
	const ut64 n = RVecPdcRegionPtr_length (&seq->children);
	if (n == 0) {
		region_free (seq);
		return NULL;
	}
	if (n == 1) {
		PdcRegion *only = *RVecPdcRegionPtr_at (&seq->children, 0);
		RVecPdcRegionPtr_fini (&seq->children);
		free (seq);
		return only;
	}
	return seq;
}

static const char *region_kind(PdcRegionType t) {
	switch (t) {
	case PDC_R_BB: return "bb";
	case PDC_R_SEQ: return "seq";
	case PDC_R_IF: return "if";
	case PDC_R_IFELSE: return "if-else";
	case PDC_R_WHILE: return "while";
	case PDC_R_DOWHILE: return "do-while";
	case PDC_R_SWITCH: return "switch";
	case PDC_R_BREAK: return "break";
	case PDC_R_CONTINUE: return "continue";
	case PDC_R_GOTO: return "goto";
	}
	return "?";
}

static void dump_region(PdcRegion *r, int indent, RStrBuf *sb) {
	r_strbuf_appendf (sb, "%*s%s 0x%08" PFMT64x "\n",
		indent * 2, "", region_kind (r->type), r->addr);
	PdcRegion **it;
	R_VEC_FOREACH (&r->children, it) {
		dump_region (*it, indent + 1, sb);
	}
}

typedef struct pdc_scope_t {
	const struct pdc_scope_t *up;
	ut64 brk;	// where break leaves this scope
	ut64 cont;	// where continue restarts it, UT64_MAX for a switch
} PdcScope;

// break binds to the innermost loop or switch and continue to the innermost
// loop, which the CFG walk cannot tell apart
static void classify_transfers(PdcRegion *r, const PdcScope *scope) {
	if (r->type == PDC_R_GOTO && scope) {
		const PdcScope *s = scope;
		while (s && s->cont == UT64_MAX) {	// continue skips switch scopes
			s = s->up;
		}
		if (s && r->addr == s->cont) {
			r->type = PDC_R_CONTINUE;
		} else if (r->addr == scope->brk) {
			r->type = PDC_R_BREAK;
		}
	}
	PdcScope inner = { scope, r->exit, r->addr };
	const PdcScope *sub = scope;
	if (r->type == PDC_R_WHILE || r->type == PDC_R_DOWHILE) {
		sub = &inner;
	} else if (r->type == PDC_R_SWITCH) {
		inner.cont = UT64_MAX;
		sub = &inner;
	}
	PdcRegion **it;
	R_VEC_FOREACH (&r->children, it) {
		classify_transfers (*it, sub);
	}
}

void pdc_plan_free(PdcPlan *plan) {
	if (plan) {
		region_free (plan->root);
		ht_uu_free (plan->reachable);
		free (plan);
	}
}

// a two-way block left to the orphan pass would lose one of its successors
static bool blocks_are_owned(RAnalFunction *fcn, HtUU *emitted, HtUU *reachable) {
	RAnalBlock **it;
	RAnalBlock *bb;
	R_VEC_FOREACH (&fcn->bbs, it) {
		bb = *it;
		if (reachable && !htuu_get (reachable, bb->addr, 0)) {
			continue;
		}
		if (bb->jump != UT64_MAX && bb->fail != UT64_MAX
				&& !htuu_get (emitted, bb->addr, 0)) {
			return false;
		}
	}
	return true;
}

static void mark_reachable(RGraphNode *n, RGraphVisitor *vis) {
	PdcCtx *ctx = vis->data;
	RAnalBlock *bb = n->data;
	if (bb) {
		ht_uu_update (ctx->reachable, bb->addr, 1);
	}
}

// Landing pads and filters have exceptional incoming edges absent from the CFG.
static void mark_exception_entry(PdcCtx *ctx, ut64 addr) {
	if (!valid_addr (addr)) {
		return;
	}
	RListIter *it;
	RGraphNode *n;
	r_list_foreach (ctx->cfg->nodes, it, n) {
		RAnalBlock *bb = n->data;
		if (addr >= bb->addr && addr - bb->addr < bb->size) {
			if (!htuu_get (ctx->reachable, bb->addr, 0)) {
				RGraphVisitor reach = { .discover_node = mark_reachable, .data = ctx };
				r_graph_dfs_node (ctx->cfg, n, &reach);
			}
			break;
		}
	}
}

static void mark_exception_reachable(RCore *core, PdcCtx *ctx) {
	RBinFile *bf = r_bin_cur (core->bin);
	const RVecRBinTrycatch *handlers = bf? r_bin_file_get_trycatch (bf): NULL;
	if (!handlers) {
		return;
	}
	const RBinTrycatch *tc;
	R_VEC_FOREACH (handlers, tc) {
		mark_exception_entry (ctx, tc->handler);
		mark_exception_entry (ctx, tc->filter);
	}
}

static void mark_known_reachable(RCore *core, PdcCtx *ctx) {
	RGraphVisitor reach = { .discover_node = mark_reachable, .data = ctx };
	r_graph_dfs_node (ctx->cfg, ctx->entry, &reach);
	mark_exception_reachable (core, ctx);
}

// Prove only local x86 zero-flag branches; unmodelled instructions are unknown.
typedef struct {
	RRegItem *reg; // ref-counted; released at the end of the proof
	ut64 value;
	bool zf_known;
	bool zf;
} PdcProof;

static bool proof_number(const char *text, ut64 *out) {
	if (!text || !*text) {
		return false;
	}
	char *end;
	errno = 0;
	const ut64 n = strtoull (text, &end, 0);
	if (errno || end == text || *end) {
		return false;
	}
	*out = n;
	return true;
}

static bool proof_value(RReg *regs, PdcProof *p, const char *s, ut64 *value) {
	if (proof_number (s, value)) {
		return true;
	}
	RRegItem *reg = r_reg_get (regs, s, -1);
	if (!reg) {
		return false;
	}
	const bool known = p->reg && reg->arena == p->reg->arena
		&& reg->offset == p->reg->offset && reg->size > 0
		&& reg->size <= p->reg->size && reg->size <= 64;
	if (known) {
		*value = p->value & (reg->size == 64? UT64_MAX: (UT64_MAX >> (64 - reg->size)));
	}
	r_unref (reg);
	return known;
}

static int proof_register_bits(RReg *regs, const char *name) {
	RRegItem *reg = r_reg_get (regs, name, -1);
	if (!reg) {
		return 0;
	}
	const int bits = reg->size;
	r_unref (reg);
	return bits > 0 && bits <= 64? bits: 0;
}

static void proof_register(RReg *regs, PdcProof *p, const char *name, ut64 value) {
	r_unref (p->reg);
	p->reg = r_reg_get (regs, name, -1);
	p->value = value;
}

static bool proof_step(RReg *regs, PdcProof *p, RAnalOp *op) {
	const char *esil = r_strbuf_get (&op->esil);
	char a[32], b[32];
	int end = 0;
	const int type = op->type & R_ANAL_OP_TYPE_MASK;
	if (type == R_ANAL_OP_TYPE_NOP) {
		return true;
	}
	if (type == R_ANAL_OP_TYPE_MOV) {
		ut64 value;
		if (sscanf (esil, "%31[^,],%31[^,],=%n", a, b, &end) == 2
				&& end && !esil[end] && proof_number (a, &value)) {
			proof_register (regs, p, b, value);
			if (p->reg) {
				return true;
			}
		}
		// Unmodelled moves and LEAs preserve x86 ZF, not tracked values.
		r_unref (p->reg);
		p->reg = NULL;
		return true;
	}
	if (type == R_ANAL_OP_TYPE_LEA) {
		r_unref (p->reg);
		p->reg = NULL;
		return true;
	}
	if (type == R_ANAL_OP_TYPE_XOR) {
		if (!op->mnemonic || sscanf (op->mnemonic, "xor %31[^,], %31s%n", a, b, &end) != 2
				|| !end || op->mnemonic[end] || strcmp (a, b)) {
			return false;
		}
		proof_register (regs, p, a, 0);
		p->zf_known = p->reg != NULL;
		p->zf = true;
		return p->zf_known;
	}
	if (type == R_ANAL_OP_TYPE_CMP) {
		if (sscanf (esil, "%31[^,],%31[^,],==,$z,zf,:=%n", a, b, &end) != 2 || !end) {
			return false;
		}
		RRegItem *same = !strcmp (a, b)? r_reg_get (regs, a, -1): NULL;
		p->zf_known = same != NULL;
		r_unref (same);
		if (p->zf_known) {
			p->zf = true;
		} else {
			// x86 comparisons use the register operand's width. ESIL can
			// sign-extend an imm8 to 64 bits even for a 32-bit CMP.
			const int abits = proof_register_bits (regs, a);
			const int bbits = proof_register_bits (regs, b);
			const int bits = abits? abits: bbits;
			ut64 x, y;
			p->zf_known = bits && (!abits || !bbits || abits == bbits)
				&& proof_value (regs, p, a, &x) && proof_value (regs, p, b, &y);
			if (p->zf_known) {
				const ut64 mask = bits == 64? UT64_MAX: UT64_MAX >> (64 - bits);
				p->zf = (x & mask) == (y & mask);
			}
		}
		return true;
	}
	if (type == R_ANAL_OP_TYPE_ACMP) {
		if (sscanf (esil, "0,%31[^,],%31[^,],&,==,$z,zf,:=%n", a, b, &end) != 2 || !end) {
			return false;
		}
		ut64 x, y;
		const bool kx = proof_value (regs, p, a, &x);
		const bool ky = proof_value (regs, p, b, &y);
		p->zf_known = (kx && !x) || (ky && !y) || (kx && ky);
		if (p->zf_known) {
			p->zf = (kx && !x) || (ky && !y) || !(x & y);
		}
		return true;
	}
	return false;
}

// A failed proof never changes the CFG. Each candidate has a strict instruction budget.
static bool proof_branch(RCore *core, RAnalBlock *bb, bool *taken) {
	if (strcmp (r_config_get (core->config, "asm.arch"), "x86")
			|| (r_config_get_i (core->config, "asm.bits") != 64
				&& r_config_get_i (core->config, "asm.bits") != 32)
			|| bb->jump == UT64_MAX || bb->fail == UT64_MAX
			|| bb->jump == bb->fail || bb->switch_op || bb->size > 192) {
		return false;
	}
	PdcProof p = {0};
	bool proved = false;
	ut64 off = 0;
	int i;
	for (i = 0; i < 32 && off < bb->size; i++) {
		RAnalOp *op = r_core_anal_op (core, bb->addr + off,
			R_ARCH_OP_MASK_ESIL | R_ARCH_OP_MASK_DISASM);
		if (!op || op->size < 1 || op->size > bb->size - off || op->delay) {
			r_anal_op_free (op);
			break;
		}
		off += op->size;
		const int type = op->type & R_ANAL_OP_TYPE_MASK;
		if (type == R_ANAL_OP_TYPE_CJMP && off == bb->size
				&& op->jump == bb->jump && op->fail == bb->fail && p.zf_known) {
			const char *s = r_strbuf_get (&op->esil);
			const bool negated = r_str_startswith (s, "zf,!,?{,");
			const char *start = negated? s + 8: (r_str_startswith (s, "zf,?{,")? s + 6: NULL);
			ut64 target;
			char *end;
			if (start) {
				target = strtoull (start, &end, 0);
				if (end != start && !strcmp (end, ",rip,=,}") && target == op->jump) {
					*taken = negated? !p.zf: p.zf;
					proved = true;
				}
			}
		} else if (type != R_ANAL_OP_TYPE_CJMP && !proof_step (core->anal->reg, &p, op)) {
			r_anal_op_free (op);
			break;
		}
		r_anal_op_free (op);
		if (proved) {
			break;
		}
	}
	r_unref (p.reg);
	return proved;
}

PdcPlan *pdc_plan_build(RCore *core, RAnalFunction *fcn) {
	R_RETURN_VAL_IF_FAIL (core && fcn, NULL);
	RGraphNode *entry = NULL;
	RGraph *g = r_anal_function_get_graph (fcn, &entry, fcn->addr);
	if (!g || !entry) {
		r_graph_free (g);
		return NULL;
	}
	PdcCtx ctx = {
		.anal = core->anal,
		.fcn = fcn,
		.cfg = g,
		.entry = entry,
		.dom_pre = NULL,
		.dom_post = NULL,
		.ipdom = ht_uu_new0 (),
		.loops = ht_up_new0 (),
		.emitted = ht_uu_new0 (),
		.reachable = r_config_get_b (core->config, "pdc.reachable")? ht_uu_new0 (): NULL,
		.decisions = r_config_get_b (core->config, "pdc.prove")
			&& r_config_get_b (core->config, "pdc.reachable")? ht_uu_new0 (): NULL,
		.owned = r_config_get_b (core->config, "pdc.reachable")? ht_up_new0 (): NULL,
		.cap = 4 * (int)RVecAnalBlockPtr_length (&fcn->bbs) + 64
	};

	if (ctx.owned) {
		RAnalBlock **it;
		R_VEC_FOREACH (&fcn->bbs, it) {
			ht_up_insert (ctx.owned, (*it)->addr, *it);
		}
	}

	if (ctx.reachable) {
		// The unmodified CFG bounds which blocks are worth decoding.
		mark_known_reachable (core, &ctx);
	}

	bool reduced = false;
	if (ctx.decisions) {
		RListIter *it;
		RGraphNode *n;
		r_list_foreach (g->nodes, it, n) {
			RAnalBlock *bb = n->data;
			bool taken;
			if (!htuu_get (ctx.reachable, bb->addr, 0) || !proof_branch (core, bb, &taken)) {
				continue;
			}
			const ut64 target = taken? bb->jump: bb->fail;
			const ut64 discarded = taken? bb->fail: bb->jump;
			RGraphNode *kept = NULL, *dropped = NULL;
			RGraphNode **child;
			R_VEC_FOREACH (&n->out_nodes, child) {
				RAnalBlock *successor = (*child)->data;
				if (successor->addr == target) {
					kept = *child;
				} else if (successor->addr == discarded) {
					dropped = *child;
				}
			}
			if (kept && dropped) {
				r_graph_del_edge (g, n, dropped);
				ht_uu_update (ctx.decisions, bb->addr, target);
				reduced = true;
			}
		}
	}

	if (ctx.reachable) {
		if (reduced) {
			// A proven edge can make its former successor unreachable.
			ht_uu_free (ctx.reachable);
			ctx.reachable = ht_uu_new0 ();
			mark_known_reachable (core, &ctx);
		}
		RVecGraphNodePtr unreachable;
		RVecGraphNodePtr_init (&unreachable);
		RListIter *it;
		RGraphNode *n;
		r_list_foreach (g->nodes, it, n) {
			RAnalBlock *bb = n->data;
			if (!htuu_get (ctx.reachable, bb->addr, 0)) {
				RVecGraphNodePtr_push_back (&unreachable, &n);
			}
		}
		r_graph_del_nodes (g, &unreachable);
		RVecGraphNodePtr_fini (&unreachable);
	}

	// Do not admit disconnected predecessors into a live natural-loop set.
	RGraphVisitor loops = { .back_edge = back_edge_cb, .data = &ctx };
	r_graph_dfs_node (g, entry, &loops);

	// add a virtual sink (addr UT64_MAX reads as "past function exit") so
	// post-dominance is well-defined on multi-exit functions
	RAnalBlock sink_bb = { .addr = UT64_MAX, .jump = UT64_MAX, .fail = UT64_MAX };
	RGraphNode *sink = r_graph_add_node (g, &sink_bb);
	if (sink) {
		RListIter *it;
		RGraphNode *cn;
		r_list_foreach (g->nodes, it, cn) {
			if (cn == sink) {
				continue;
			}
			RAnalBlock *bb = (RAnalBlock *)cn->data;
			if (bb && block_is_exit (bb)) {
				r_graph_add_edge (g, cn, sink);
			}
		}
		RGraph *pdt = r_graph_pdom_tree (g, sink);
		if (pdt) {
			collect_idom (ctx.ipdom, pdt);
			r_graph_free (pdt);
		}
	}

	PdcRegion *root = region_seq (&ctx, fcn->addr, UT64_MAX);
	// the orphan renderer drops a successor, so give unreached blocks a region
	if (root) {
		RAnalBlock **bit;
		RAnalBlock *b;
		PdcRegion *extra = NULL;
		R_VEC_FOREACH (&fcn->bbs, bit) {
			b = *bit;
			if ((ctx.reachable && !htuu_get (ctx.reachable, b->addr, 0))
					|| htuu_get (ctx.emitted, b->addr, 0)) {
				continue;
			}
			PdcRegion *r = region_seq (&ctx, b->addr, UT64_MAX);
			if (!r) {
				continue;
			}
			if (!extra) {
				extra = region_new (PDC_R_SEQ, root->addr);
				region_add_child (extra, root, PDC_ROLE_SEQ);
				root = extra;
			}
			region_add_child (extra, r, PDC_ROLE_SEQ);
		}
	}

	r_graph_free (ctx.dom_tree);
	r_graph_free (g);
	ht_uu_free (ctx.dom_pre);
	ht_uu_free (ctx.dom_post);
	ht_uu_free (ctx.ipdom);
	ht_uu_free (ctx.decisions);
	ht_up_free (ctx.owned);
	ht_up_foreach (ctx.loops, free_loop_set_cb, NULL);
	ht_up_free (ctx.loops);
	if (root) {
		classify_transfers (root, NULL);
	}
	PdcPlan *plan = R_NEW0 (PdcPlan);
	plan->root = root;
	plan->complete = blocks_are_owned (fcn, ctx.emitted, ctx.reachable);
	plan->reachable = ctx.reachable;
	ht_uu_free (ctx.emitted);
	return plan;
}

char *pdc_ast_dump(RCore *core, RAnalFunction *fcn) {
	PdcPlan *plan = pdc_plan_build (core, fcn);
	RStrBuf *sb = r_strbuf_new ("");
	if (plan && plan->root) {
		dump_region (plan->root, 0, sb);
	}
	pdc_plan_free (plan);
	return r_strbuf_drain (sb);
}
