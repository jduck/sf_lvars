/*
 * Hex-Rays Superfluous Variable Plugin
 * v0.9
 *
 * Copyright (c) 2009 iDefense
 * ALL RIGHTS RESERVED.
 *
 * Written by Joshua J. Drake <jdrake.sf_lvars.SPAM.idefense.com>
 */

/*
 * NOTE1:
 * In some cases, the merging can result in a C representation 
 * that is not accurate.  Use at your own risk.
 *
 * one case in particular is:
 * v1 = a1;
 * func(&v1);
 *
 * in this case, the var is a stack var, and the location on the stack 
 * referenced will not match.  however, it is logically equivalent.
 */

/*
 * NOTE2:
 * It seems that doing this automatically on hxe_maturity would be
 * possible.  It seems resonable to identify simple variable assignments 
 * that are unnecessary and remove/merge them all.
 */

#include <hexrays.hpp>

// note: hiding the vars causes the action to be irreversible
// #define HIDE_SUPERFLUOUS_LVARS

// #define DEBUG
// #define DEBUG_ADD
// #define DO_RESET_NETNODE

// Hex-Rays API pointer
hexdsp_t *hexdsp = NULL;

static bool inited = false;

// The node to keep saved information.
static const char nodename[] = "$ hexrays sf_lvars";
static netnode node;

// Cached copy of superfluous local variables
class sflvar_t
{
public:
	ea_t func_ea;
	lvar_locator_t lv;

	sflvar_t(void)
	{
		lv = lvar_locator_t(BAD_ARGLOC, BADADDR);
		func_ea = BADADDR;
	}
	sflvar_t(lvar_locator_t rlv, ea_t fea)
	{
		lv = rlv;
		func_ea = fea;
	}

	DECLARE_COMPARISONS(sflvar_t)
	/* compare function guts */
	{
		/* greater/less than by ea */
		if (func_ea < r.func_ea)
			return -1;
		if (func_ea > r.func_ea)
			return 1;

		/* func_ea is equal, check the other two */
		if (lv.location == r.lv.location
			&& lv.defea == r.lv.defea)
			return 0;

		/* not equal, return error 
		   (nothing cares about the error of course) */
		return -2;
	};
};
typedef qvector<sflvar_t> sflvvec_t;
static sflvvec_t superfluous_vars;

/*
 * variable switcher class:
 * replace all occurences of 'ov' with 'nv'
 */
struct var_switcher_t : public ctree_visitor_t
{
	cexpr_t *ov;
	cexpr_t *nv;
	int found;

	var_switcher_t(cexpr_t *o, cexpr_t *n) : ctree_visitor_t(CV_FAST)
	{
		found = 0;
		ov = o;
		nv = n;
	}
	int idaapi visit_expr(cexpr_t *i)
	{
		if (i->op == cot_var 
			&& i->v.idx == ov->v.idx)
		{
			found = 1;
			cexpr_t *rs = new cexpr_t(*nv);
			i->replace_by(rs);
			return 1; // stop enumeration
		}
		return 0; // keep enumerating
	}
};


/*
 * assignment finder class:
 * look for an assignment to 'ov' that isn't assigning 'nv'
 */
struct var_finder_t : public ctree_visitor_t
{
	cexpr_t *ov;
	cexpr_t *nv;
	int found;

	var_finder_t(cexpr_t *o, cexpr_t *n) : ctree_visitor_t(CV_FAST)
	{
		found = 0;
		ov = o;
		nv = n;
	}
	int idaapi visit_expr(cexpr_t *i)
	{
		if (i->op == cot_asg 
			&& i->x->v.idx == ov->v.idx
			&& i->y->v.idx != nv->v.idx)
		{
			found = 1;
			return 1; // stop enumeration
		}
		return 0; // keep enumerating
	}
};


/*
 * assignment finder class:
 * look for an assignment of the specified var (of another var)
 */
struct asg_finder_t : public ctree_visitor_t
{
	int v;
	cexpr_t *found;

	asg_finder_t(int vidx) : ctree_visitor_t(CV_FAST)
	{
		found = NULL;
		v = vidx;
	}
	int idaapi visit_expr(cexpr_t *i)
	{
		// first assignment of a var to the specified var
		if (i->op == cot_asg 
			&& i->x->op == cot_var
			&& i->x->v.idx == v
			&& i->y->op == cot_var)
		{
			found = i;
			return 1; // stop enumeration
		}
		return 0; // keep enumerating
	}
};


/*
 * save the node data to the database
 */
static void save_node_data(void)
{
	// immediately save data into the database
	node.setblob(&superfluous_vars[0], superfluous_vars.size() * sizeof(sflvar_t), 0, 'I');
	node.altset(-1, superfluous_vars.size());
}


/*
 * add a superfluous variable to the netnode data
 */
static void add_superfluous_var(sflvar_t sflv)
{
	sflvvec_t::iterator p = superfluous_vars.find(sflv);

	// if we already have it, just forget it
	if (p != superfluous_vars.end())
	{
		msg("%s: lvar is already marked superfluous!\n", "sf_lvar");
		return;
	}
#ifdef DEBUG_ADD
	msg("%s: adding superfluous variable (func %a, def @ %a, %d)!\n", "sf_lvars",
		sflv.func_ea, sflv.lv.defea, sflv.lv.location);
#endif
	superfluous_vars.push_back(sflv);
	save_node_data();
}


/*
 * remove a superfluous variable from the netnode data
 */
static void remove_superfluous_var(sflvar_t &sflv)
{
	sflvvec_t::iterator p = superfluous_vars.find(sflv);

	// if we don't have it, just forget it
	if (p == superfluous_vars.end())
	{
		msg("%s: lvar is not marked superfluous!\n", "sf_lvar");
		return;
	}
	superfluous_vars.erase(p);
	save_node_data();
}


/*
 * check to see if the specified assignment is superfluous
 */
static bool assignment_is_superfluous(cexpr_t *asg, cexpr_t *e)
{
	/* for now we must only mess with varX = varY type assignments. */
	if (asg->x->op != cot_var
		|| asg->y->op != cot_var)
	{
#ifdef DEBUG
		msg("%s: selected assignment is too complex!\n", "sf_lvars");
#endif
		return false;
	}

	/* if an expression is specified, it must be the left side of 
	 * the assignment
	 */
	if (e && asg->x != e)
	{
#ifdef DEBUG
		msg("%s: selected var is not the assignee\n", "sf_lvars");
#endif
		return false;
	}

	/* no other assignments should be made to this variable */
	// NOTE: this is currently enforced when attempting to set the mark
	return true;
}


/*
 * Check if the item under the cursor is a variable that can be marked
 * as superfluous.
 *
 * If yes, return pointer to the corresponding "asg" ctree item
 */
static cexpr_t *find_var_asg(vdui_t &vu)
{
	// if its not an item, return false
	if (!vu.item.is_citem())
	{
#ifdef DEBUG
		msg("%s: selection is not a citem (%d)\n", "sf_lvars");
#endif
		return NULL;
	}

	// variable assignment?
	cexpr_t *e = vu.item.e;
	if (e->op != cot_var)
	{
#ifdef DEBUG
		msg("%s: selection is not a var\n", "sf_lvars");
#endif
		return NULL;
	}

	// get the parent (should be asg)
	citem_t *p = vu.cfunc->body.find_parent_of(e);
	if (!p)
	{
#ifdef DEBUG
		msg("%s: selection var has no parent\n", "sf_lvars");
#endif
		return NULL;
	}
	if (p->op != cot_asg) 
	{
#ifdef DEBUG
		msg("%s: selection var parent is not an assignment\n", "sf_lvars");
#endif
		return NULL;
	}

	cexpr_t *asg = (cexpr_t *)p;
	// both sides must be vars (for now), the left must be the selected item
	if (assignment_is_superfluous(asg, e))
		return asg;
	return NULL;
}

/*
 * remove the lvar from the lvar list
 */
static void remove_from_lvars(lvar_t &lv)
{
#ifdef HIDE_SUPERFLUOUS_LVARS
	// hide the variable from the lvar list
	lv.clear_used();
#else
	// we want to leave it visible, so we can remove the mark...
	// instead we'll add a comment to it?
	lv.cmt.clear();
	lv.cmt.append("SUPERFLUOUS");
#endif
}

/*
 * This function does the work of removing a superfluous variable.
 *
 * It is called by both the restoration and the manual selection procedures.
 */
static bool merge_var(cfunc_t *cfunc, cexpr_t *asg)
{
	// make sure we're dealing with:
	//  block->expr->asg->var1
	//                \-->var2
	cinsn_t *pe = (cinsn_t *)cfunc->body.find_parent_of(asg);
	if (!pe || pe->op != cit_expr)
	{
		msg("%s: eek! parent is not an expression!\n", "sf_lvars");
		return false;
	}
#ifdef DEBUG
	msg("%s: found expr parent\n", "sf_lvars");
#endif
	cinsn_t *pb = (cinsn_t *)cfunc->body.find_parent_of(pe);
	if (!pb || pb->op != cit_block)
	{
		msg("%s: eek! expression parent is not a block!\n", "sf_lvars");
		return false;
	}
#ifdef DEBUG
	msg("%s: found block parent\n", "sf_lvars");
#endif

	// temporarily set the expr to empty, we'll erase it later
	// this prevents us from replacing the var itself
	pe->op = cit_empty;

	// don't replace if there is another assignment to this var
	var_finder_t vf(asg->x, asg->y);
	vf.apply_to(&cfunc->body, NULL);
	if (vf.found)
	{
		msg("%s: merging vars with multiple assignments is not supported.  maybe a split will help...\n", "sf_lvars");
		pe->op = cit_expr;
		return false;
	}

#ifdef DEBUG
	// nice notification of what is to happen
	msg("%s: removing assignment @ 0x%lx\n", "sf_lvars", asg->ea);
#endif
#ifdef DEBUG
	char asg_buf[64];
	memset(asg_buf, 0, sizeof(asg_buf));
	asg->x->print1(asg_buf, sizeof(asg_buf), NULL);
	tag_remove(asg_buf, asg_buf, sizeof(asg_buf));
	char rs_buf[1024];
	memset(rs_buf, 0, sizeof(rs_buf));
	asg->y->print1(rs_buf, sizeof(rs_buf), NULL);
	tag_remove(rs_buf, rs_buf, sizeof(rs_buf));
	msg("%s: replacing all instances of \"%s\" with \"%s\"\n", "sf_lvars",
		asg_buf, rs_buf);
#endif

	// replace every reference to this variable with the right side 
	// of the assignment.
	while (1)
	{
		var_switcher_t vf(asg->x, asg->y);

		vf.apply_to(&cfunc->body, NULL);
		if (!vf.found)
			break;
	}

	// set it back, and ...
	pe->op = cit_expr;

	// remove the expr from the block
	cblock_t *cb = (cblock_t *)pb->cblock;
	for (cblock_t::iterator bi = cb->begin(); bi != cb->end(); bi++)
	{
		if (bi->op == cit_expr && bi->ea == pe->ea)
		{
			cb->erase(bi);
			break;
		}
	}
	return true;
}


/*
 * The user has selected to mark the variable superfluous (via the assignment)
 *
 * 1. Update the ctree
 * 2. Remember the operation
 * 3. refresh the ctree.
 */
static bool idaapi mark_superfluous(void *ud)
{
	vdui_t &vu = *(vdui_t *)ud;
	cexpr_t *asg = find_var_asg(vu);

	// this should never happen
	if (!asg)
		return false;
	int vidx = asg->x->v.idx;

	// #1
	if (!merge_var(vu.cfunc, asg))
		return false;

	// #2
	lvars_t &lvs = *vu.cfunc->get_lvars();
	lvar_t &lv = lvs[vidx];
	sflvar_t sflv(lv, vu.cfunc->entry_ea);
#ifdef DEBUG_ADD
	msg("%s: adding superfluous variable 1 (func %a, def @ %a, %d)!\n", "sf_lvars",
		vu.cfunc->entry_ea, lv.defea, lv.location);
	msg("%s: adding superfluous variable 2 (func %a, def @ %a, %d)!\n", "sf_lvars",
		sflv.func_ea, sflv.lv.defea, sflv.lv.location);
#endif
	add_superfluous_var(sflv);
	remove_from_lvars(lv);

	// #3
	vu.refresh_ctext();
	return true; // done
}


/*
 * called at maturity, reapplies any saved superfluous lvar modifications
 */
static void remove_superfluous_vars(cfunc_t *cfunc)
{
	lvars_t &lvs = *cfunc->get_lvars();

	sflvvec_t::iterator p;
	for (p = superfluous_vars.begin(); p != superfluous_vars.end(); p++)
	{
		/* ignore superfluous vars for other functions */
		if (p->func_ea != cfunc->entry_ea)
			continue;

		// find the index for this var
		lvar_t *plv = lvs.find(p->lv);
		if (!plv)
		{
			msg("%s: unable to find saved superfluous variable (func %a, def @ %a, %d)!\n", "sf_lvars",
				p->func_ea, p->lv.defea, p->lv.location);
			continue;
		}
		int vidx = lvs.find_lvar(plv->location, plv->width);
		if (vidx == -1)
		{
			msg("%s: unable to find saved variable's index!\n", "sf_lvars");
			continue;
		}

		// find the assignment to this variable
		asg_finder_t af(vidx);
		af.apply_to(&cfunc->body, NULL);
		if (!af.found)
			msg("%s: unable to find superfluous lvar's initial assignment!\n", "sf_lvars");
		else
		{
			if (merge_var(cfunc, af.found))
				remove_from_lvars(*plv);
		}
	}
}


/*
 * The user has selected to remove the superfluous mark from the variable (via lvars area)
 */
static bool idaapi unmark_superfluous(void *ud)
{
	vdui_t &vu = *(vdui_t *)ud;

	lvar_t *plv = vu.item.get_lvar();
	// lvars_t &lvs = *vu.cfunc->get_lvars();
	// int vidx = lvs.find_lvar(plv->location, plv->width);

	sflvar_t sflv(*plv, vu.cfunc->entry_ea);
	remove_superfluous_var(sflv);
	plv->cmt.clear();

	// refresh the entire view
	vu.refresh_view(false);
	return true; // done
}


/*
 * This callback handles the hexrays right-click and maturity events
 */
static int idaapi callback(void *, hexrays_event_t event, va_list va)
{
	switch ( event )
	{
		case hxe_right_click:
			{
				vdui_t &vu = *va_arg(va, vdui_t *);

				// pointing at the lvar itself (in local vars area)
				if (vu.item.citype == VDI_LVAR)
				{
					lvar_t *plv = vu.item.get_lvar();
					sflvar_t sflv(*plv, vu.cfunc->entry_ea);
					if (superfluous_vars.has(sflv))
						add_custom_viewer_popup_item(vu.ct, "Unmark as superfluous", "", unmark_superfluous, &vu);
					break;
				}

				// pointing at an assignment to the var
				if (find_var_asg(vu))
				{
					add_custom_viewer_popup_item(vu.ct, "Mark as superfluous", "", mark_superfluous, &vu);
					break;
				}
			}
			break;

		case hxe_maturity:
			if ( !superfluous_vars.empty() )
			{ 
				// If the ctree is ready, replay merge actions
				cfunc_t *cfunc = va_arg(va, cfunc_t *);
				ctree_maturity_t new_maturity = va_argi(va, ctree_maturity_t);
				if ( new_maturity == CMAT_FINAL ) // ctree is ready
					remove_superfluous_vars(cfunc);
			}
			break;
	}
  return 0;
}


/*
 * Initialize the plugin.
 */
int idaapi init(void)
{
	if (!init_hexrays_plugin())
		return PLUGIN_SKIP; // no decompiler

	if (!node.create(nodename)) // create failed -> node existed
	{
#ifdef DO_RESET_NETNODE
		// needed to reset bad data saved prior (where is the uber netnode manger plugin?)
		node.kill();
#endif
		size_t n = node.altval(-1);
		if ( n > 0 )
		{
			superfluous_vars.resize(n);
			n *= sizeof(sflvar_t);
			node.getblob(&superfluous_vars[0], &n, 0, 'I');
		}
	}

	install_hexrays_callback(callback, NULL);
	const char *hxver = get_hexrays_version();
	msg("Hex-rays version %s has been detected, %s ready to use\n", hxver, PLUGIN.wanted_name);
	inited = true;
	return PLUGIN_KEEP;
}

/*
 * clean up stuff (unload)
 */
void idaapi term(void)
{
	if ( inited )
	{
		// clean up
		remove_hexrays_callback(callback, NULL);
		term_hexrays_plugin();
	}
}

/*
 * run method for ida plugin
 */
void idaapi run(int)
{
	// should not be called because of PLUGIN_HIDE
}


//--------------------------------------------------------------------------
//
//      PLUGIN DESCRIPTION BLOCK
//
//--------------------------------------------------------------------------
static char comment[] = "Superfluous variable removal plugin for Hex-Rays decompiler";

plugin_t PLUGIN =
{
	IDP_INTERFACE_VERSION,
	PLUGIN_HIDE,          // plugin flags
	init,                 // initialize
	term,                 // terminate. this pointer may be NULL.
	run,                  // invoke plugin
	comment,              // long comment about the plugin
						  // it could appear in the status line
						  // or as a hint
	"",                   // multiline help about the plugin
	"Hex-Rays sf_lvars",  // the preferred short name of the plugin
	""                    // the preferred hotkey to run the plugin
};
