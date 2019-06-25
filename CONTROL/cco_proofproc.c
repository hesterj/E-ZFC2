/*-----------------------------------------------------------------------

  File  : cco_proofproc.c

  Author: Stephan Schulz

  Contents

  Functions realizing the proof procedure.

  Copyright 1998--2018 by the author.
  This code is released under the GNU General Public Licence and
  the GNU Lesser General Public License.
  See the file COPYING in the main E directory for details..
  Run "eprover -h" for contact information.

  Created: Mon Jun  8 11:47:44 MET DST 1998

  -----------------------------------------------------------------------*/

#include "cco_proofproc.h"
#include "cco_watchlist.h"



/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/

PERF_CTR_DEFINE(ParamodTimer);
PERF_CTR_DEFINE(BWRWTimer);


/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/

void PrintTermStack(Sig_p sig, PStack_p stack);
TFormula_p TFormulaMergeVars(TFormula_p formula,  TB_p bank, Term_p x, Term_p y);
FormulaSet_p CreateNearbyFormulas(ProofState_p state, FormulaSet_p input, int distance);

/*  John's Functions
 * 
*/

WFormula_p NegIntroductionSimple(TB_p bank, WFormula_p a)
{
	TFormula_p a_tform = a->tformula;
	TFormula_p a_neg = TFormulaFCodeAlloc(bank,bank->sig->not_code,a_tform,NULL);
	
	WFormula_p handle = WTFormulaAlloc(bank,a_neg);
	return handle;
}

TFormula_p TFormulaMergeVars(TFormula_p formula,  TB_p bank, Term_p x, Term_p y)
{
   Subst_p  subst = SubstAlloc();
   TFormula_p new_tform;
   
   SubstAddBinding(subst, x,y);
   new_tform = TBInsertNoProps(bank, formula, DEREF_ALWAYS);
   SubstDelete(subst);

   return new_tform;
}

void PrintTermStack(Sig_p sig, PStack_p stack)
{
	for (PStackPointer i = 0; i<PStackGetSP(stack); i++)
	{
		TermPrint(GlobalOut,PStackElementP(stack,i),sig,DEREF_NEVER);
		putc('\n',GlobalOut);
	}
}

bool PStackFindTerm(PStack_p res, Term_p handle)
{
   PStackPointer i;

   for(i=0; i<PStackGetSP(res); i++)
   {
      if (TermStructEqual(PStackElementP(res,i),handle))
      {
		  return true;
	  }
   }
   return false;
}

PStack_p PStackRemoveDuplicatesTerm(PStack_p handle)
{
	PStackPointer i;
	PStack_p res = PStackAlloc();
	for(i=0; i<PStackGetSP(handle); i++)
	{
		if (!PStackFindTerm(res,PStackElementP(handle,i)))
		{
			PStackPushP(res,PStackElementP(handle,i));
		}
	}
	return res;
}
/*
FunCode VariableThatDoesNotOccurInStack(ProofState_p control, PStack_p handle)
{
	PStack_p function_symbols = PStackAlloc();
	FunCode minimal;
	
	LabelFunctionSymbols(control,handle->tformula,function_symbols);	
	
	PStackFree(function_symbols);
	return minimal;
}
*/
// returns the subterms of formulas in set

PStack_p FormulaSetCollectSubterms(ProofState_p control, FormulaSet_p set)
{
	PStack_p collector = PStackAlloc();
	WFormula_p handle = set->anchor->succ;
	PStack_p function_symbols = FormulaSetLabelFunctionSymbols(control,set);
	while (handle != set->anchor)
	{
		//WFormula_p copy = WFormulaFlatCopy(handle);
		CollectSubterms(control,handle->tformula,collector,function_symbols);
		//WFormulaFree(copy);
		handle = handle->succ;
	}
	//PStackFree(function_symbols);
	PStack_p res = PStackRemoveDuplicatesTerm(collector);
	PStackFree(function_symbols);
	PStackEmpty(collector);
	PStackFree(collector);
	return res;
}

//Labels the function symbols occuring in set, returns the stack of f_codes

PStack_p FormulaSetLabelFunctionSymbols(ProofState_p control, FormulaSet_p set)
{
	WFormula_p handle = set->anchor->succ;
	PStack_p function_symbols = PStackAlloc();
	while (handle != set->anchor)
	{
		LabelFunctionSymbols(control,handle->tformula,function_symbols);
		handle = handle->succ;
	}
	PStack_p res = PStackRemoveDuplicatesInt(function_symbols);
	
	PStackEmpty(function_symbols);
	PStackFree(function_symbols);
	return res;
}

PStack_p PStackRemoveDuplicatesInt(PStack_p handle)
{
	PStackPointer i;
	PStack_p res = PStackAlloc();
	for(i=0; i<PStackGetSP(handle); i++)
	{
		if (!PStackFindInt(res,PStackElementInt(handle,i)))
		{
			PStackPushInt(res,PStackElementInt(handle,i));
		}
	}
	//PStackFree(handle);
	return res;
}


/*
 *  collects the subterms of term recursively, by looking for the function symbols in the stack fsymbols
 *  
 * 
*/

long CollectSubterms(ProofState_p proofstate, Term_p term, PStack_p collector, PStack_p function_symbols)
{
	
	long res = 0;
	if (!term) return 0;
	if (term->f_code > 0)
	{
		if (PStackFindInt(function_symbols,term->f_code))
		{
			res += 1;
			PStackPushP(collector,term);
		}
		if (term->f_code != SIG_TRUE_CODE)
		{
			for (int i=0; i<term->arity;i++)
			{
				CollectSubterms(proofstate,term->args[i],collector,function_symbols);
			}
		}
	}
	else
	{
		res += 1;
		PStackPushP(collector,term);
	}
	return res;
}

//  returns true if handle is an element of res, only use this method if res is a stack consisting only of ints

bool PStackFindInt(PStack_p res, FunCode handle)
{
   PStackPointer i;

   for(i=0; i<PStackGetSP(res); i++)
   {
      if (PStackElementInt(res,i) == handle)
      {
		  return true;
	  }
   }
   return false;
}

int LabelFunctionSymbols(ProofState_p control, Term_p term, PStack_p function_symbols)
{
	Sig_p sig = control->signature;

	if (term->arity == 2 && ((term->args[0]->f_code == SIG_TRUE_CODE)
				|| (term->args[1]->f_code == SIG_TRUE_CODE)
				|| (term->args[0]->f_code == SIG_FALSE_CODE)
				|| (term->args[1]->f_code == SIG_FALSE_CODE)))
	{
		//printf("\nfound a predicate\n");
		//PStackPushInt(control->predicates,term->args[0]->f_code);
		for (int i=0; i<term->args[0]->arity; i++)
		{
			if (term->args[0]->args[i]->arity > 0)
			{
				LabelFunctionSymbols(control,term->args[0]->args[i],function_symbols);
			}
		}
	}
	else if (term->f_code == sig->eqn_code || term->f_code == sig->neqn_code)
	{
		//printf("\nfound equality\n");
		//PStackPushInt(control->predicates,term->f_code);
		for (int i=0; i<term->arity; i++)
		{
			if (term->args[i]->arity > 0)
			{
				LabelFunctionSymbols(control,term->args[i],function_symbols);
			}
		}
	}
	else if ((term->f_code == sig->not_code) || (term->f_code == sig->or_code)
											 || (term->f_code == sig->qall_code)
											 || (term->f_code == sig->qex_code)
											 || (term->f_code == sig->impl_code)
											 || (term->f_code == sig->equiv_code)
											 || (term->f_code == sig->and_code)
											 || (term->f_code == sig->bimpl_code))
	{
		//printf("\nfound a boolean\n");
		for (int i=0; i<term->arity; i++)
		{
			if (term->args[i]->arity > 0)
			{
				LabelFunctionSymbols(control,term->args[i],function_symbols);
			}
		}
	}
	else if (term->arity >= 0)
	{
		//printf("\nfound a function symbol\n");
		PStackPushInt(function_symbols,term->f_code);
		for (int i=0; i<term->arity; i++)
		{
			if (term->args[i]->arity > 0)
			{
				LabelFunctionSymbols(control,term->args[i],function_symbols);
			}
		}
	}
	return 0;
}

// ideally will create the nearby formulas of input subformulas within a reasonable "distance"

FormulaSet_p CreateNearbyFormulas(ProofState_p state, FormulaSet_p input, int distance)
{
	FormulaSet_p new_formulas = FormulaSetAlloc();
	WFormula_p handle = input->anchor->succ;
	TB_p bank = state->terms;
	
	while (handle != input->anchor)
	{
		if (handle->tformula->f_code != state->signature->not_code)
		{
			WFormula_p new = NegIntroductionSimple(bank, handle);
			FormulaSetInsert(new_formulas,new);
		}
		else
		{
			WFormula_p new = WTFormulaAlloc(bank,handle->tformula->args[0]);
			FormulaSetInsert(new_formulas,new);
		}
		handle = handle->succ;
	}
	
	return new_formulas;
}

// need to actually generalize now

FormulaSet_p GeneralizeFormulas(ProofState_p proofstate, FormulaSet_p input, int iterations)
{
	FormulaSet_p generalizations = FormulaSetAlloc();
	Sig_p sig = proofstate->signature;
	TB_p bank = proofstate->terms;
	
	// 6/24/19 Add some more subformula neighbors so that we will have more comprehension options
	FormulaSet_p subformula_neighbors = CreateNearbyFormulas(proofstate,input,iterations);
	FormulaSetInsertSet(input,subformula_neighbors);
	FormulaSetFree(subformula_neighbors);
	
	WFormula_p handle = input->anchor->succ;
	
	
	while (handle != input->anchor)
	{
		PStack_p all_subterms = FormulaSetCollectSubterms(proofstate, input);
		
		for (PStackPointer i = 0; i<PStackGetSP(all_subterms); i++)
		{
			Term_p current = PStackElementP(all_subterms,i);
			if (!TermIsSubterm(handle->tformula,current,DEREF_NEVER))
			{
				continue;
			}
			PStack_p subterm_generalizations = ComputeSubtermsGeneralizations(current, proofstate->terms->vars);
			for (PStackPointer j = 0; j<PStackGetSP(subterm_generalizations); j++)
			{
				Term_p generalization_of_current = PStackElementP(subterm_generalizations,j);
				TFormula_p replaced = TFormulaMergeVars(handle->tformula,bank,current,generalization_of_current);
				WFormula_p generalized_formula = WTFormulaAlloc(bank, replaced);
				FormulaSetInsert(generalizations,generalized_formula);
			}
		}
		
		handle = handle->succ;
	}
	return generalizations;
}

FormulaSet_p GenerateComprehensionInstances(ProofState_p proofstate, FormulaSet_p subformulas)
{
   TFormula_p term_encoded_subformula;
   FormulaSet_p comprehension_instances = FormulaSetAlloc();
   TFormula_p term_encoded_schema_instance;
   WFormula_p schema_formula;
   WFormula_p handle = subformulas->anchor->succ;
   //ClauseSet_p final = ClauseSetAlloc();
   Clause_p tobeevaluated;
   while (handle != subformulas->anchor)
   {
	   PStack_p free_variables_stack = PStackAlloc();
	   term_encoded_subformula = handle->tformula;
	   VarSet_p free_variables_set = tform_compute_freevars(proofstate->terms,term_encoded_subformula);
	   int free_variable_count = PTreeNodes(free_variables_set->vars);
	   PTree_p free_variables = free_variables_set->vars;
	   PTreeToPStack(free_variables_stack,free_variables);
	   /*
	   for (PStackPointer i=0;i<PStackGetSP(free_variables_stack);i++)
	   {
		   TermPrint(GlobalOut,PStackElementP(free_variables_stack,i),proofstate->signature,DEREF_NEVER);
		   printf("\n");
	   }
	   */
	   if (free_variable_count > 0)
	   {
		   for (PStackPointer i=0;i<PStackGetSP(free_variables_stack);i++)
		   {
			   TFormula_p subformula_copy = TFormulaCopy(proofstate->terms, term_encoded_subformula);
			   term_encoded_schema_instance = tformula_comprehension2(proofstate,free_variables_stack,i,subformula_copy);
			   schema_formula = WTFormulaAlloc(proofstate->terms,term_encoded_schema_instance);
			   FormulaSetProp(schema_formula,CPIsSchema);
			   /*
				if (OutputLevel >= 1)
				{
					fprintf(GlobalOut,   "COMPREHENSION: term: ");
					TermPrint(GlobalOut, schema_formula->tformula, proofstate->signature, DEREF_ALWAYS);
					fprintf(GlobalOut, "\n            formula: ");
					WFormulaPrint(GlobalOut, schema_formula, true);
					fprintf(GlobalOut, "\n");
				}
				*/
				/*
				long res = WFormulaCNF(schema_formula,final,proofstate->terms,proofstate->terms->vars);
				printf("\nC clauses: %ld\n",res);
				while ((tobeevaluated = ClauseSetExtractFirst(final)))
				{
					printf("\n@ ");
					ClausePrint(GlobalOut,tobeevaluated,true);
					ClauseSetProp(tobeevaluated, CPIsSchema);
					ClauseSetIndexedInsertClause(proofstate->axioms, tobeevaluated);
					//HCBClauseEvaluate(control->hcb, tobeevaluated);
				}
				WFormulaCellFree(schema_formula);
				printf("\n");
				printf("\nSuccessful comprehension\n");
				*/
				FormulaSetInsert(comprehension_instances,schema_formula);
			}
       }
	   //VarSetFree(free_variables_set);
	   PStackFree(free_variables_stack);
	   //ClauseSetFree(final);
	   handle = handle->succ;
   }
   return comprehension_instances;
}

bool TermIsPredicate(Term_p term)
{
	bool check = (term->arity == 2 && ((term->args[0]->f_code == SIG_TRUE_CODE)
				|| (term->args[1]->f_code == SIG_TRUE_CODE)));
	return check;
}

bool TermIsBooleanSymbol(Sig_p sig, Term_p term)
{
	FunCode fcode = term->f_code;
	bool check = (fcode == sig->eqn_code || fcode == sig->neqn_code
				|| (fcode == sig->not_code) || (fcode == sig->or_code)
											 || (fcode == sig->qall_code)
											 || (fcode == sig->qex_code)
											 || (fcode == sig->impl_code)
											 || (fcode == sig->equiv_code)
											 || (fcode == sig->and_code)
											 || (fcode == sig->bimpl_code));
	return check;
}

bool SubformulaCandidateCheck(Sig_p sig, Term_p term)
{
	bool check = (TermIsPredicate(term) || TermIsBooleanSymbol(sig,term));
	return check;
}
// collect all subformulas of the formulaset, store them in collector then pass them to a formulaset that is return

long FormulaSetCollectSubformulas(ProofState_p state, FormulaSet_p input, FormulaSet_p collector)
{
	WFormula_p handle = input->anchor->succ;
	long subformula_count = 0;
	while (handle != input->anchor)
	{
		subformula_count += WFormulaCollectSubformulas(state,handle,collector);
		handle = handle->succ;
	}
	return subformula_count;
}

//Wrapper for TFormulaCollectSubformulas

long WFormulaCollectSubformulas(ProofState_p state, WFormula_p input, FormulaSet_p collector)
{
	return TFormulaCollectSubformulas(state,input->tformula,collector);
}

//Collect all the subformulas of the input by looking for "terms" whose top FunCode is a predicate symbol
//This means that we need to worry about the situation where term encoded predicates are masked by an equality with $true

long TFormulaCollectSubformulas(ProofState_p state, TFormula_p term, FormulaSet_p collector)
{
	long subformula_count = 0;
	WFormula_p handle;
	Sig_p sig = state->signature;
	
	if (SubformulaCandidateCheck(sig,term))
	{
		handle = WTFormulaAlloc(state->terms,term);
		FormulaSetInsert(collector,handle);
		subformula_count++;
		for (int i=0; i<term->arity; i++)
		{
			if (term->args[i]->arity > 0)
			{
				subformula_count += TFormulaCollectSubformulas(state,term->args[i],collector);
			}
		}
	}
	return subformula_count;
}



//Redo of everything above but using E internal methods rather than printing to file (slow)

long compute_schemas_tform(ProofControl_p control, TB_p bank, OCB_p ocb, Clause_p clause,
			  ClauseSet_p store, VarBank_p
              freshvars, ProofState_p state) 
{
	if (ClauseQueryProp(clause, CPIsSchema))
	{
		printf("\nSelected schema instance\n");
      return 0;
	}
	
	long numfreevars = 0;
	long res = 0;
	TFormula_p clauseasformula;
	TFormula_p schemaformula;
	WFormula_p schemaaswformula;
	PTree_p freevars = NULL;
	ClauseSet_p final = ClauseSetAlloc();
	Clause_p tobeevaluated;
	Clause_p clausecopy = ClauseCopy(clause,bank);
	
	clauseasformula = TFormulaClauseEncode(bank, clausecopy);
   VarBankVarsSetProp(bank->vars, TPIsFreeVar);
	TFormulaCollectFreeVars(bank, clauseasformula, &freevars);
	numfreevars = PTreeNodes(freevars);
	
	if (numfreevars == 1)  //Comprehension
	{
		schemaformula = tformula_comprehension(bank, state, &freevars, clauseasformula);

		schemaaswformula = WTFormulaAlloc(bank,schemaformula);

      //yan
      /*
      if (OutputLevel >= 1)
      {
         fprintf(GlobalOut,   "COMPREHENSION: term: ");
         TermPrint(GlobalOut, schemaformula, bank->sig, DEREF_ALWAYS);
         fprintf(GlobalOut, "\n            formula: ");
         WFormulaPrint(GlobalOut, schemaaswformula, true);
         fprintf(GlobalOut, "\n");
      }
      */
      //

		res = WFormulaCNF(schemaaswformula,final,state->terms,/*state->freshvars*/bank->vars);
		printf("\nC clauses: %ld\n",res);
		while ((tobeevaluated = ClauseSetExtractFirst(final)))
		{
		  printf("\n@ ");
		  ClausePrint(GlobalOut,tobeevaluated,true);
          ClauseSetProp(tobeevaluated, CPIsSchema);
		  ClauseSetIndexedInsertClause(state->tmp_store, tobeevaluated);
		  //HCBClauseEvaluate(control->hcb, tobeevaluated);
		}
		WFormulaCellFree(schemaaswformula);
		printf("\n");
		printf("\nSuccessful comprehension\n");
	}
	/*
	else if (numfreevars == 2) // Replacement  //bugged
	{
		
		final = tformula_replacement(bank,state,&freevars,clauseasformula,clausecopy);
		
		while ((tobeevaluated = ClauseSetExtractFirst(final)))
		{
		  //printf("\n@ ");
		  //ClausePrint(GlobalOut,tobeevaluated,true);
        ClauseSetProp(tobeevaluated, CPIsSchema);
		  ClauseSetIndexedInsertClause(state->tmp_store, tobeevaluated);
		  HCBClauseEvaluate(control->hcb, tobeevaluated);
		  //printf("\n");
		}
		//WFormulaCellFree(schemaaswformula);
		//printf("\nSuccessful replacement\n");
	}
	*/
	ClauseSetFree(final);
	ClauseFree(clausecopy);
	PTreeFree(freevars);
	
	return 0;
}

//  Compute comprehension instance for TFormula_p with ONE free variable

TFormula_p tformula_comprehension(TB_p bank, ProofState_p state, PTree_p* freevars, TFormula_p input)
{
	FunCode member = SigFindFCode(state->signature, "member");
	//TFormula_p new = TFormulaCopy(bank,input);
   
	Term_p z = PTreeExtractRootKey(freevars);
   //Term_p x = VarBankVarAssertAlloc(bank->vars, z->f_code-2, STIndividuals);
   //Term_p y = VarBankVarAssertAlloc(bank->vars, x->f_code-2, STIndividuals);
   Term_p x = VarBankGetFreshVar(bank->vars, STIndividuals);
   Term_p y = VarBankGetFreshVar(bank->vars, STIndividuals);
	
   TFormula_p ziny0 = TFormulaFCodeAlloc(bank, member, z, y);
	TFormula_p zinx0 = TFormulaFCodeAlloc(bank, member, z, x);
	
   Eqn_p ziny1 = EqnAlloc(ziny0, bank->true_term, bank, true);
	Eqn_p zinx1 = EqnAlloc(zinx0, bank->true_term, bank, true);
	
	TFormula_p ziny2 = TFormulaLitAlloc(ziny1);
	TFormula_p zinx2 = TFormulaLitAlloc(zinx1);

	TFormula_p scheme = TFormulaFCodeAlloc(bank, bank->sig->and_code, zinx2, input);
	scheme = TFormulaFCodeAlloc(bank, bank->sig->equiv_code, ziny2, scheme);
	scheme = TFormulaAddQuantor(bank, scheme, true, z);
	scheme = TFormulaAddQuantor(bank, scheme, false, y);
	scheme = TFormulaAddQuantor(bank, scheme, true, x);
	
   EqnFree(ziny1);
	EqnFree(zinx1);
	
	return scheme;
	
	/*
	TFormula_p freevariable = (TFormula_p) pointer;
   
   TermPrint(GlobalOut, freevariable, bank->sig, DEREF_NEVER);
   fprintf(GlobalOut, "\n%ld  %d\n", freevariable->f_code, freevariable->sort);
	
	TFormula_p a = VarBankGetFreshVar(state->freshvars,freevariable->sort);
	TFormula_p b = VarBankGetFreshVar(state->freshvars,freevariable->sort);
	
	TFormula_p xina = TFormulaFCodeAlloc(bank,member,freevariable,a);
	TFormula_p xinb = TFormulaFCodeAlloc(bank,member,freevariable,b);
	
	Eqn_p xina_eq = EqnAlloc(xina,bank->true_term,bank,true);
	Eqn_p xinb_eq = EqnAlloc(xinb,bank->true_term,bank,true);
	
	TFormula_p xina_f = TFormulaLitAlloc(xina_eq);
	TFormula_p xinb_f = TFormulaLitAlloc(xinb_eq);
	
	input = TFormulaFCodeAlloc(bank,bank->sig->and_code,xina_f,input);
	input = TFormulaFCodeAlloc(bank,bank->sig->equiv_code,xinb_f,input);
	input = TFormulaAddQuantor(bank,input,true,freevariable);
	input = TFormulaAddQuantor(bank,input,false,b);
	input = TFormulaAddQuantor(bank,input,true,a);
	
	EqnFree(xina_eq);
	EqnFree(xinb_eq);
	
	return input;
   */
}

/*  This is a newer comprehension method that allows more than one free variable.  The "selected variable" is the one at position in the freevars stack
 *  All other free variables are considered to be parameters that are then universally quantified over, as in full comprehension
 * 
 * 
*/

TFormula_p tformula_comprehension2(ProofState_p state, PStack_p freevars, PStackPointer position, TFormula_p input)
{
	//void* pointer = PTreeExtractRootKey(freevars);
	void* pointer = PStackElementP(freevars,position);
	TB_p bank = state->terms;
	//FunCode member = SigFindFCode(state->signature, "member"); // TPTP
	FunCode member;
	if (SigFindFCode(state->signature, "r2_hidden"))
	{
		member = SigFindFCode(state->signature, "r2_hidden");
	}
	else if (SigFindFCode(state->signature, "member"))
	{
		member = SigFindFCode(state->signature, "member");
	}
	else 
	{
		fprintf(GlobalOut, "\nNo known membership symbol, aborting.");
		exit(0);
	}
	//TFormula_p new = TFormulaCopy(bank,input);
	
	TFormula_p freevariable = (TFormula_p) pointer;
	
	//find a fresh variable
	PStack_p function_symbols = PStackAlloc();
	PStack_p subterms = PStackAlloc();
	LabelFunctionSymbols(state,input,function_symbols);
	CollectSubterms(state,input,subterms,function_symbols);
	
	//printf("\nTerms found:\n");
	//PrintTermStack(state->signature,subterms);
	FunCode minimal = 0;
	for (PStackPointer i=0; i<PStackGetSP(subterms);i++)
	{
		Term_p subterm = PStackElementP(subterms,i);
		//printf("fcode: %ld minimal: %ld\n",subterm->f_code,minimal);
		if (subterm->f_code < minimal)
		{
			minimal = subterm->f_code;
		}
	}
	FunCode minimal1 = minimal - 2;
	FunCode minimal2 = minimal - 4;
	
	PStackEmpty(subterms);
	PStackFree(subterms);
	PStackFree(function_symbols);
	// minimal1 is now the FunCode of a variable that does not occur in the function, same for minimal2
	
	TFormula_p a,b;
	a = VarBankFCodeFind(state->terms->vars,minimal1);
	if (!a)
	{
		//printf("allocing a\n");
		a = VarBankVarAlloc(state->terms->vars,minimal1,freevariable->sort);
	}
	b = VarBankFCodeFind(state->terms->vars,minimal2);
   if (!b)
	{
		//printf("allocing b\n");
		b = VarBankVarAlloc(state->terms->vars,minimal2,freevariable->sort);
	}
	assert(a);
	assert(b);
	//printf("\nnew variables\n");
	//TermPrint(GlobalOut,a,state->signature,DEREF_NEVER);
	//printf("\n");
	//TermPrint(GlobalOut,b,state->signature,DEREF_NEVER);
	//exit(0);
	//TFormula_p a = VarBankGetFreshVar(state->freshvars,freevariable->sort);
	//TFormula_p b = VarBankGetFreshVar(state->freshvars,freevariable->sort);
	
	TFormula_p xina = TFormulaFCodeAlloc(bank,member,freevariable,a);
	TFormula_p xinb = TFormulaFCodeAlloc(bank,member,freevariable,b);
	
	Eqn_p xina_eq = EqnAlloc(xina,bank->true_term,bank,true);
	Eqn_p xinb_eq = EqnAlloc(xinb,bank->true_term,bank,true);
	
	TFormula_p xina_f = TFormulaLitAlloc(xina_eq);
	TFormula_p xinb_f = TFormulaLitAlloc(xinb_eq);
	
	input = TFormulaFCodeAlloc(bank,bank->sig->and_code,xina_f,input);
	input = TFormulaFCodeAlloc(bank,bank->sig->equiv_code,xinb_f,input);
	input = TFormulaAddQuantor(bank,input,true,freevariable);
	input = TFormulaAddQuantor(bank,input,false,b);
	input = TFormulaAddQuantor(bank,input,true,a);
	
	for (PStackPointer i=0; i<PStackGetSP(freevars); i++)  // Universally quantify over the parameters of the formula
	{
		if (i == position) continue;
		Term_p v_i = (Term_p) PStackElementP(freevars,i);
		input = TFormulaAddQuantor(bank,input,true,v_i);
	}
	
	EqnFree(xina_eq);
	EqnFree(xinb_eq);
	
	return input;
}

ClauseSet_p tformula_replacement(TB_p bank, ProofState_p state, PTree_p* freevars, TFormula_p input, Clause_p clause)  //bugged
{
	void* pointer0 = PTreeExtractRootKey(freevars);
	void* pointer1 = PTreeExtractRootKey(freevars);
	FunCode member = SigFindFCode(state->signature, "member");  //TPTP only
	ClauseSet_p final = ClauseSetAlloc();
	//Subst_p binder = SubstAlloc();
	
	if (pointer0 == NULL || pointer1 == NULL)
	{
		printf("\nNULL pointer\n");
	}
	
	TFormula_p temp1 = TFormulaCopy(bank,input);
	TFormula_p temp2 = TFormulaCopy(bank,input);
	
	
	TFormula_p x = (TFormula_p) pointer0;
	TFormula_p y = (TFormula_p) pointer1;
	
	TFormula_p a = VarBankGetFreshVar(state->freshvars,x->sort);
	TFormula_p b = VarBankGetFreshVar(state->freshvars,x->sort);
	
	TFormula_p c = VarBankGetFreshVar(state->freshvars,x->sort); //
	//TFormula_p phi2 = tformula_substitute_variable(temp1,y,c);
	
	
	Clause_p substitutedclause = ClauseMergeVars(clause, bank, y, c);
	
	TFormula_p phi2 = TFormulaClauseEncode(bank, substitutedclause);
	
	TFormula_p xina = TFormulaFCodeAlloc(bank,member,x,a);
	Eqn_p xina_eq = EqnAlloc(xina,bank->true_term,bank,true);
	TFormula_p xina_f = TFormulaLitAlloc(xina_eq);
	
	temp2 = TFormulaFCodeAlloc(bank,bank->sig->and_code,xina_f,temp2);
	temp2 = TFormulaAddQuantor(bank,temp2,false,a);
	
	TFormula_p yinb = TFormulaFCodeAlloc(bank,member,y,b);
	Eqn_p yinb_eq = EqnAlloc(yinb,bank->true_term,bank,true);
	TFormula_p yinb_f = TFormulaLitAlloc(yinb_eq);
	
	temp2 = TFormulaFCodeAlloc(bank,bank->sig->equiv_code,yinb_f,temp2);
	temp2 = TFormulaAddQuantor(bank,temp2,true,y);
	temp2 = TFormulaAddQuantor(bank,temp2,false,b);
	temp2 = TFormulaAddQuantor(bank,temp2,true,a);
	
	TFormula_p yeqc = TFormulaFCodeAlloc(bank,bank->sig->eqn_code,y,c);
	
	phi2 = TFormulaFCodeAlloc(bank,bank->sig->equiv_code,phi2,yeqc);
	phi2 = TFormulaAddQuantor(bank,phi2,true,c);
	phi2 = TFormulaAddQuantor(bank,phi2,false,y);
	phi2 = TFormulaAddQuantor(bank,phi2,true,x);
	
	// join
	
	temp2 = TFormulaFCodeAlloc(bank,bank->sig->impl_code,phi2,temp2);
	
	WFormula_p schemaaswformula = WTFormulaAlloc(bank,temp2);
      
   //yan
   if (OutputLevel >= 1)
   {
      fprintf(GlobalOut,   "REPLACEMENT: term: ");
      TermPrint(GlobalOut, temp2, bank->sig, DEREF_ALWAYS);
      fprintf(GlobalOut, "\n          formula: ");
      WFormulaPrint(GlobalOut, schemaaswformula, true);
      fprintf(GlobalOut, "\n");
   }
   //

	long res = WFormulaCNF(schemaaswformula,final,state->terms,state->freshvars);
	//printf("\nR clauses: %ld\n",res);
	return final;
}
/*-----------------------------------------------------------------------
//
// Function: ClauseMergeVars()
//
//   Create a copy of clause in which the two variables x and y are
//   merged, or, more exactly, every occurrence of x is replaced by
//   one in y.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/


Clause_p ClauseMergeVars(Clause_p clause,  TB_p bank, Term_p x, Term_p y)
{
   Subst_p  subst = SubstAlloc();
   Clause_p new_clause;
   
   SubstAddBinding(subst, x,y);
   new_clause = ClauseCopy(clause, bank);
   SubstDelete(subst);

   return new_clause;
}


/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
//
// Function: document_processing()
//
//   Document processing of the new given clause (depending on the
//   output level).
//
// Global Variables: OutputLevel, GlobalOut (read only)
//
// Side Effects    : Output
//
/----------------------------------------------------------------------*/

void document_processing(Clause_p clause)
{
   if(OutputLevel)
   {
      if(OutputLevel == 1)
      {
         putc('\n', GlobalOut);
         putc('#', GlobalOut);
         ClausePrint(GlobalOut, clause, true);
         putc('\n', GlobalOut);
      }
      DocClauseQuoteDefault(6, clause, "new_given");
   }
}

/*-----------------------------------------------------------------------
//
// Function: check_ac_status()
//
//   Check if the AC theory has been extended by the currently
//   processed clause, and act accordingly.
//
// Global Variables: -
//
// Side Effects    : Changes AC status in signature
//
/----------------------------------------------------------------------*/

static void check_ac_status(ProofState_p state, ProofControl_p
                            control, Clause_p clause)
{
   if(control->heuristic_parms.ac_handling!=NoACHandling)
   {
      bool res;
      res = ClauseScanAC(state->signature, clause);
      if(res && !control->ac_handling_active)
      {
         control->ac_handling_active = true;
         if(OutputLevel)
         {
            SigPrintACStatus(GlobalOut, state->signature);
            fprintf(GlobalOut, "# AC handling enabled dynamically\n");
         }
      }
   }
}



/*-----------------------------------------------------------------------
//
// Function: eliminate_backward_rewritten_clauses()
//
//   Remove all processed clauses rewritable with clause and put
//   them into state->tmp_store.
//
// Global Variables: -
//
// Side Effects    : Changes clause sets
//
/----------------------------------------------------------------------*/

static bool
eliminate_backward_rewritten_clauses(ProofState_p
                                     state, ProofControl_p control,
                                     Clause_p clause, SysDate *date)
{
   long old_lit_count = state->tmp_store->literals,
      old_clause_count= state->tmp_store->members;
   bool min_rw = false;

   PERF_CTR_ENTRY(BWRWTimer);
   if(ClauseIsDemodulator(clause))
   {
      SysDateInc(date);
      if(state->gindices.bw_rw_index)
      {
         min_rw = RemoveRewritableClausesIndexed(control->ocb,
                                                 state->tmp_store,
                                                 state->archive,
                                                 clause, *date, &(state->gindices));

      }
      else
      {
         min_rw = RemoveRewritableClauses(control->ocb,
                                          state->processed_pos_rules,
                                          state->tmp_store,
                                          state->archive,
                                          clause, *date, &(state->gindices))
            ||min_rw;
         min_rw = RemoveRewritableClauses(control->ocb,
                                          state->processed_pos_eqns,
                                          state->tmp_store,
                                          state->archive,
                                          clause, *date, &(state->gindices))
            ||min_rw;
         min_rw = RemoveRewritableClauses(control->ocb,
                                          state->processed_neg_units,
                                          state->tmp_store,
                                          state->archive,
                                          clause, *date, &(state->gindices))
            ||min_rw;
         min_rw = RemoveRewritableClauses(control->ocb,
                                          state->processed_non_units,
                                          state->tmp_store,
                                          state->archive,
                                          clause, *date, &(state->gindices))
            ||min_rw;
      }
      state->backward_rewritten_lit_count+=
         (state->tmp_store->literals-old_lit_count);
      state->backward_rewritten_count+=
         (state->tmp_store->members-old_clause_count);

      if(control->heuristic_parms.detsort_bw_rw)
      {
         ClauseSetSort(state->tmp_store, ClauseCmpByStructWeight);
      }
   }
   PERF_CTR_EXIT(BWRWTimer);
   /*printf("# Removed %ld clauses\n",
     (state->tmp_store->members-old_clause_count)); */
   return min_rw;
}


/*-----------------------------------------------------------------------
//
// Function: eliminate_backward_subsumed_clauses()
//
//   Eliminate subsumed processed clauses, return number of clauses
//   deleted.
//
// Global Variables: -
//
// Side Effects    : Changes clause sets.
//
/----------------------------------------------------------------------*/

static long eliminate_backward_subsumed_clauses(ProofState_p state,
                                                FVPackedClause_p pclause)
{
   long res = 0;

   if(ClauseLiteralNumber(pclause->clause) == 1)
   {
      if(pclause->clause->pos_lit_no)
      {
         /* A unit rewrite rule that is a variant of an old rule is
            already subsumed by the older one.
            A unit rewrite rule can never subsume an unorientable
            equation (else it would be unorientable itself). */
         if(!ClauseIsRWRule(pclause->clause))
         {
            res += RemoveSubsumed(&(state->gindices), pclause,
                                   state->processed_pos_rules,
                                   state->archive, NULL);
            res += RemoveSubsumed(&(state->gindices), pclause,
                                   state->processed_pos_eqns,
                                   state->archive, NULL);
         }
         res += RemoveSubsumed(&(state->gindices), pclause,
                                state->processed_non_units,
                                state->archive, NULL);
      }
      else
      {
         res += RemoveSubsumed(&(state->gindices), pclause,
                                state->processed_neg_units,
                                state->archive, NULL);
         res += RemoveSubsumed(&(state->gindices), pclause,
                                state->processed_non_units,
                                state->archive, NULL);
      }
   }
   else
   {
      res += RemoveSubsumed(&(state->gindices), pclause,
                             state->processed_non_units,
                             state->archive, NULL);
   }
   state->backward_subsumed_count+=res;
   return res;
}



/*-----------------------------------------------------------------------
//
// Function: eliminate_unit_simplified_clauses()
//
//   Perform unit-back-simplification on the proof state.
//
// Global Variables: -
//
// Side Effects    : Potentially changes and moves clauses.
//
/----------------------------------------------------------------------*/

static void eliminate_unit_simplified_clauses(ProofState_p state,
                                              Clause_p clause)
{
   if(ClauseIsRWRule(clause)||!ClauseIsUnit(clause))
   {
      return;
   }
   ClauseSetUnitSimplify(state->processed_non_units, clause,
                         state->tmp_store,
                         state->archive,
                         &(state->gindices));
   if(ClauseIsPositive(clause))
   {
      ClauseSetUnitSimplify(state->processed_neg_units, clause,
                            state->tmp_store,
                            state->archive,
                            &(state->gindices));
   }
   else
   {
      ClauseSetUnitSimplify(state->processed_pos_rules, clause,
                            state->tmp_store,
                            state->archive,
                            &(state->gindices));
      ClauseSetUnitSimplify(state->processed_pos_eqns, clause,
                            state->tmp_store,
                            state->archive,
                            &(state->gindices));
   }
}

/*-----------------------------------------------------------------------
//
// Function: eliminate_context_sr_clauses()
//
//   If required by control, remove all
//   backward-contextual-simplify-reflectable clauses.
//
// Global Variables: -
//
// Side Effects    : Moves clauses from state->processed_non_units
//                   to state->tmp_store
//
/----------------------------------------------------------------------*/

static long eliminate_context_sr_clauses(ProofState_p state,
                                         ProofControl_p control,
                                         Clause_p clause)
{
   if(!control->heuristic_parms.backward_context_sr)
   {
      return 0;
   }
   return RemoveContextualSRClauses(state->processed_non_units,
                                    state->tmp_store,
                                    state->archive,
                                    clause,
                                    &(state->gindices));
}

/*-----------------------------------------------------------------------
//
// Function: simplify_watchlist()
//
//   Simplify all clauses in state->watchlist with processed positive
//   units from state. Assumes that all those clauses are in normal
//   form with respect to all clauses but clause!
//
// Global Variables: -
//
// Side Effects    : Changes watchlist, introduces new rewrite links
//                   into the term bank!
//
/----------------------------------------------------------------------*/

void simplify_watchlist(ProofState_p state, ProofControl_p control,
                        Clause_p clause)
{
   if(!ClauseIsDemodulator(clause))
   {
      return;
   }
   // printf("# simplify_watchlist()...\n");
   WatchlistSimplify(state->wlcontrol, clause, control, state->terms, state->archive, state->demods);
   // printf("# ...simplify_watchlist()\n");
}


/*-----------------------------------------------------------------------
//
// Function: generate_new_clauses()
//
//   Apply the generating inferences to the proof state, putting new
//   clauses into state->tmp_store.
//
// Global Variables: -
//
// Side Effects    : Changes proof state as described.
//
/----------------------------------------------------------------------*/

static void generate_new_clauses(ProofState_p state, ProofControl_p
                                 control, Clause_p clause, Clause_p tmp_copy)
{
	//generate new schema instances and add to tmp_store
   //printf("\nSchema mode!!!\n");
   /*
   state->paramod_count += compute_schemas_tform(control,
										state->terms,
										control->ocb,
										clause,
										state->tmp_store, state->freshvars,
										state);
   */
   if(control->heuristic_parms.enable_eq_factoring)
   {
      state->factor_count+=
         ComputeAllEqualityFactors(state->terms, control->ocb, clause,
                                   state->tmp_store, state->freshvars);
   }
   state->resolv_count+=
      ComputeAllEqnResolvents(state->terms, clause, state->tmp_store,
                              state->freshvars);

   if(control->heuristic_parms.enable_neg_unit_paramod
      ||!ClauseIsUnit(clause)
      ||!ClauseIsNegative(clause))
   { /* Sometime we want to disable paramodulation for negative units */
      PERF_CTR_ENTRY(ParamodTimer);
      if(state->gindices.pm_into_index)
      {
         state->paramod_count+=
            ComputeAllParamodulantsIndexed(state->terms,
                                           control->ocb,
                                           state->freshvars,
                                           tmp_copy,
                                           clause,
                                           state->gindices.pm_into_index,
                                           state->gindices.pm_negp_index,
                                           state->gindices.pm_from_index,
                                           state->tmp_store,
                                           control->heuristic_parms.pm_type);
      }
      else
      {
         state->paramod_count+=
            ComputeAllParamodulants(state->terms, control->ocb,
                                    tmp_copy, clause,
                                    state->processed_pos_rules,
                                    state->tmp_store, state->freshvars,
                                    control->heuristic_parms.pm_type);
         state->paramod_count+=
            ComputeAllParamodulants(state->terms, control->ocb,
                                    tmp_copy, clause,
                                    state->processed_pos_eqns,
                                    state->tmp_store, state->freshvars,
                                    control->heuristic_parms.pm_type);

         if(control->heuristic_parms.enable_neg_unit_paramod && !ClauseIsNegative(clause))
         { /* We never need to try to overlap purely negative clauses! */
            state->paramod_count+=
               ComputeAllParamodulants(state->terms, control->ocb,
                                       tmp_copy, clause,
                                       state->processed_neg_units,
                                       state->tmp_store, state->freshvars,
                                       control->heuristic_parms.pm_type);
         }
         state->paramod_count+=
            ComputeAllParamodulants(state->terms, control->ocb,
                                    tmp_copy, clause,
                                    state->processed_non_units,
                                    state->tmp_store, state->freshvars,
                                    control->heuristic_parms.pm_type);
      }
      PERF_CTR_EXIT(ParamodTimer);
   }
}


/*-----------------------------------------------------------------------
//
// Function: eval_clause_set()
//
//   Add evaluations to all clauses in state->eval_set. Factored out
//   so that batch-processing with e.g. neural networks can be easily
//   integrated.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void eval_clause_set(ProofState_p state, ProofControl_p control)
{
   Clause_p handle;
   assert(state);
   assert(control);

   for(handle = state->eval_store->anchor->succ;
       handle != state->eval_store->anchor;
       handle = handle->succ)
   {
      HCBClauseEvaluate(control->hcb, handle);
   }
}


/*-----------------------------------------------------------------------
//
// Function: insert_new_clauses()
//
//   Rewrite clauses in state->tmp_store, remove superfluous literals,
//   insert them into state->unprocessed. If an empty clause is
//   detected, return it, otherwise return NULL.
//
// Global Variables: -
//
// Side Effects    : As described.
//
/----------------------------------------------------------------------*/

static Clause_p insert_new_clauses(ProofState_p state, ProofControl_p control)
{
   Clause_p handle;
   long     clause_count;

   state->generated_count+=state->tmp_store->members;
   state->generated_lit_count+=state->tmp_store->literals;
   while((handle = ClauseSetExtractFirst(state->tmp_store)))
   {
      /* printf("Inserting: ");
         ClausePrint(stdout, handle, true);
         printf("\n"); */
      if(ClauseQueryProp(handle,CPIsIRVictim))
      {
         assert(ClauseQueryProp(handle, CPLimitedRW));
         ForwardModifyClause(state, control, handle,
                             control->heuristic_parms.forward_context_sr_aggressive||
                             (control->heuristic_parms.backward_context_sr&&
                              ClauseQueryProp(handle,CPIsProcessed)),
                             control->heuristic_parms.condensing_aggressive,
                             FullRewrite);
         ClauseDelProp(handle,CPIsIRVictim);
      }
      ForwardModifyClause(state, control, handle,
                          control->heuristic_parms.forward_context_sr_aggressive||
                          (control->heuristic_parms.backward_context_sr&&
                           ClauseQueryProp(handle,CPIsProcessed)),
                          control->heuristic_parms.condensing_aggressive,
                          control->heuristic_parms.forward_demod);


      if(ClauseIsTrivial(handle))
      {
         assert(!handle->children);
         ClauseDetachParents(handle);
         ClauseFree(handle);
         continue;
      }
      if(state->wlcontrol)
      {
         /*check_watchlist(&(state->wlindices), state->watchlist,
                         handle, state->archive,
                         control->heuristic_parms.watchlist_is_static,
                         &(state->watch_progress), state->signature);
         */
         WatchlistCheck(state->wlcontrol, handle, state->archive, 
            control->heuristic_parms.watchlist_is_static, state->signature);
      }
      if(ClauseIsEmpty(handle))
      {
         return handle;
      }
      if(control->heuristic_parms.er_aggressive &&
         control->heuristic_parms.er_varlit_destructive &&
         (clause_count =
          ClauseERNormalizeVar(state->terms,
                               handle,
                               state->tmp_store,
                               state->freshvars,
                               control->heuristic_parms.er_strong_destructive)))
      {
         state->other_redundant_count += clause_count;
         state->resolv_count += clause_count;
         state->generated_count += clause_count;
         continue;
      }
      if(control->heuristic_parms.split_aggressive &&
         (clause_count = ControlledClauseSplit(state->definition_store,
                                               handle,
                                               state->tmp_store,
                                               control->heuristic_parms.split_clauses,
                                               control->heuristic_parms.split_method,
                                               control->heuristic_parms.split_fresh_defs)))
      {
         state->generated_count += clause_count;
         continue;
      }
      state->non_trivial_generated_count++;
      ClauseDelProp(handle, CPIsOriented);
      if(!control->heuristic_parms.select_on_proc_only)
      {
         DoLiteralSelection(control, handle);
      }
      else
      {
         EqnListDelProp(handle->literals, EPIsSelected);
      }
      handle->create_date = state->proc_non_trivial_count;
      if(ProofObjectRecordsGCSelection)
      {
         ClausePushDerivation(handle, DCCnfEvalGC, NULL, NULL);
      }
//      HCBClauseEvaluate(control->hcb, handle);

      ClauseSetInsert(state->eval_store, handle);
   }
   eval_clause_set(state, control);

   while((handle = ClauseSetExtractFirst(state->eval_store)))
   {
      ClauseDelProp(handle, CPIsOriented);
      DocClauseQuoteDefault(6, handle, "eval");

      ClauseSetInsert(state->unprocessed, handle);
   }
   return NULL;
}


/*-----------------------------------------------------------------------
//
// Function: replacing_inferences()
//
//   Perform the inferences that replace a clause by another:
//   Destructive equality-resolution and/or splitting.
//
//   Returns NULL if clause was replaced, the empty clause if this
//   produced an empty clause, and the original clause otherwise
//
// Global Variables: -
//
// Side Effects    : May insert new clauses into state. May destroy
//                   pclause (in which case it gets rid of the container)
//
/----------------------------------------------------------------------*/

Clause_p replacing_inferences(ProofState_p state, ProofControl_p
                              control, FVPackedClause_p pclause)
{
   long     clause_count;
   Clause_p res = pclause->clause;

   if(control->heuristic_parms.er_varlit_destructive &&
      (clause_count =
       ClauseERNormalizeVar(state->terms,
                            pclause->clause,
                            state->tmp_store,
                            state->freshvars,
                            control->heuristic_parms.er_strong_destructive)))
   {
      state->other_redundant_count += clause_count;
      state->resolv_count += clause_count;
      pclause->clause = NULL;
   }
   else if(ControlledClauseSplit(state->definition_store,
                                 pclause->clause, state->tmp_store,
                                 control->heuristic_parms.split_clauses,
                                 control->heuristic_parms.split_method,
                                 control->heuristic_parms.split_fresh_defs))
   {
      pclause->clause = NULL;
   }

   if(!pclause->clause)
   {  /* ...then it has been destroyed by one of the above methods,
       * which may have put some clauses into tmp_store. */
      FVUnpackClause(pclause);

      res = insert_new_clauses(state, control);
   }
   return res;
}


/*-----------------------------------------------------------------------
//
// Function: cleanup_unprocessed_clauses()
//
//   Perform maintenenance operations on state->unprocessed, depending
//   on paramters in control:
//   - Remove copies
//   - Simplify all unprocessed clauses
//   - Reweigh all unprocessed clauses
//   - Delete "bad" clauses to avoid running out of memories.
//   Simplification can find the empty clause, which is then
//   returned.
//
// Global Variables: -
//
// Side Effects    : As described above.
//
/----------------------------------------------------------------------*/

static Clause_p cleanup_unprocessed_clauses(ProofState_p state,
                                            ProofControl_p control)
{
   long long current_storage    = ProofStateStorage(state);
   long long filter_base        = current_storage;
   long long filter_copies_base = current_storage;
   long long reweight_base      = state->unprocessed->members;
   long tmp;
   Clause_p unsatisfiable = NULL;

   filter_copies_base = MIN(filter_copies_base,current_storage);
   if((current_storage - filter_copies_base) >
      control->heuristic_parms.filter_copies_limit)
   {
      tmp = ClauseSetDeleteCopies(state->unprocessed);
      if(OutputLevel)
      {
         fprintf(GlobalOut,
                 "# Deleted %ld clause copies (remaining: %ld)\n",
                 tmp, state->unprocessed->members);
      }
      state->other_redundant_count += tmp;
      current_storage  = ProofStateStorage(state);
      filter_copies_base = current_storage;
   }
   filter_base = MIN(filter_base,current_storage);
   if((current_storage - filter_base) > control->heuristic_parms.filter_limit)
   {
      tmp = state->unprocessed->members;
      unsatisfiable =
         ForwardContractSet(state, control,
                            state->unprocessed, false, FullRewrite,
                            &(state->other_redundant_count), true);
      if(unsatisfiable)
      {
         PStackPushP(state->extract_roots, unsatisfiable);
      }
      if(OutputLevel)
      {
         fprintf(GlobalOut,
                 "# Special forward-contraction deletes %ld clauses"
                 "(remaining: %ld) \n",
                 tmp - state->unprocessed->members,
                 state->unprocessed->members);
      }
      current_storage  = ProofStateStorage(state);
      filter_base = current_storage;
      if(unsatisfiable)
      {
         return unsatisfiable;
      }
   }
   reweight_base = MIN(state->unprocessed->members, reweight_base);
   if((state->unprocessed->members - reweight_base)
      > control->heuristic_parms.reweight_limit)
   {
      OUTPRINT(1, "# Reweighting unprocessed clauses...\n");
      ClauseSetReweight(control->hcb,  state->unprocessed);
      reweight_base = state->unprocessed->members;
   }
   tmp = LONG_MAX;

   if(current_storage > control->heuristic_parms.delete_bad_limit)
   {
      tmp = HCBClauseSetDeleteBadClauses(control->hcb,
                                         state->unprocessed,
                                         state->unprocessed->members/2);
      state->non_redundant_deleted += tmp;
      if(OutputLevel)
      {
         fprintf(GlobalOut,
                 "# Deleted %ld bad clauses (prover may be"
                 " incomplete now)\n", tmp);
      }
      state->state_is_complete = false;
//       ProofStateGCMarkTerms(state);
//       ProofStateGCSweepTerms(state);
      GCCollect(state->terms->gc);
      current_storage = ProofStateStorage(state);
      filter_base = MIN(filter_base, current_storage);
      filter_copies_base = MIN(filter_copies_base, current_storage);
   }
   return unsatisfiable;
}

/*-----------------------------------------------------------------------
//
// Function: SATCheck()
//
//   Create ground (or pseudo-ground) instances of the clause set,
//   hand them to a SAT solver, and check then for unsatisfiability.
//
// Global Variables:
//
// Side Effects    :
//
/----------------------------------------------------------------------*/

Clause_p SATCheck(ProofState_p state, ProofControl_p control)
{
   Clause_p res = NULL;

   if(control->heuristic_parms.sat_check_normalize)
   {
      //printf("# Cardinality of unprocessed: %ld\n",
      //        ClauseSetCardinality(state->unprocessed));
      res = ForwardContractSetReweight(state, control, state->unprocessed,
                                       false, 2,
                                       &(state->proc_trivial_count));
      // printf("# ForwardContraction done\n");

   }
   if(!res)
   {
      SatClauseSet_p set = SatClauseSetAlloc();

      //printf("# SatCheck() %ld, %ld..\n",
      //       state->proc_non_trivial_count,
      //       ProofStateCardinality(state));

      SatClauseSetImportProofState(set, state,
                                   control->heuristic_parms.sat_check_grounding,
                                   control->heuristic_parms.sat_check_normconst);

      // printf("# SatCheck()..imported\n");

      res = SatClauseSetCheckUnsat(set);
      state->satcheck_count++;
      if(res)
      {
         state->satcheck_success++;
      }
      SatClauseSetFree(set);
   }
   return res;
}

#ifdef PRINT_SHARING

/*-----------------------------------------------------------------------
//
// Function: print_sharing_factor()
//
//   Determine the sharing factor and print it. Potentially expensive,
//   only useful for manual analysis.
//
// Global Variables:
//
// Side Effects    :
//
/----------------------------------------------------------------------*/

static void print_sharing_factor(ProofState_p state)
{
   long shared, unshared;
   shared = TBTermNodes(state->terms);
   unshared = ClauseSetGetTermNodes(state->tmp_store)+
      ClauseSetGetTermNodes(state->processed_pos_rules)+
      ClauseSetGetTermNodes(state->processed_pos_eqns)+
      ClauseSetGetTermNodes(state->processed_neg_units)+
      ClauseSetGetTermNodes(state->processed_non_units)+
      ClauseSetGetTermNodes(state->unprocessed);

   fprintf(GlobalOut, "\n#        GClauses   NClauses    NShared  "
           "NUnshared    TShared  TUnshared TSharinF   \n");
   fprintf(GlobalOut, "# grep %10ld %10ld %10ld %10ld %10ld %10ld %10.3f\n",
           state->generated_count - state->backward_rewritten_count,
           state->tmp_store->members,
           ClauseSetGetSharedTermNodes(state->tmp_store),
           ClauseSetGetTermNodes(state->tmp_store),
           shared,
           unshared,
           (float)unshared/shared);
}
#endif


#ifdef PRINT_RW_STATE

/*-----------------------------------------------------------------------
//
// Function: print_rw_state()
//
//   Print the system (R,E,NEW), e.g. the two types of demodulators
//   and the newly generated clauses.
//
// Global Variables: -
//
// Side Effects    : Output
//
/----------------------------------------------------------------------*/

void print_rw_state(ProofState_p state)
{
   char prefix[20];

   sprintf(prefix, "RWD%09ld_R: ",state->proc_non_trivial_count);
   ClauseSetPrintPrefix(GlobalOut,prefix,state->processed_pos_rules);
   sprintf(prefix, "RWD%09ld_E: ",state->proc_non_trivial_count);
   ClauseSetPrintPrefix(GlobalOut,prefix,state->processed_pos_eqns);
   sprintf(prefix, "RWD%09ld_N: ",state->proc_non_trivial_count);
   ClauseSetPrintPrefix(GlobalOut,prefix,state->tmp_store);
}

#endif





/*---------------------------------------------------------------------*/
/*                         Exported Functions                          */
/*---------------------------------------------------------------------*/



/*-----------------------------------------------------------------------
//
// Function: ProofControlInit()
//
//   Initialize a proof control cell for a given proof state (with at
//   least axioms and signature) and a set of parameters
//   describing the ordering and heuristics.
//
// Global Variables: -
//
// Side Effects    : Sets specs.
//
/----------------------------------------------------------------------*/

void ProofControlInit(ProofState_p state,ProofControl_p control,
                      HeuristicParms_p params, FVIndexParms_p fvi_params,
                      PStack_p wfcb_defs, PStack_p hcb_defs)
{
   PStackPointer sp;
   Scanner_p in;

   assert(control && control->wfcbs);
   assert(state && state->axioms && state->signature);
   assert(params);
   assert(!control->ocb);
   assert(!control->hcb);

   SpecFeaturesCompute(&(control->problem_specs),
                       state->axioms,state->signature);

   control->ocb = TOSelectOrdering(state, params,
                                   &(control->problem_specs));

   in = CreateScanner(StreamTypeInternalString,
                      DefaultWeightFunctions,
                      true, NULL);
   WeightFunDefListParse(control->wfcbs, in, control->ocb, state);
   DestroyScanner(in);

   for(sp = 0; sp < PStackGetSP(wfcb_defs); sp++)
   {
      in = CreateScanner(StreamTypeOptionString,
                         PStackElementP(wfcb_defs, sp) ,
                         true, NULL);
      WeightFunDefListParse(control->wfcbs, in, control->ocb, state);
      DestroyScanner(in);
   }
   in = CreateScanner(StreamTypeInternalString,
                      DefaultHeuristics,
                      true, NULL);
   HeuristicDefListParse(control->hcbs, in, control->wfcbs,
                         control->ocb, state);
   DestroyScanner(in);
   for(sp = 0; sp < PStackGetSP(hcb_defs); sp++)
   {
      in = CreateScanner(StreamTypeOptionString,
                         PStackElementP(hcb_defs, sp) ,
                         true, NULL);
      HeuristicDefListParse(control->hcbs, in, control->wfcbs,
                            control->ocb, state);
      DestroyScanner(in);
   }
   control->heuristic_parms     = *params;

   control->hcb = GetHeuristic(params->heuristic_name,
                               state,
                               control,
                               params);
   control->fvi_parms           = *fvi_params;
   if(!control->heuristic_parms.split_clauses)
   {
      control->fvi_parms.symbol_slack = 0;
   }
}


/*-----------------------------------------------------------------------
//
// Function: ProofStateResetProcessedSet()
//
//   Move all clauses from set into state->unprocessed.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void ProofStateResetProcessedSet(ProofState_p state,
                                 ProofControl_p control,
                                 ClauseSet_p set)
{
   Clause_p handle;

   while((handle = ClauseSetExtractFirst(set)))
   {
      if(ClauseQueryProp(handle, CPIsGlobalIndexed))
      {
         GlobalIndicesDeleteClause(&(state->gindices), handle);
      }

      ClauseKillChildren(handle); /* Should be none, but better be safe */

      if(ProofObjectRecordsGCSelection)
      {
         ClausePushDerivation(handle, DCCnfEvalGC, NULL, NULL);
      }
      if(BuildProofObject)
      {
         Clause_p tmpclause = ClauseFlatCopy(handle);
         ClausePushDerivation(tmpclause, DCCnfQuote, handle, NULL);
         ClauseSetInsert(state->archive, handle);
         handle = tmpclause;
      }
      HCBClauseEvaluate(control->hcb, handle);
      ClauseDelProp(handle, CPIsOriented);
      DocClauseQuoteDefault(6, handle, "move_eval");

      if(control->heuristic_parms.prefer_initial_clauses)
      {
         EvalListChangePriority(handle->evaluations, -PrioLargestReasonable);
      }
      ClauseSetInsert(state->unprocessed, handle);
   }
}


/*-----------------------------------------------------------------------
//
// Function: ProofStateResetProcessed()
//
//   Move all clauses from the processed clause sets to unprocessed.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void ProofStateResetProcessed(ProofState_p state, ProofControl_p control)
{
   ProofStateResetProcessedSet(state, control, state->processed_pos_rules);
   ProofStateResetProcessedSet(state, control, state->processed_pos_eqns);
   ProofStateResetProcessedSet(state, control, state->processed_neg_units);
   ProofStateResetProcessedSet(state, control, state->processed_non_units);
}


/*-----------------------------------------------------------------------
//
// Function: fvi_param_init()
//
//   Initialize the parameters for all feature vector indices in
//   state.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void fvi_param_init(ProofState_p state, ProofControl_p control)
{
   long symbols;
   PermVector_p perm;
   FVCollect_p  cspec;

   state->fvi_initialized = true;
   state->original_symbols = state->signature->f_count;

   symbols = MIN(state->original_symbols+control->fvi_parms.symbol_slack,
                 control->fvi_parms.max_symbols);

   // printf("### Symbols: %ld\n", symbols);
   switch(control->fvi_parms.cspec.features)
   {
   case FVIBillFeatures:
         cspec = BillFeaturesCollectAlloc(state->signature, symbols*2+2);
         break;
   case FVIBillPlusFeatures:
         cspec = BillPlusFeaturesCollectAlloc(state->signature, symbols*2+4);
         break;
   case FVIACFold:
         // printf("# FVIACFold\n");
         cspec = FVCollectAlloc(FVICollectFeatures,
                                true,
                                0,
                                symbols*2+2,
                                2,
                                0,
                                symbols,
                                symbols+2,
                                0,
                                symbols,
                                0,0,0,
                                0,0,0);
         break;
   case FVIACStagger:
         cspec = FVCollectAlloc(FVICollectFeatures,
                                true,
                                0,
                                symbols*2+2,
                                2,
                                0,
                                2*symbols,
                                2,
                                2+symbols,
                                2*symbols,
                                0,0,0,
                                0,0,0);
         break;
   case FVICollectFeatures:
         cspec = FVCollectAlloc(control->fvi_parms.cspec.features,
                                control->fvi_parms.cspec.use_litcount,
                                control->fvi_parms.cspec.ass_vec_len,
                                symbols,
                                control->fvi_parms.cspec.pos_count_base,
                                control->fvi_parms.cspec.pos_count_offset,
                                control->fvi_parms.cspec.pos_count_mod,
                                control->fvi_parms.cspec.neg_count_base,
                                control->fvi_parms.cspec.neg_count_offset,
                                control->fvi_parms.cspec.neg_count_mod,
                                control->fvi_parms.cspec.pos_depth_base,
                                control->fvi_parms.cspec.pos_depth_offset,
                                control->fvi_parms.cspec.pos_depth_mod,
                                control->fvi_parms.cspec.neg_depth_base,
                                control->fvi_parms.cspec.neg_depth_offset,
                                control->fvi_parms.cspec.neg_depth_mod);

         break;
   default:
         cspec = FVCollectAlloc(control->fvi_parms.cspec.features,
                                0,
                                0,
                                0,
                                0, 0, 0,
                                0, 0, 0,
                                0, 0, 0,
                                0, 0, 0);
         break;
   }
   cspec->max_symbols=symbols;
   state->fvi_cspec = cspec;

   perm = PermVectorCompute(state->axioms,
                            cspec,
                            control->fvi_parms.eliminate_uninformative);
   if(control->fvi_parms.cspec.features != FVINoFeatures)
   {
      state->processed_non_units->fvindex =
         FVIAnchorAlloc(cspec, PermVectorCopy(perm));
      state->processed_pos_rules->fvindex =
         FVIAnchorAlloc(cspec, PermVectorCopy(perm));
      state->processed_pos_eqns->fvindex =
         FVIAnchorAlloc(cspec, PermVectorCopy(perm));
      state->processed_neg_units->fvindex =
         FVIAnchorAlloc(cspec, PermVectorCopy(perm));
      if(state->wlcontrol)
      {
         WatchlistInitFVI(state->wlcontrol, cspec, PermVectorCopy(perm));
      }
   }
   state->def_store_cspec = FVCollectAlloc(FVICollectFeatures,
                                           true,
                                           0,
                                           symbols*2+2,
                                           2,
                                           0,
                                           symbols,
                                           symbols+2,
                                           0,
                                           symbols,
                                           0,0,0,
                                           0,0,0);
   state->definition_store->def_clauses->fvindex =
      FVIAnchorAlloc(state->def_store_cspec, perm);
}



/*-----------------------------------------------------------------------
//
// Function: ProofStateInit()
//
//   Given a proof state with axioms and a heuristic parameter
//   description, initialize the ProofStateCell, i.e. generate the
//   HCB, the ordering, and evaluate the axioms and put them in the
//   unprocessed list.
//
// Global Variables:
//
// Side Effects    :
//
/----------------------------------------------------------------------*/

void ProofStateInit(ProofState_p state, ProofControl_p control)
{
   Clause_p handle, new;
   HCB_p    tmphcb;
   PStack_p traverse;
   Eval_p   cell;

   OUTPRINT(1, "# Initializing proof state\n");

   assert(ClauseSetEmpty(state->processed_pos_rules));
   assert(ClauseSetEmpty(state->processed_pos_eqns));
   assert(ClauseSetEmpty(state->processed_neg_units));
   assert(ClauseSetEmpty(state->processed_non_units));

   if(!state->fvi_initialized)
   {
      fvi_param_init(state, control);
   }
   //ProofStateInitWatchlist(state, control->ocb);

   tmphcb = GetHeuristic("Uniq", state, control, &(control->heuristic_parms));
   assert(tmphcb);
   ClauseSetReweight(tmphcb, state->axioms);

   ProofStateInitWatchlist(state, control->ocb); // yan's wild guess

   traverse =
      EvalTreeTraverseInit(PDArrayElementP(state->axioms->eval_indices,0),0);

   while((cell = EvalTreeTraverseNext(traverse, 0)))
   {
      handle = cell->object;
      new = ClauseCopy(handle, state->terms);

      ClauseSetProp(new, CPInitial);
      if(state->wlcontrol)
      {
         WatchlistCheck(state->wlcontrol, new, state->archive,
                         control->heuristic_parms.watchlist_is_static,
                         state->signature);
      }
      HCBClauseEvaluate(control->hcb, new);
      DocClauseQuoteDefault(6, new, "eval");
      ClausePushDerivation(new, DCCnfQuote, handle, NULL);
      if(ProofObjectRecordsGCSelection)
      {
         ClausePushDerivation(new, DCCnfEvalGC, NULL, NULL);
      }
      if(control->heuristic_parms.prefer_initial_clauses)
      {
         EvalListChangePriority(new->evaluations, -PrioLargestReasonable);
      }
      ClauseSetInsert(state->unprocessed, new);
   }
   ClauseSetMarkSOS(state->unprocessed, control->heuristic_parms.use_tptp_sos);
   // printf("Before EvalTreeTraverseExit\n");
   EvalTreeTraverseExit(traverse);

   if(control->heuristic_parms.ac_handling!=NoACHandling)
   {
      if(OutputLevel)
      {
         fprintf(GlobalOut, "# Scanning for AC axioms\n");
      }
      control->ac_handling_active = ClauseSetScanAC(state->signature,
                                                    state->unprocessed);
      if(OutputLevel)
      {
         SigPrintACStatus(GlobalOut, state->signature);
         if(control->ac_handling_active)
         {
            fprintf(GlobalOut, "# AC handling enabled\n");
         }
      }
   }

   GlobalIndicesInit(&(state->gindices),
                     state->signature,
                     control->heuristic_parms.rw_bw_index_type,
                     control->heuristic_parms.pm_from_index_type,
                     control->heuristic_parms.pm_into_index_type);
   
   //OCBDebugPrint(GlobalOut, control->ocb);

}


/*-----------------------------------------------------------------------
//
// Function: ProcessClause()
//
//   Select an unprocessed clause, process it. Return pointer to empty
//   clause if it can be derived, NULL otherwise. This is the core of
//   the main proof procedure.
//
// Global Variables: -
//
// Side Effects    : Everything ;-)
//
/----------------------------------------------------------------------*/

Clause_p ProcessClause(ProofState_p state, ProofControl_p control,
                       long answer_limit)
{
   Clause_p         clause, resclause, tmp_copy, empty, arch_copy = NULL;
   FVPackedClause_p pclause;
   SysDate          clausedate;

   clause = control->hcb->hcb_select(control->hcb,
                                     state->unprocessed);                   
                                     
   //EvalListPrintComment(GlobalOut, clause->evaluations); printf("\n");
   if(OutputLevel==1)
   {
      putc('#', GlobalOut);
   }
   assert(clause);

   state->processed_count++;
   
   // Have to copy the state twice.
   //watch_progress_copy(&(clause->watch_proof_state), state->watch_progress);

   ClauseSetExtractEntry(clause);
   ClauseSetProp(clause, CPIsProcessed);
   ClauseDetachParents(clause);
   ClauseRemoveEvaluations(clause);

   assert(!ClauseQueryProp(clause, CPIsIRVictim));

   WatchlistClauseProcessed(state->wlcontrol, clause);
   if(ProofObjectRecordsGCSelection)
   {
	  arch_copy = ClauseArchive(state->archive, clause);
   }

   if(!(pclause = ForwardContractClause(state, control,
                                        clause, true,
                                        control->heuristic_parms.forward_context_sr,
                                        control->heuristic_parms.condensing,
                                        FullRewrite)))
   {
      if(arch_copy)
      {
         ClauseSetDeleteEntry(arch_copy);
      }
      return NULL;
   }

   
   
   if(ClauseIsSemFalse(pclause->clause))
   {
      state->answer_count ++;
      ClausePrintAnswer(GlobalOut, pclause->clause, state);
      PStackPushP(state->extract_roots, pclause->clause);
      if(ClauseIsEmpty(pclause->clause)||
         state->answer_count>=answer_limit)
      {
         clause = FVUnpackClause(pclause);
         ClauseEvaluateAnswerLits(clause);
         return clause;
      }
   }
   assert(ClauseIsSubsumeOrdered(pclause->clause));
   check_ac_status(state, control, pclause->clause);

   document_processing(pclause->clause);
   state->proc_non_trivial_count++;

   resclause = replacing_inferences(state, control, pclause);
   if(!resclause || ClauseIsEmpty(resclause))
   {
      if(resclause)
      {
         PStackPushP(state->extract_roots, resclause);
      }
      return resclause;
   }

   if(state->wlcontrol)
   {
      WatchlistCheck(state->wlcontrol, pclause->clause, state->archive,
                      control->heuristic_parms.watchlist_is_static,
                      state->signature);
   }

   /* Now on to backward simplification. */
   clausedate = ClauseSetListGetMaxDate(state->demods, FullRewrite);

   eliminate_backward_rewritten_clauses(state, control, pclause->clause, &clausedate);
   eliminate_backward_subsumed_clauses(state, pclause);
   eliminate_unit_simplified_clauses(state, pclause->clause);
   eliminate_context_sr_clauses(state, control, pclause->clause);
   ClauseSetSetProp(state->tmp_store, CPIsIRVictim);

   clause = pclause->clause;

   ClauseNormalizeVars(clause, state->freshvars);
   tmp_copy = ClauseCopyDisjoint(clause);
   tmp_copy->ident = clause->ident;

   clause->date = clausedate;
   ClauseSetProp(clause, CPLimitedRW);

   if(ClauseIsDemodulator(clause))
   {
      assert(clause->neg_lit_no == 0);
      if(EqnIsOriented(clause->literals))
      {
         TermCellSetProp(clause->literals->lterm, TPIsRewritable);
         state->processed_pos_rules->date = clausedate;
         ClauseSetIndexedInsert(state->processed_pos_rules, pclause);
      }
      else
      {
         state->processed_pos_eqns->date = clausedate;
         ClauseSetIndexedInsert(state->processed_pos_eqns, pclause);
      }
   }
   else if(ClauseLiteralNumber(clause) == 1)
   {
      assert(clause->neg_lit_no == 1);
      ClauseSetIndexedInsert(state->processed_neg_units, pclause);
   }
   else
   {
      ClauseSetIndexedInsert(state->processed_non_units, pclause);
   }
   GlobalIndicesInsertClause(&(state->gindices), clause);

   FVUnpackClause(pclause);
   ENSURE_NULL(pclause);
   if(state->wlcontrol && control->heuristic_parms.watchlist_simplify)
   {
      simplify_watchlist(state, control, clause);
   }
   if(control->heuristic_parms.selection_strategy != SelectNoGeneration)
   {
      generate_new_clauses(state, control, clause, tmp_copy);
   }
   ClauseFree(tmp_copy);
   if(TermCellStoreNodes(&(state->tmp_terms->term_store))>TMPBANK_GC_LIMIT)
   {
      TBGCSweep(state->tmp_terms);
   }
#ifdef PRINT_SHARING
   print_sharing_factor(state);
#endif
#ifdef PRINT_RW_STATE
   print_rw_state(state);
#endif
   if(control->heuristic_parms.detsort_tmpset)
   {
      ClauseSetSort(state->tmp_store, ClauseCmpByStructWeight);
   }
   if((empty = insert_new_clauses(state, control)))
   {
      PStackPushP(state->extract_roots, empty);
      return empty;
   }
   //
   //fprintf(GlobalOut, "%%STATE,%ld,%ld,%ld\n",
   //   state->processed_count,
   //   state->generated_count,
   //   state->paramod_count);
   //
   return NULL;
}


/*-----------------------------------------------------------------------
//
// Function:  Saturate()
//
//   Process clauses until either the empty clause has been derived, a
//   specified number of clauses has been processed, or the clause set
//   is saturated. Return empty clause (if found) or NULL.
//
// Global Variables: -
//
// Side Effects    : Modifies state.
//
/----------------------------------------------------------------------*/

Clause_p Saturate(ProofState_p state, ProofControl_p control, long
                  step_limit, long proc_limit, long unproc_limit, long
                  total_limit, long generated_limit, long tb_insert_limit,
                  long answer_limit)
{
   Clause_p unsatisfiable = NULL;
   long
      count = 0,
      sat_check_size_limit = control->heuristic_parms.sat_check_size_limit,
      sat_check_step_limit = control->heuristic_parms.sat_check_step_limit;

   while(!TimeIsUp &&
         !ClauseSetEmpty(state->unprocessed) &&
         step_limit   > count &&
         proc_limit   > ProofStateProcCardinality(state) &&
         unproc_limit > ProofStateUnprocCardinality(state) &&
         total_limit  > ProofStateCardinality(state) &&
         generated_limit > (state->generated_count -
                            state->backward_rewritten_count)&&
         tb_insert_limit > state->terms->insertions &&
         (!state->wlcontrol||!WatchlistEmpty(state->wlcontrol)))
   {
      count++;
      unsatisfiable = ProcessClause(state, control, answer_limit);
      if(unsatisfiable)
      {
         break;
      }
      unsatisfiable = cleanup_unprocessed_clauses(state, control);
      if(unsatisfiable)
      {
         break;
      }
      if(control->heuristic_parms.sat_check_grounding != GMNoGrounding)
      {
         if(ProofStateCardinality(state) >= sat_check_size_limit)
         {
            unsatisfiable = SATCheck(state, control);
            while(sat_check_size_limit <= ProofStateCardinality(state))
            {
               sat_check_size_limit += control->heuristic_parms.sat_check_size_limit;
            }
         }
         else if(state->proc_non_trivial_count >= sat_check_step_limit)
         {
            unsatisfiable = SATCheck(state, control);
            sat_check_step_limit += control->heuristic_parms.sat_check_step_limit;
         }
         if(unsatisfiable)
         {
            PStackPushP(state->extract_roots, unsatisfiable);
            break;
         }
      }
   }
   return unsatisfiable;
}

/*-----------------------------------------------------------------------
//
// Function: RemoveSubsumed()
//
//   Remove all clauses subsumed by subsumer from set, kill their
//   children. Return number of removed clauses.
//
// Global Variables: -
//
// Side Effects    : Changes set, memory operations.
//
/----------------------------------------------------------------------*/

long RemoveSubsumed(GlobalIndices_p indices,
                    FVPackedClause_p subsumer,
                    ClauseSet_p set,
                    ClauseSet_p archive,
                    WatchlistControl_p wlcontrol)
{
   Clause_p handle;
   long     res;
   PStack_p stack = PStackAlloc();
   Sig_p sig = (wlcontrol && WLNormalizeSkolemSymbols) ? wlcontrol->sig : NULL;
   
	res = ClauseSetFindFVSubsumedClauses(set, subsumer, stack, sig);
   
   while(!PStackEmpty(stack))
   {
      handle = PStackPopP(stack);
      //printf("# XXX Removing (remove_subumed()) %p from %p = %p\n", handle, set, handle->set);
      //printf("# XWL "); ClausePrint(GlobalOut, handle, true); printf("\n"); 
	   if(ClauseQueryProp(handle, CPWatchOnly))
      {
         assert(watch_progress);

         DocClauseQuote(GlobalOut, OutputLevel, 6, handle,
                        "extract_wl_subsumed", subsumer->clause);
         if (wlcontrol)
         {
            WatchlistUpdateProgress(wlcontrol, subsumer->clause, handle);
         }
         
         //fprintf(GlobalOut, "# Watchlist hit: ");
         //ClausePrint(GlobalOut, handle, true);
         //fprintf(GlobalOut, "\n");

         //fprintf(GlobalOut, "# ... by: ");
         //ClausePrint(GlobalOut, subsumer->clause, true);
         //fprintf(GlobalOut, "\n");
      }
      else
      {
         DocClauseQuote(GlobalOut, OutputLevel, 6, handle,
                        "subsumed", subsumer->clause);
      }
      ClauseKillChildren(handle);
      GlobalIndicesDeleteClause(indices, handle);
      if(BuildProofObject||ClauseIsDemodulator(handle))
      {
         ClauseSetExtractEntry(handle);
         ClauseSetInsert(archive, handle);
      }
      else
      {
         ClauseSetDeleteEntry(handle);
      }
   }
   PStackFree(stack);

   return res;
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/
