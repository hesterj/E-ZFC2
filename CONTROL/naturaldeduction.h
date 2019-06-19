#ifndef NATURALDEDUCTION

#define NATURALDEDUCTION

#include <clb_os_wrapper.h>
#include <cio_signals.h>
#include <ccl_fcvindexing.h>
#include <che_heuristics.h>
#include <che_axiomscan.h>
#include <che_to_autoselect.h>
#include <cco_clausesplitting.h>
#include <cco_forward_contraction.h>
#include <cco_interpreted.h>
#include <ccl_satinterface.h>
#include <time.h>
#include <arpa/inet.h>

typedef struct ndcell 
{
	PStack_p derivation;
	PStack_p absolutely_flagged_variables;
	PStack_p relatively_flagged_variables;
	
	PStack_p predicates;
	PStack_p functions;
	
	FormulaSet_p nd_derivation;
	FormulaSet_p nd_generated;
	FormulaSet_p nd_temporary_formulas;
	FormulaSet_p branch_formulas; // the formulas that are exlusive to this branch
	
	long generated_formulas;
	VarBank_p     freshvars;
	TB_p          terms;
	Sig_p         signature;
	
	WFormula_p goal;
	WFormula_p last_assumption;
	
	bool active;
	
   struct nd_set_cell* set;      /* Is the formula in a set? */
   struct ndcell* pred;        /* For fomula sets = doubly  */
   struct ndcell* succ;        /* linked lists */
	
}NDCell, *ND_p;

/*
typedef struct connectioncell
{
	
}
*/

#define NDCellAlloc() (NDCell*)SizeMalloc(sizeof(NDCell))
#define NDCellFree(junk) SizeFree(junk, sizeof(NDCell))
ND_p NDAlloc(ProofState_p initial);
ND_p NDAllocAssumption(ND_p initial);
void NDAssumptionControlFree(ND_p initial);
void NDFree(ND_p initial);
void NDCloseAssumption(ND_p initial);

WFormula_p NDAndIntroduction(ND_p control, TB_p bank, WFormula_p a, WFormula_p b);
WFormula_p NDOrIntroduction(ND_p control, TB_p bank, WFormula_p a, WFormula_p b);
WFormula_p NDImplIntroduction(ND_p control,TB_p bank, WFormula_p a, WFormula_p b);
WFormula_p NDNegIntroduction(ND_p control,TB_p bank, WFormula_p a, WFormula_p b, WFormula_p c);
WFormula_p NDUniversalIntroduction(ND_p control,TB_p bank, Term_p term, Term_p variable, WFormula_p formula);
WFormula_p NDExistentialIntroduction(ND_p control,TB_p bank, Term_p term, Term_p variable, WFormula_p formula);

WFormula_p NDAndElimination(ND_p control,TB_p bank, WFormula_p conjunct, int select);
WFormula_p NDOrElimination(ND_p control,TB_p bank, WFormula_p a,WFormula_p b);
WFormula_p NDImplElimination(ND_p control,TB_p bank, WFormula_p a,WFormula_p b);
WFormula_p NDNegationElimination(ND_p control,TB_p bank, WFormula_p a);
WFormula_p NDUniversalElimination(ND_p control,TB_p bank, WFormula_p a, Term_p substitute);
WFormula_p NDExistentialElimination(ND_p control,TB_p bank, WFormula_p a, Term_p substitute);  // Quine
WFormula_p NDExistentialElimination2(ND_p control,TB_p bank, WFormula_p existential, WFormula_p psi);  //Gentzen

long NDAndIntProcess(ND_p control,TB_p bank,WFormula_p selected);
long NDOrIntProcess(ND_p control,TB_p bank,WFormula_p selected);
long NDImplIntProcess(ND_p control,TB_p bank,WFormula_p selected);
long NDNegIntProcess(ND_p control,TB_p bank,WFormula_p selected);
long NDUniversalIntProcess(ND_p control,TB_p bank,WFormula_p selected);
long NDExistentialIntProcess(ND_p control,TB_p bank,WFormula_p selected);

long NDOrElimProcess(ND_p control,TB_p bank,WFormula_p selected);
long NDAndElimProcess(ND_p control,TB_p bank,WFormula_p selected);
long NDImplElimProcess(ND_p control,TB_p bank,WFormula_p selected);
long NDNegElimProcess(ND_p control,TB_p bank,WFormula_p selected);
long NDUniversalElimProcess(ND_p control,TB_p bank,WFormula_p selected);
long NDExistentialElimProcess(ND_p control,TB_p bank,WFormula_p selected);
/*
int NDSaturate(ProofState_p state, ProofControl_p control, long
                  step_limit, long proc_limit, long unproc_limit, long
                  total_limit,  long generated_limit, long tb_insert_limit,
                  long answer_limit);
*/
void NDGenerateAndScoreFormulas(ND_p ndcontrol, WFormula_p handle);
int NDStartNewAssumption(ND_p ndcontrol, int socketDescriptor);

//void NDProofSearch(ND_p control,ND_Derivation_p derivation);
bool NDFormulaSetCheckForContradictions(ND_p control, FormulaSet_p formulaset);
bool NDUnify(ND_p control, Subst_p subst, Term_p s, Term_p t);
//bool NDAssumptionCheckForContradictions(NDAssumption_p derivation);
//bool NDAssumptionGoalIsReached(ND_p control,NDAssumption_p derivation);

void NDPInitializeDerivationGoal(ND_p input, FormulaSet_p source);
bool NDPDerivationGoalIsReached(ND_p control);

void pstack_push_skip(PStack_p target, PStack_p source, Term_p skip);
long nd_term_collect_subterms(Sig_p sig, Term_p term, PStack_p collector);
long nd_collect_subterms(ND_p control, Sig_p sig, Term_p term, PStack_p collector);
long nd_collect_subterms2(ND_p control, Sig_p sig, Term_p term, PStack_p collector);
long nd_label_symbols(ND_p control,Term_p term);
void NDSaturateLoop(ND_p ndcontrol, long loops);
void ProofTest(ND_p ndcontrol);
void ContradictionTest(ND_p ndcontrol);

void NDResetState(ND_p ndcontrol);
                  
// inline functions
                  
static __inline__ bool PStackFindInt(PStack_p res, FunCode handle);
static __inline__ bool PStackFindTerm(PStack_p res, Term_p handle);
static __inline__ bool FunCodeIsPredicate(ND_p res, FunCode handle);
static __inline__ bool FunCodeIsFunction(ND_p res, FunCode handle);
static __inline__ PStack_p PStackRemoveDuplicatesInt(PStack_p handle);
static __inline__ PStack_p PStackRemoveDuplicatesTerm(PStack_p handle);
static __inline__ void PStackPrintFunCodes(ND_p control, PStack_p handle);
static __inline__ void UpdateControlSymbols(ND_p control);
//static void PStackPrintTerms(ND_p control, PStack_p handle);

#define NDAbsolutelyFlagTerm(control,term) PStackPushP(control->absolutely_flagged_variables,term)
#define NDRelativelyFlagTerms(control,stack) PStackPushStack(control->relatively_flagged_variables,stack)
#define NDTermIsAbsolutelyFlagged(control,term) PStackFindTerm(control->absolutely_flagged_variables,term)
#define NDTermIsRelateivelyFlagged(control,term) PStackFindTerm(control->relatively_flagged_variables,term)

// remove duplicates in the predicates and function stacks

void FormulaSetUpdateControlSymbols(ND_p control, FormulaSet_p target);

/*  Inline function definitions
*/


static __inline__ void UpdateControlSymbols(ND_p control)
{
   PStack_p predicates_duplicates_removed = PStackRemoveDuplicatesInt(control->predicates);
   PStack_p functions_duplicates_removed = PStackRemoveDuplicatesInt(control->functions);
   control->predicates = predicates_duplicates_removed;
   control->functions = functions_duplicates_removed;
}

//  check if funcode is predicate symbol

static __inline__ bool FunCodeIsPredicate(ND_p res, FunCode handle)
{
	return PStackFindInt(res->predicates,handle);
}

// check if funcode is function symbol

static __inline__ bool FunCodeIsFunction(ND_p res, FunCode handle)
{
	return PStackFindInt(res->functions,handle);
}

//  returns true if handle is an element of res

static __inline__ bool PStackFindInt(PStack_p res, FunCode handle)
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

//  look for duplicate Term_p in res

static __inline__ bool PStackFindTerm(PStack_p res, Term_p handle)
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

// returns copy of handle with duplicates removed

static __inline__ PStack_p PStackRemoveDuplicatesInt(PStack_p handle)
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
	PStackFree(handle);
	return res;
}

// unfinished

static __inline__ PStack_p PStackRemoveDuplicatesTerm(PStack_p handle)
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

// print the funcodes in the stack handle

static __inline__ void PStackPrintFunCodes(ND_p control, PStack_p handle)
{
	PStackPointer i;
	for(i=0; i<PStackGetSP(handle); i++)
	{
		printf("\n%s",SigFindName(control->signature,PStackElementInt(handle,i)));
	}
}



#endif
