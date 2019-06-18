/*-----------------------------------------------------------------------

File  : cco_proofproc.h

Author: Stephan Schulz

Contents

  Top level proof procedure

  Copyright 1998-2016 by the author.
  This code is released under the GNU General Public Licence and
  the GNU Lesser General Public License.
  See the file COPYING in the main E directory for details..
  Run "eprover -h" for contact information.

Changes

<1> Mon Jun  8 04:19:50 MET DST 1998
    New

-----------------------------------------------------------------------*/

#ifndef CCO_PROOFPROC

#define CCO_PROOFPROC

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


/*---------------------------------------------------------------------*/
/*                    Data type declarations                           */
/*---------------------------------------------------------------------*/



/*---------------------------------------------------------------------*/
/*                Exported Functions and Variables                     */
/*---------------------------------------------------------------------*/

PERF_CTR_DECL(ParamodTimer);
PERF_CTR_DECL(BWRWTimer);


/* Collect term cells from temporary clause copies if their number
   reaches this. 10000 is big enough that it nearly never happens, 500
   is big enough that it rarely happens, but that the bank remains
   small enough. */
#define TMPBANK_GC_LIMIT 256

void     ProofControlInit(ProofState_p state, ProofControl_p control,
           HeuristicParms_p params,
                          FVIndexParms_p fvi_params,
                          PStack_p wfcb_defs,
                          PStack_p hcb_defs);
void     ProofStateInit(ProofState_p state, ProofControl_p control);
void     ProofStateResetProcessedSet(ProofState_p state,
                                     ProofControl_p control,
                                     ClauseSet_p set);
void     ProofStateResetProcessed(ProofState_p state,
                                  ProofControl_p control);
Clause_p ProcessClause(ProofState_p state, ProofControl_p control,
                       long answer_limit);
Clause_p Saturate(ProofState_p state, ProofControl_p control, long
                  step_limit, long proc_limit, long unproc_limit, long
                  total_limit,  long generated_limit, long tb_insert_limit,
                  long answer_limit);
long RemoveSubsumed(GlobalIndices_p indices,
                            FVPackedClause_p subsumer,
                            ClauseSet_p set,
                            ClauseSet_p archive,
                            WatchlistControl_p wlcontrol);
                            
// ZFC Functions

void eval_clause_set_given(ProofState_p state, ProofControl_p control, ClauseSet_p set);
long compute_schemas_tform(ProofControl_p control, 
						   TB_p bank, 
						   OCB_p ocb, 
						   Clause_p clause,
						   ClauseSet_p store, 
						   VarBank_p freshvars, 
						   ProofState_p state);
TFormula_p tformula_comprehension(TB_p bank, ProofState_p state, PTree_p* freevars, TFormula_p input); // for clauses
TFormula_p tformula_comprehension2(ProofState_p state, PStack_p freevars, PStackPointer position, TFormula_p input);  //for tformula, full comprehension
ClauseSet_p tformula_replacement(TB_p bank, ProofState_p state, PTree_p* freevars, TFormula_p input, Clause_p clause);  //bugged

Clause_p ClauseMergeVars(Clause_p clause,  TB_p bank, Term_p x, Term_p y);
FormulaSet_p GenerateComprehensionInstances(ProofState_p proofstate, FormulaSet_p input);
FormulaSet_p GeneralizeFormulas(ProofState_p proofstate, FormulaSet_p input, int iterations);

long TFormulaCollectSubformulas(ProofState_p state, TFormula_p input, FormulaSet_p collector);
long WFormulaCollectSubformulas(ProofState_p state, WFormula_p input, FormulaSet_p collector);
long FormulaSetCollectSubformulas(ProofState_p state, FormulaSet_p input, FormulaSet_p collector);
bool TermIsPredicate(Term_p term);
bool SubformulaCandidateCheck(Sig_p sig, Term_p term);
bool TermIsBooleanSymbol(Sig_p sig, Term_p term);
int LabelFunctionSymbols(ProofState_p control, Term_p term,PStack_p function_symbols);
bool PStackFindInt(PStack_p res, FunCode handle);
PStack_p PStackRemoveDuplicatesInt(PStack_p handle);
PStack_p PStackRemoveDuplicatesTerm(PStack_p handle);
bool PStackFindTerm(PStack_p res, Term_p handle);
long CollectSubterms(ProofState_p proofstate, Term_p term, PStack_p collector, PStack_p function_symbols);
PStack_p FormulaSetLabelFunctionSymbols(ProofState_p control, FormulaSet_p set);
PStack_p FormulaSetCollectSubterms(ProofState_p control, FormulaSet_p set);

#endif

/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/
