/*-----------------------------------------------------------------------

File  : fofshared.c

Author: Josef Urban

Contents
 
  Read an initial set of fof terms and print the (shared) codes of all subterms
  present in them. If file names given (or file and stdin), read both
  in, but only print the codes for the second one (this is intended to
  allow consistent codes over several runs).
 

  Copyright 1998, 1999 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Fri Nov 28 00:27:40 MET 1997

-----------------------------------------------------------------------*/

#include <stdio.h>
#include <string.h>
#include <cio_commandline.h>
#include <cio_output.h>
#include <cte_termbanks.h>
#include <ccl_formulafunc.h>
#include <ccl_proofstate.h>
#include <che_enigma.h>

/*---------------------------------------------------------------------*/
/*                  Data types                                         */
/*---------------------------------------------------------------------*/

typedef enum
{
   OPT_NOOPT=0,
   OPT_HELP,
   OPT_VERBOSE,
   OPT_FREE_NUMBERS,
   OPT_ENIGMA_FEATURES,
   OPT_OUTPUT
}OptionCodes;

/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/

OptCell opts[] =
{
    {OPT_HELP, 
        'h', "help", 
        NoArg, NULL,
        "Print a short description of program usage and options."},
    {OPT_VERBOSE, 
        'v', "verbose", 
        OptArg, "1",
        "Verbose comments on the progress of the program."},
    {OPT_OUTPUT,
        'o', "output-file",
        ReqArg, NULL,
        "Redirect output into the named file."},
   {OPT_ENIGMA_FEATURES,
      '\0', "enigma-features",
      ReqArg, NULL,
      "Enigma features to be generate. The value is a string of characters "
      "determining the features to be used. Valid characters are 'V' "
      "(vertical features), 'H' (horizontal), 'S' (symbols), 'L' "
      "(length stats) 'C' (conjecture)."},
   {OPT_FREE_NUMBERS,
    '\0', "free-numbers",
     NoArg, NULL,
     "Treat numbers (strings of decimal digits) as normal free function "
    "symbols in the input. By default, number now are supposed to denote"
    " domain constants and to be implicitly different from each other."},
    {OPT_NOOPT,
        '\0', NULL,
        NoArg, NULL,
        NULL}
};

char *outname = NULL;
FunctionProperties free_symb_prop = FPIgnoreProps;
EnigmaFeatures Enigma = EFAll;

/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/

CLState_p process_options(int argc, char* argv[]);
void print_help(FILE* out);

/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/


static char* top_symbol_string(Term_p term, Sig_p sig)
{
   if (TermIsVar(term)) 
   {
      return ENIGMA_VAR;
   }
   else if ((strncmp(SigFindName(sig, term->f_code), "esk", 3) == 0)) 
   {
      return ENIGMA_SKO;
   }
   else 
   {
      return SigFindName(sig, term->f_code);
   }
}

static void term_features_string(DStr_p str, Term_p term, Sig_p sig, char* sym1, char* sym2)
{
   assert(Enigma & EFVertical);

   char* sym3 = top_symbol_string(term, sig);

   // vertical features
   if (Enigma & EFVertical)
   {
      DStrAppendStr(str, sym1); DStrAppendChar(str, ':');
      DStrAppendStr(str, sym2); DStrAppendChar(str, ':');
      DStrAppendStr(str, sym3); DStrAppendChar(str, ' ');
   }
   
   if (TermIsVar(term)||(TermIsConst(term))) 
   {
      return;
   }
   for (int i=0; i<term->arity; i++)
   {
      term_features_string(str, term->args[i], sig, sym2, sym3);
   }

   // horizontal features (functions only)
   if (Enigma & EFHorizontal)
   {
      DStr_p hstr = FeaturesGetTermHorizontal(sym3, term, sig);
      DStrAppendDStr(str, hstr);
      DStrAppendChar(str, ' ');
      DStrFree(hstr);
   }
}

static void clause_features_string(DStr_p str, Clause_p clause, Sig_p sig, long* vec)
{
   for(Eqn_p lit = clause->literals; lit; lit = lit->next)
   {
      char* sym1 = EqnIsPositive(lit)?ENIGMA_POS:ENIGMA_NEG;
      if (lit->rterm->f_code == SIG_TRUE_CODE)
      {
         char* sym2 = SigFindName(sig, lit->lterm->f_code);

         // traverse verticals/horizontals 
         for (int i=0; i<lit->lterm->arity; i++) // here we ignore prop. constants
         {
            term_features_string(str, lit->lterm->args[i], sig, sym1, sym2);
         }

         // top-level horizontal
         if ((Enigma & EFHorizontal) && (lit->lterm->arity > 0))
         {
            DStr_p hstr = FeaturesGetTermHorizontal(sym2, lit->lterm, sig);
            DStrAppendDStr(str, hstr);
            DStrAppendChar(str, ' ');
            DStrFree(hstr);
         }
      }
      else
      {
         char* sym2 = ENIGMA_EQ;
         
         // traverse verticals/horizontals 
         term_features_string(str, lit->lterm, sig, sym1, sym2);
         term_features_string(str, lit->rterm, sig, sym1, sym2);

         // top-level horizontal
         if (Enigma & EFHorizontal)
         {
            DStr_p hstr = FeaturesGetEqHorizontal(lit->lterm, lit->rterm, sig);
            DStrAppendDStr(str, hstr);
            DStrAppendChar(str, ' ');
            DStrFree(hstr);
         }
      }
   }

   if (vec)
   {
      PStack_p mod_stack = PStackAlloc();
      ClauseAddSymbolFeatures(clause, mod_stack, vec);
      PStackFree(mod_stack);
   }
}
/*
static void clause_static_features_string(DStr_p str, long* vec, Sig_p sig)
{
   static char fstr[1024];

   if (Enigma & EFLengths) 
   {
      snprintf(fstr, 1024, "!LEN/%ld ", vec[0]); DStrAppendStr(str, fstr);
      snprintf(fstr, 1024, "!POS/%ld ", vec[1]); DStrAppendStr(str, fstr);
      snprintf(fstr, 1024, "!NEG/%ld ", vec[2]); DStrAppendStr(str, fstr);
   }

   if (!(Enigma & EFSymbols)) 
   {
      return;
   }
   
   for (long f=sig->internal_symbols+1; f<=sig->f_count; f++)
   {
      char* fname = SigFindName(sig, f);
      if ((strlen(fname)>3) && (strncmp(fname, "esk", 3) == 0))
      {
         continue;
      }
      if (vec[3+4*f+0] > 0) 
      {
         snprintf(fstr, 1024, "#+%s/%ld ", fname, vec[3+4*f+0]); DStrAppendStr(str, fstr);
         snprintf(fstr, 1024, "%%+%s/%ld ", fname, vec[3+4*f+1]+1); DStrAppendStr(str, fstr);
      }
      if (vec[3+4*f+2] > 0) 
      {
         snprintf(fstr, 1024, "#-%s/%ld ", fname, vec[3+4*f+2]); DStrAppendStr(str, fstr);
         snprintf(fstr, 1024, "%%-%s/%ld ", fname, vec[3+4*f+3]+1); DStrAppendStr(str, fstr);
      }
   }
}
*/

static void clause_static_features_string(DStr_p str, long* vec, Sig_p sig)
{
   static char fstr[1024];

   if (Enigma & EFLengths) 
   {
      snprintf(fstr, 1024, "!LEN/%ld ", vec[0]); DStrAppendStr(str, fstr);
      snprintf(fstr, 1024, "!POS/%ld ", vec[1]); DStrAppendStr(str, fstr);
      snprintf(fstr, 1024, "!NEG/%ld ", vec[2]); DStrAppendStr(str, fstr);
      snprintf(fstr, 1024, "!SCH/%ld ", vec[3]); DStrAppendStr(str, fstr);
   }

   if (!(Enigma & EFSymbols)) 
   {
      return;
   }
   
   for (long f=sig->internal_symbols+1; f<=sig->f_count; f++)
   {
      char* fname = SigFindName(sig, f);
      if ((strlen(fname)>3) && (strncmp(fname, "esk", 3) == 0))
      {
         continue;
      }
      if (vec[4+4*f+0] > 0) // All lines below this in the method have been changed by John to allow the !SCH feature at index 3
      {
         snprintf(fstr, 1024, "#+%s/%ld ", fname, vec[4+4*f+0]); DStrAppendStr(str, fstr);  
         snprintf(fstr, 1024, "%%+%s/%ld ", fname, vec[4+4*f+1]+1); DStrAppendStr(str, fstr);
      }
      if (vec[4+4*f+2] > 0) 
      {
         snprintf(fstr, 1024, "#-%s/%ld ", fname, vec[4+4*f+2]); DStrAppendStr(str, fstr);
         snprintf(fstr, 1024, "%%-%s/%ld ", fname, vec[4+4*f+3]+1); DStrAppendStr(str, fstr);
      }
   }
}
/*
static DStr_p get_conjecture_features_string(char* filename, TB_p bank)
{
   static long* vec = NULL;
   static size_t size = 0;
   if (!vec)
   {
      size = (3+4*64)*sizeof(long); // start with memory for 64 symbols
      vec = RegMemAlloc(size);
   }
   vec = RegMemProvide(vec, &size, (3+4*(bank->sig->f_count+1))*sizeof(long));
   for (int i=0; i<3+4*(bank->sig->f_count+1); i++) { vec[i] = 0L; }

   DStr_p str = DStrAlloc();
   Scanner_p in = CreateScanner(StreamTypeFile, filename, true, NULL);
   ScannerSetFormat(in, TSTPFormat);
   while (TestInpId(in, "cnf"))
   {
      Clause_p clause = ClauseParse(in, bank);
      vec = RegMemProvide(vec, &size, (3+4*(bank->sig->f_count+1))*sizeof(long));
      if (ClauseQueryTPTPType(clause) == CPTypeNegConjecture) 
      {
         vec[0] += (long)ClauseWeight(clause,1,1,1,1,1,false);
         vec[1] += clause->pos_lit_no;
         vec[2] += clause->neg_lit_no;
         clause_features_string(str, clause, bank->sig, &vec[3]);
      }
      ClauseFree(clause);
   }
   CheckInpTok(in, NoToken);
   DestroyScanner(in);

   clause_static_features_string(str, vec, bank->sig);
   DStrDeleteLastChar(str);
   return str;
}
*/

static DStr_p get_conjecture_features_string(char* filename, TB_p bank)
{
   static long* vec = NULL;
   static size_t size = 0;
   if (!vec)
   {
      size = (4+4*64)*sizeof(long); // start with memory for 64 symbols, John changed 3 to 4
      vec = RegMemAlloc(size);
   }
   vec = RegMemProvide(vec, &size, (4+4*(bank->sig->f_count+1))*sizeof(long));   //John
   for (int i=0; i<4+4*(bank->sig->f_count+1); i++) { vec[i] = 0L; }  //John

   DStr_p str = DStrAlloc();
   Scanner_p in = CreateScanner(StreamTypeFile, filename, true, NULL);
   ScannerSetFormat(in, TSTPFormat);
   while (TestInpId(in, "cnf"))
   {
      Clause_p clause = ClauseParse(in, bank);
      vec = RegMemProvide(vec, &size, (4+4*(bank->sig->f_count+1))*sizeof(long));  //John
      if (ClauseQueryTPTPType(clause) == CPTypeNegConjecture) 
      {
         vec[0] += (long)ClauseWeight(clause,1,1,1,1,1,false);
         vec[1] += clause->pos_lit_no;
         vec[2] += clause->neg_lit_no;
         int schema = 0;  //John
         if (ClauseQueryProp(clause,CPIsSchema))
         {
				schema = 1;
			}
			vec[3] += schema;
         clause_features_string(str, clause, bank->sig, &vec[4]); //John
      }
      ClauseFree(clause);
   }
   CheckInpTok(in, NoToken);
   DestroyScanner(in);

   clause_static_features_string(str, vec, bank->sig);
   DStrDeleteLastChar(str);
   return str;
}

// TODO: join these two!
static DStr_p get_theory_features_string(char* filename, TB_p bank)
{
   static long* vec = NULL;
   static size_t size = 0;
   if (!vec)
   {
      size = (4+4*64)*sizeof(long); // start with memory for 64 symbols, John changed 3 to 4
      vec = RegMemAlloc(size);
   }
   vec = RegMemProvide(vec, &size, (4+4*(bank->sig->f_count+1))*sizeof(long));  //John
   for (int i=0; i<4+4*(bank->sig->f_count+1); i++) { vec[i] = 0L; }  //John

   DStr_p str = DStrAlloc();
   Scanner_p in = CreateScanner(StreamTypeFile, filename, true, NULL);
   ScannerSetFormat(in, TSTPFormat);
   while (TestInpId(in, "cnf"))
   {
      Clause_p clause = ClauseParse(in, bank);
      vec = RegMemProvide(vec, &size, (4+4*(bank->sig->f_count+1))*sizeof(long));  //John
      if (ClauseQueryTPTPType(clause) != CPTypeNegConjecture) 
      {
         vec[0] += (long)ClauseWeight(clause,1,1,1,1,1,false);
         vec[1] += clause->pos_lit_no;
         vec[2] += clause->neg_lit_no;
         int schema = 0;  //John
         if (ClauseQueryProp(clause,CPIsSchema))
         {
				schema = 1;
			}
			vec[3] += schema;
         clause_features_string(str, clause, bank->sig, &vec[4]);  //John
      }
      ClauseFree(clause);
   }
   CheckInpTok(in, NoToken);
   DestroyScanner(in);

   clause_static_features_string(str, vec, bank->sig);
   DStrDeleteLastChar(str);
   return str;
}

int main(int argc, char* argv[])
{
   InitIO(argv[0]);
   CLState_p args = process_options(argc, argv);
   //SetMemoryLimit(2L*1024*MEGA);
   OutputFormat = TSTPFormat;
   if (outname) { OpenGlobalOut(outname); }
   ProofState_p state = ProofStateAlloc(free_symb_prop);
   TB_p bank = state->terms;
  
   DStr_p cstr = get_conjecture_features_string(args->argv[0], bank);
   DStr_p tstr = get_theory_features_string(args->argv[0], bank);

   fprintf(GlobalOut, "#|%s|%s\n", DStrView(tstr), DStrView(cstr));

   DStrFree(cstr);
   DStrFree(tstr);
   
   ProofStateFree(state);
   CLStateFree(args);
   ExitIO();

   return 0;
}


/*-----------------------------------------------------------------------
//
// Function: process_options()
//
//   Read and process the command line option, return (the pointer to)
//   a CLState object containing the remaining arguments.
//
// Global Variables: opts, Verbose, TermPrologArgs,
//                   TBPrintInternalInfo 
//
// Side Effects    : Sets variables, may terminate with program
//                   description if option -h or --help was present
//
/----------------------------------------------------------------------*/

CLState_p process_options(int argc, char* argv[])
{
   Opt_p handle;
   CLState_p state;
   char*  arg;
   
   state = CLStateAlloc(argc,argv);
   
   while((handle = CLStateGetOpt(state, &arg, opts)))
   {
      switch(handle->option_code)
      {
      case OPT_VERBOSE:
             Verbose = CLStateGetIntArg(handle, arg);
             break;
      case OPT_HELP: 
             print_help(stdout);
             exit(NO_ERROR);
      case OPT_OUTPUT:
             outname = arg;
             break;
      case OPT_ENIGMA_FEATURES:
             Enigma = ParseEnigmaFeaturesSpec(arg);
             break;
      case OPT_FREE_NUMBERS:
            free_symb_prop = free_symb_prop|FPIsInteger|FPIsRational|FPIsFloat;
            break;
      default:
          assert(false);
          break;
      }
   }

   if (state->argc < 1 || state->argc > 3)
   {
      print_help(stdout);
      exit(NO_ERROR);
   }
   
   return state;
}
 
void print_help(FILE* out)
{
   fprintf(out, "\n\
\n\
Usage: enigma-problem-features [options] cnf.tptp\n\
\n\
Make enigma features from TPTP problem in CNF.\n\
\n");
   PrintOptions(stdout, opts, NULL);
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/


