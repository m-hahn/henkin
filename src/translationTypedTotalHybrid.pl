/*************************************************************************

    File: translationTotalTypedHybrid.pl
    Copyright (C) 2015 Michael Hahn

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.


*************************************************************************/

% Typed Translation (with total functional application),
%  with special treatment of terms of type t

:- module(translationTypedTotalHybrid,[translateHybrid/5]).
:- op(500,xfx,@).
:- op(500,xf,istrue).


/*
* Assumptions about the input:
*  functions of type t>t must be connectives from a fixed vocabulary (they are translated to Prolog functors)
*/

/*======================================
   Composing FO formula
=======================================*/



translateHybrid(Term, FOTerm, Conds, TypeStatements,Constants) :-
      translationTypedTotalHybrid:translate(Term, FOTerm, [] - Conds, ((true = true) - TypeStatements), 0 - _, [] - _, _, formula, []-Predicates,[]-Constants),!.





/*==================================*/

buildFormula(FOTerm,Conds, FormulaResult) :-
    ((Type = t,!); (write('buildFormula/3: Wrong type: '),write(Type),nl)),
      Matrix = FOTerm,
      buildConditions(Conds, Matrix, FormulaResult).
buildFormula(A,B,C) :-
      write(buildFormula(A,B,C)),nl,fail.

buildConditions([],Matrix,Matrix) :- !.
buildConditions([Definition|Tail], Matrix, imp(Condition,InnerResult)) :-
      buildConditions(Tail, Matrix, InnerResult),
      addCondition(Definition, Condition).
buildConditions(A,B,C) :-
      write(buildConditions(A,B,C)),nl,fail.


addCondition((TermName,(Var, TypeOfVarR), Equation, LambdaType, FreeVariables), all(Var,imp(has_type(Var,TypeOfVarR),DefinitionFormula))) :-
      foTranslation:translateType(LambdaType, LambdaTypeTranslated),
      buildDefinitionFormula(and(has_type(TermName, LambdaTypeTranslated),Equation),TermName, LambdaType,FreeVariables, DefinitionFormula).
addCondition(A,B) :-
      write(addCondition(A,B)),nl,fail.

buildDefinitionFormula(Equation, _, _, [], Equation).
buildDefinitionFormula(Equation, TermName, LambdaType, [(Var,VarType)|Tail], all(Var,imp(has_type(Var,VarTypeTranslated),InnerFormula))) :-
      foTranslation:translateType(VarType, VarTypeTranslated),
      buildDefinitionFormula(Equation, TermName, LambdaType, Tail, InnerFormula).

buildDefinitionFormula(A,B,C,D,E) :-
      write(buildDefinitionFormula(A,B,C,D,E)),nl,fail.






/*========================================================
          Translation
=========================================================*/
/*  
    (1) HO Input
    (2) FO Output
    (3) Definitions
    (4) Type Declarations for Constants
    (5) Counter for constants
    (6) cache of lambda terms encountered
    (7) variables free in HO Input
    (8) predicates
    (9) linguistic constants
*/
translationTypedTotalHybrid:translate((Var,VarType), Var, Form - Form, TypeState-TypeState, Counter-Counter, TermCache-TermCache, [(Var,VarType)],term, Predicates-Predicates,Cons-Cons) :-
      var(Var), !.
translationTypedTotalHybrid:translate((Var, t), Var istrue, Form-Form, TypeState-TypeState,Counter-Counter,TermCache-TermCache, [(Var,t)], formula, Predicates-Predicates,Cons-Cons) :-
      var(Var), !.
translationTypedTotalHybrid:translate((Term, t), Term istrue, Form-Form, TypeState-and(has_type(Term, t), TypeState),Counter-Counter,TermCache-TermCache, [], formula, Predicates-Predicates,Cons-[(Term,t)|Cons]) :-
      atom(Term), !.
translationTypedTotalHybrid:translate(((A @ B), t), Result, FormulasIn - FormulasOut, TypeIn-TypeOut, CounterIn-CounterOut,CacheIn-CacheOut, FreeVars,formula, PredicatesIn-PredicatesOut,ConsIn-ConsOut) :-
     translateT(((A @ B), t), Result, FormulasIn - FormulasOut, TypeIn- TypeOut, CounterIn-CounterOut,CacheIn-CacheOut, FreeVars, PredicatesIn-PredicatesOut,ConsIn-ConsOut),!.
translationTypedTotalHybrid:translate(((A @ B), _), f(A2, B2), Formulas - Formulas3, TypeStateIn - TypeStateOut, CounterIn - CounterOut, TermCacheIn-TermCacheOut, FreeVars, term, PredicatesIn-PredicatesOut,ConsIn-ConsOut) :-
      translationTypedTotalHybrid:translate(A,A2,Formulas - Formulas2, TypeStateIn - TypeState2, CounterIn - CounterMid, TermCacheIn-TermCacheMid, FreeVarsA, term, PredicatesIn-PredicatesMid,ConsIn-ConsMid),
      translationTypedTotalHybrid:translate(B,B2,Formulas2 - Formulas3, TypeState2 - TypeStateOut, CounterMid - CounterOut, TermCacheMid-TermCacheOut, FreeVarsB, term, PredicatesMid-PredicatesOut,ConsMid-ConsOut),
      betaConversion:unionNoUnification(FreeVarsA, FreeVarsB, FreeVars),!.


translationTypedTotalHybrid:translate(HOTerm, TermName, DefinitionsIn - DefinitionsOut, TypeStateIn - TypeStateOut, CounterIn - CounterOut, TermCacheIn - TermCacheOut, FreeVariables, term, PredicatesIn-PredicatesOut,ConsIn-ConsOut) :-
      HOTerm = (lam((Var,TypeOfVar),Term),LambdaType),!,
     % take term from cache
     (
     % problems with variables, e.g.: 'lambda x.xy' and 'lambda y.xy' look the same
      (fail,findTerm(TermCacheIn, HOTerm, TermName, FreeVariables), !, TermCacheOut = TermCacheIn, TypeStateOut = TypeStateIn, DefinitionsOut = DefinitionsIn, CounterIn = CounterOut, PredicatesIn=PredicatesOut,ConsIn=ConsOut);

      % translate lambda expression with function term and a defining equation
      (
       translationTypedTotalHybrid:translate(Term, TermTrans, [Defi|DefinitionsIn]-DefinitionsOut, TypeStateIn - TypeStateMid, CounterIn - CounterMid, TermCacheIn - TermCacheMid, FreeVariablesIn, TranslationType, PredicatesIn-PredicatesOut,ConsIn-ConsOut),
       % Updated Bookkeeping lists
       betaConversion:deleteNoUnification(FreeVariablesIn, (Var, TypeOfVar), FreeVariables, single),
       %Term = (_, TypeOfTerm),
       TermCacheOut = [(TermName, HOTerm, FreeVariablesIn)|TermCacheMid],
       TypeStateOut = TypeStateMid,

       % create term with defining equation
       foTranslation:translateType(TypeOfVar, TypeOfVarR),
       foTranslation:projectToTermComponent(FreeVariables, Arguments),
       foTranslation:createConstant(TermName, CounterMid, CounterOut, Arguments),
       ((LambdaType = (_ > SecondType), SecondType == t, TranslationType = formula, !, Defi = (TermName,(Var, TypeOfVarR), iff(TermTrans, f(TermName,Var) istrue), LambdaType, FreeVariables));
       (Defi = (TermName,(Var, TypeOfVarR), TermTrans = f(TermName,Var), LambdaType, FreeVariables)))
      
      )),!.


translationTypedTotalHybrid:translate(Term, Result, Form - Form, TypeState - and(TypeStatement,TypeState), Counter - Counter, TermCache-TermCache, [], term, Predicates-Predicates,ConsIn-[Term|ConsIn]) :-
      betaConversion:isParametrizedTy2Constant(Term),!,
      foTranslation:translateParametrizedTy2Constant(Term, Result, TypeStatement),!.

translationTypedTotalHybrid:translate((Atom, Type), Atom, Form - Form, TypeStatements - and(has_type(Atom, TypeR), TypeStatements), Counter-Counter, TermCache-TermCache, [], term, Predicates-Predicates, ConsIn-[(Atom, Type)|ConsIn]) :-
      atom(Atom),
      foTranslation:translateType(Type,TypeR),!.

translationTypedTotalHybrid:translate(A, B,C,D,E,F,G,H,I,J) :-
      write('translate '),
      write(translationTypedTotalHybrid:translate(A, B,C,D,E,F,G,H,I,J)),nl,nl,
      fail.

/*=================================*/

translateT(((ATerm, AType) @ B, t), Result, FormulasIn-FormulasOut, TypeIn-TypeOut, CounterIn-CounterOut, CacheIn-CacheOut,FreeVars,PredicatesIn-PredicatesOut,ConsIn-ConsOut) :-
      var(ATerm),!,
      Result = (f(ATerm,B2) istrue),
      translationTypedTotalHybrid:translate(B,B2,FormulasIn-FormulasOut,TypeIn-TypeOut,CounterIn-CounterOut,CacheIn-CacheOut,FreeVarsB, term, PredicatesIn-PredicatesOut,ConsIn-ConsOut),
  betaConversion:unionNoUnification(FreeVarsB, [(ATerm,AType)], FreeVars).


translateT(((((ATerm, AType) @ B), _) @ C, t), Result, FormulasIn-FormulasOut, TypeIn-TypeOut, CounterIn-CounterOut, CacheIn-CacheOut,FreeVars,PredicatesIn-PredicatesOut,ConsIn-ConsOut) :-
      var(ATerm),!,
      Result = (f(f(ATerm,BT),CT) istrue),
      translationTypedTotalHybrid:translate(B,BT,FormulasIn-FormulasMid,TypeIn-TypeMid,CounterIn-CounterMid,CacheIn-CacheMid,FreeVarsB, term, PredicatesIn-PredicatesMid,ConsIn-ConsMid),
      translationTypedTotalHybrid:translate(C,CT,FormulasMid-FormulasOut,TypeMid-TypeOut,CounterMid-CounterOut,CacheMid-CacheOut,FreeVarsC, term, PredicatesMid-PredicatesOut,ConsMid-ConsOut),
  betaConversion:unionNoUnification(FreeVarsB, [(ATerm,AType)|FreeVarsC], FreeVars).


translateT(((((eq(EqType),_) @ A, _) @ B), t), iff(A2,B2),FormulasIn-FormulasOut,TypeIn-TypeOut,CounterIn-CounterOut,CacheIn-CacheOut,FreeVars,PredicatesIn-PredicatesOut,ConsIn-ConsOut) :- %write('huhu '),write(EqType),nl,
      EqType == t, !,
      translationTypedTotalHybrid:translate(A,A2,FormulasIn-FormulasMid,TypeIn-TypeMid,CounterIn-CounterMid,CacheIn-CacheMid,FreeVarsA,formula,PredicatesIn-PredicatesMid,ConsIn-ConsMid),
      translationTypedTotalHybrid:translate(B,B2,FormulasMid-FormulasOut,TypeMid-TypeOut,CounterMid-CounterOut,CacheMid-CacheOut,FreeVarsB,formula,PredicatesMid-PredicatesOut,ConsMid-ConsOut),
      betaConversion:unionNoUnification(FreeVarsA,FreeVarsB,FreeVars).

translateT(((((eq(_), _) @ A, _) @ B),t), A2 = B2, FormulasIn-FormulasOut,TypeIn-TypeOut,CounterIn-CounterOut,CacheIn-CacheOut,FreeVars,PredicatesIn-PredicatesOut,ConsIn-ConsOut) :- !,
      translationTypedTotalHybrid:translate(A,A2,FormulasIn-FormulasMid,TypeIn-TypeMid,CounterIn-CounterMid,CacheIn-CacheMid,FreeVarsA,term,PredicatesIn-PredicatesMid,ConsIn-ConsMid),
      translationTypedTotalHybrid:translate(B,B2,FormulasMid-FormulasOut,TypeMid-TypeOut,CounterMid-CounterOut,CacheMid-CacheOut,FreeVarsB,term,PredicatesMid-PredicatesOut,ConsMid-ConsOut),
      betaConversion:unionNoUnification(FreeVarsA,FreeVarsB,FreeVars). 

translateT((((((Connective, (t > (t > t))) @ A), _)  @ B), t), Result, FormulasIn - FormulasOut, TypeIn-TypeOut, CounterIn-CounterOut,CacheIn-CacheOut, FreeVars, PredicatesIn-PredicatesOut,ConsIn-ConsOut) :- atom(Connective),
      !,
      translationTypedTotalHybrid:translate(A, A2, FormulasIn-FormulasMid, TypeIn-TypeMid, CounterIn-CounterMid, CacheIn-CacheMid, FreeVarsA, formula, PredicatesIn-PredicatesMid,ConsIn-ConsMid),
      translationTypedTotalHybrid:translate(B, B2, FormulasMid-FormulasOut, TypeMid-TypeOut, CounterMid-CounterOut, CacheMid-CacheOut, FreeVarsB, formula, PredicatesMid-PredicatesOut,ConsMid-ConsOut),
      betaConversion:unionNoUnification(FreeVarsA, FreeVarsB, FreeVars),
      Result =.. [Connective, A2,B2].

translateT((((Connective, (t > t)) @ A), t), Result, FormulasIn - FormulasOut, TypeIn-TypeOut, CounterIn-CounterOut,CacheIn-CacheOut, FreeVars, PredicatesIn-PredicatesOut,ConsIn-ConsOut) :-
      atom(Connective),
      translationTypedTotalHybrid:translate(A, A2, FormulasIn-FormulasOut, TypeIn-TypeOut, CounterIn-CounterOut, CacheIn-CacheOut, FreeVars, formula, PredicatesIn-PredicatesOut,ConsIn-ConsOut),
      Result =.. [Connective, A2].

%Ordinary Quantifiers
translateT(((Q,((QType > t) > t)) @ (lam((X,QType),B),(QType > t)), t), Result, FormulasIn-FormulasOut, TypeIn-TypeOut, CounterIn-CounterOut,CacheIn-CacheOut,FreeVariables, PredicatesIn-PredicatesOut,ConsIn-ConsOut) :-
      translationTypedTotalHybrid:translate(B,B2, FormulasIn-FormulasOut,TypeIn-TypeOut,CounterIn-CounterOut,CacheIn-CacheOut,FreeVariablesIn, formula, PredicatesIn-PredicatesOut,ConsIn-ConsOut),
      betaConversion:deleteNoUnification(FreeVariablesIn, (X, QType), FreeVariables, single),
      foTranslation:translateType(QType, QTypeT),
      Q =.. [QName, QType],
      ((QName = all, Connective = imp); (QName = some, Connective = and)),
      Formula =.. [Connective,has_type(X,QTypeT), B2],
      Result =.. [QName, X, Formula].

% Ordinary Quantifiers without Lambda
translateT(((Q,((QType > t) > t)) @ B, t), Result, FormulasIn-FormulasOut, TypeIn-TypeOut, CounterIn-CounterOut,CacheIn-CacheOut,FreeVars, PredicatesIn-PredicatesOut,ConsIn-ConsOut) :-
      Q =.. [QName, QType],
      translationTypedTotalHybrid:translate(B, B2, FormulasIn-FormulasOut, TypeIn-TypeOut, CounterIn-CounterOut, CacheIn-CacheOut,FreeVars, term, PredicatesIn-PredicatesOut,ConsIn-ConsOut),
      foTranslation:translateType(QType, QTypeT),
      Result =.. [QName,X,imp(has_type(X,QTypeT), f(B2, X) istrue)].

% Function Application
translateT(((A @ B), t), f(A2,B2) istrue, FormulasIn-FormulasOut, TypeIn-TypeOut,CounterIn-CounterOut,CacheIn-CacheOut,FreeVars, PredicatesIn-PredicatesOut,ConsIn-ConsOut) :-
      translationTypedTotalHybrid:translate(A,A2,FormulasIn-FormulasMid, TypeIn-TypeMid, CounterIn-CounterMid, CacheIn-CacheMid, FreeVarsA, term, PredicatesIn-PredicatesMid,ConsIn-ConsMid),
      translationTypedTotalHybrid:translate(B,B2,FormulasMid-FormulasOut, TypeMid-TypeOut,CounterMid-CounterOut,CacheMid-CacheOut,FreeVarsB,term,PredicatesMid-PredicatesOut,ConsMid-ConsOut),
      betaConversion:unionNoUnification(FreeVarsA,FreeVarsB,FreeVars).






translateT(A, B,C,D,E,F,G,H,I) :-
      write('translateT '),
      write(translateT(A, B,C,D,E,F,G,H,I)),nl,nl,
      (translateT(A, fail, Form - Form, TypeState - TypeState, Counter-Counter, TermCache-TermCache, [],P-P) = translateT(A, B,C,D,E,F,G,H,I)).

/*===================================*/


translateTForPredicateWithArguments((Predicate, PredicateType), Formulas-Formulas, Type-Type, Counter-Counter, Cache-Cache, [], [], (Predicate, PredicateType), Predicates-Predicates) :-
      atom(Predicate).

translateTForPredicateWithArguments(((Func @ Arg), _), FormulasIn - FormulasOut, TypeIn-TypeOut, CounterIn-CounterOut,CacheIn-CacheOut, FreeVars, [Arg2|Result], PredicateWithItsType, PredicatesIn-PredicatesOut) :-
      translateTForPredicateWithArguments(Func, FormulasIn-FormulasMid, TypeIn-TypeMid, CounterIn-CounterMid, CacheIn-CacheMid, FreeVarsA, Result, PredicateWithItsType, PredicatesIn-PredicatesMid),
      translate(Arg, Arg2, FormulasMid-FormulasOut,TypeMid-TypeOut,CounterMid-CounterOut,CacheMid-CacheOut,FreeVarsB, term, PredicatesMid-PredicatesOut),
      betaConversion:unionNoUnification(FreeVarsA, FreeVarsB, FreeVars).
translateTForPredicateWithArguments(A,B,C,D,E,F,G,H,I) :-
      write(translateTForPredicateWithArguments(A,B,C,D,E,F,G,H,I)),nl,fail.

/*=====================================*/









