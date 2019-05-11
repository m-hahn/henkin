/*************************************************************************

    File: translationTypedTotal.pl
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

/*
 'basic' translation; not described in the paper
*/

:- module(translationTypedTotal, [translateBasic/5]).

:- op(500,xfx,@).


/*======================================
   Composing FO formula
=======================================*/

translateBasic(Term, istrue(FOTerm), Conds, TypeStatements,Constants) :-
     translate(Term, FOTerm, [] - Conds, ((true = true) - TypeStatements), 0 - _, [] - Cache, FreeVars,[]-Constants).




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
    (8) constants
*/
translate((Var,VarType), Var, Form - Form, TypeState-TypeState, Counter-Counter, TermCache-TermCache, [(Var,VarType)],Constants-Constants) :-
      var(Var), !.
translate(((A @ B), _), f(A2, B2), Formulas - Formulas3, TypeStateIn - TypeStateOut, CounterIn - CounterOut, TermCacheIn-TermCacheOut, FreeVars, ConstantsIn-ConstantsOut) :-
      translate(A,A2,Formulas - Formulas2, TypeStateIn - TypeState2, CounterIn - CounterMid, TermCacheIn-TermCacheMid, FreeVarsA,ConstantsIn-ConstantsMid),
      translate(B,B2,Formulas2 - Formulas3, TypeState2 - TypeStateOut, CounterMid - CounterOut, TermCacheMid-TermCacheOut, FreeVarsB,ConstantsMid-ConstantsOut),
      betaConversion:unionNoUnification(FreeVarsA, FreeVarsB, FreeVars).


translate(HOTerm, TermName, DefinitionsIn - DefinitionsOut, TypeStateIn - TypeStateOut, CounterIn - CounterOut, TermCacheIn - TermCacheOut, FreeVariables,ConstantsIn-ConstantsOut) :-
      HOTerm = (lam((Var,TypeOfVar),Term),LambdaType),!,
     % take term from cache
     (
      %(findTerm(TermCacheIn, HOTerm, TermName, FreeVariables), !, TermCacheOut = TermCacheIn, TypeStateOut = TypeStateIn, DefinitionsOut = DefinitionsIn,ConstantsIn=ConstantsOut);

      % translate lambda expression with function term and a defining equation
      (
       translate(Term, TermTrans, [Defi|DefinitionsIn]-DefinitionsOut, TypeStateIn - TypeStateMid, CounterIn - CounterMid, TermCacheIn - TermCacheMid, FreeVariablesIn,ConstantsIn-ConstantsOut),
       % Updated Bookkeeping lists
       betaConversion:deleteNoUnification(FreeVariablesIn, (Var, TypeOfVar), FreeVariables, single),
       %Term = (_, TypeOfTerm),
       TermCacheOut = [(TermName, HOTerm, FreeVariablesIn)|TermCacheMid],
       TypeStateOut = TypeStateMid,

       % create term with defining equation
       foTranslation:translateType(TypeOfVar, TypeOfVarR),
       foTranslation:projectToTermComponent(FreeVariables, Arguments),
       foTranslation:createConstant(TermName, CounterMid, CounterOut, Arguments),
       Defi = (TermName,(Var, TypeOfVarR), TermTrans = f(TermName,Var), LambdaType, FreeVariables)
      )).

translate(Term, Result, Form - Form, TypeState - and(TypeStatement,TypeState), Counter - Counter, TermCache-TermCache, [], ConsIn-[Term|ConsIn]) :-
      betaConversion:isParametrizedTy2Constant(Term),!,
      foTranslation:translateParametrizedTy2Constant(Term, Result, TypeStatement),!.

translate((Atom, Type), Atom, Form - Form, TypeStatements - and(has_type(Atom, TypeR), TypeStatements), Counter-Counter, TermCache-TermCache, [], ConstantsIn-[(Atom,Type)|ConstantsIn]) :-
      atom(Atom),
      foTranslation:translateType(Type,TypeR).
translate(A, B,C,D,E,F,G,H) :-
      write('translate '),
      write(translate(A, B,C,D,E,F,G,H)),nl,nl,
      (translate(A, fail, Form - Form, TypeState - TypeState, Counter-Counter, TermCache-TermCache, [],Cons-Cons) = translate(A, B,C,D,E,F,G,H)).








