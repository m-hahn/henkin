/*************************************************************************

    File: combinators.pl
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
   Combinatorial translation (not described in the paper) 
*/

/*===========================================
          Combinators
=============================================*/

:- module(combinators,[translateCombBasic/5]).

:- op(500,xfx,@).

k((k(S,T),S > (T > S)),S,T).
i((i(T), T > T),T > T).
s((sc(X,Y,Z),((X > (Y > Z)) > ((X > Y) > (X > Z)))), X, Y, Z).


translateCombBasic(Term, FOTerm, Conds, TypeStatements,Constants) :-
      lambdaToCombinatorialForm(Term,CombTerm),
      foTranslation:translate(basic,CombTerm,FOTerm,Conds,TypeStatements,Constants).

lambdaToCombinatorialForm((X,Type),(X,Type)) :-
      var(X),!.
lambdaToCombinatorialForm((A @ B, Type),(A2 @ B2,Type)) :-
      lambdaToCombinatorialForm(A,A2),
      lambdaToCombinatorialForm(B,B2),!.
lambdaToCombinatorialForm((lam(X,A),Type),(K @ A2,Type)) :-
      Type = (ArgType > _),
      A = (_,AType),
      k(K,AType,ArgType),
      X = (XVar,_),
      \+ \+ unify_with_occurs_check(XVar,A),!,
      lambdaToCombinatorialForm(A,A2),!.
lambdaToCombinatorialForm((lam(X,Y),Type),I) :- 
      X == Y,!,
      i(I,Type).
lambdaToCombinatorialForm((lam(X,(lam(Y,A),Type1)),Type2), Result) :-
      lambdaToCombinatorialForm((lam(Y,A),Type1), InnerResult),
      lambdaToCombinatorialForm((lam(X,InnerResult),Type2),Result),!.
lambdaToCombinatorialForm((lam(X,(A1 @ A2, _)),Type),((S @ Result1, _) @ Result2, Type)) :-
      A1 = (_, A1Type),
      A2 = (_, A2Type),
      Type = (XType > ResuType),
      s(S,XType,A2Type,ResuType),
      lambdaToCombinatorialForm((lam(X,A1),XType > A1Type), Result1),
      lambdaToCombinatorialForm((lam(X,A2),XType > A2Type), Result2),!.
lambdaToCombinatorialForm(A,A).

removeTypesFromCombinatorialTerm((X,_),X) :-
       var(X),!.
removeTypesFromCombinatorialTerm((sc(_,_,_),_),sc) :- !.
removeTypesFromCombinatorialTerm((i(_),_),i) :- !.
removeTypesFromCombinatorialTerm((k(_,_),_),k) :- !.
removeTypesFromCombinatorialTerm((A @ B, _), (A2 @ B2)) :-
       removeTypesFromCombinatorialTerm(A,A2),
       removeTypesFromCombinatorialTerm(B,B2),!.
removeTypesFromCombinatorialTerm((A,_),A).

exchangeApplicationFunctor(X,X) :- var(X),!.
exchangeApplicationFunctor(A @ B, f(A2,B2)) :- exchangeApplicationFunctor(A,A2),exchangeApplicationFunctor(B,B2),!.
exchangeApplicationFunctor(A,A).



