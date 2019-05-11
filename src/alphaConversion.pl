/*************************************************************************

    File: alphaConversion.pl
    Copyright (C) 2004,2005,2006 Patrick Blackburn & Johan Bos
    Modified by Michael Hahn (2015).

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de

    It is adapted from the file alphaConversion.pl of BB1, version 1.3
    by Patrick Blackburn & Johan Bos. This file does NOT have the same
    functionality as the B&B file of the same name, it does alpha
    conversion in Ty2.

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with BB1; if not, write to the Free Software Foundation, Inc., 
    59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

*************************************************************************/





:- module(alphaConversion,[alphaConvert/2,
                           alphabeticVariants/2]).

:- use_module(comsemPredicates,[compose/3,
				memberList/2]).


/*========================================================================
   Alpha Conversion (introducing substitutions)
========================================================================*/

alphaConvert(F1,F2):-
   alphaConvert(F1,F2,[]).

alphaConvert((Term, Type), (Term2, Type),Bindings) :-
       var(Term),!, replaceVariable(Term,Term2,Bindings).
alphaConvert((lam((Var,Type), Term), LType), (lam((Var2, Type), Term2), LType), Bindings) :-
       alphaConvert(Term, Term2, [s(Var,Var2)|Bindings]).
alphaConvert((@(Term1,Term2),Type), (@(Term1b,Term2b), Type), Bindings) :-
      alphaConvert(Term1,Term1b, Bindings),
      alphaConvert(Term2, Term2b, Bindings).
alphaConvert((Term, Type), (Term1, Type), _) :-
      atom(Term), Term = Term1.
alphaConvert((Term,Type), (Term,Type), _) :-
     betaConversion:isTy2Constant((Term,Type)), !.
alphaConvert(A,B, C) :-
     print(alphaConvert(A,B, C)), nl, fail.

replaceVariable(Term,Term,[]).
replaceVariable(Var, Var2, [s(Var1, Var2)|_]) :-
      Var == Var1.
replaceVariable(Var, Resu, [_|T]) :-
      replaceVariable(Var, Resu, T).



/*========================================================================
   Alpha Conversion (listwise)
========================================================================*/

alphaConvertList([],_,Free-Free,[]).

alphaConvertList([X|L1],Sub,Free1-Free3,[Y|L2]):-
   alphaConvert(X,Sub,Free1-Free2,Y),
   alphaConvertList(L1,Sub,Free2-Free3,L2).


/*========================================================================
   Alphabetic Variants
========================================================================*/

alphabeticVariants(Term1,Term2):-
   alphaConvert(Term1,[],[]-Free1,Term3),
   alphaConvert(Term2,[],[]-Free2,Term4),
   Free1==Free2,
   numbervars(Free1,0,N),
   numbervars(Term3,N,M),
   numbervars(Term4,N,M),
   Term3=Term4.
