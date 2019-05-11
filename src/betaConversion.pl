/*************************************************************************

    File: betaConversion.pl
    Copyright (C) 2004,2005,2006 Patrick Blackburn & Johan Bos
    Modified by Michael Hahn (2015).

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de

    It is adapted from the file betaConversion.pl of BB1, version 1.3
    by Patrick Blackburn & Johan Bos. This file does NOT have the
    functionality of the original B&B file of the same name, it is used
    for beta-conversion in Ty2.

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


:- module(betaConversion,[info/0,type/2,completeTyping/2,
                          infix/0,
                          prefix/0, 
                          betaConvertTestSuite/0,
			  betaConvert/2,
                          betaConvert2/2,
                          syntaxCheck/1]).

:- use_module(comsemPredicates,[infix/0,
                                prefix/0,
                                compose/3]).

:- use_module(alphaConversion,[alphaConvert/2,
                               alphabeticVariants/2]).

:- use_module(betaConversionTestSuite,[expression/2]).





/*========================================================================
   Beta-Conversion
========================================================================*/




:- op(700,xfx,@).

syntaxCheck((Term,_)) :-
    (atom(Term) ; var(Term)), !.
syntaxCheck((((Func, FuncType) @ (Arg,ArgType)),Type)) :-
    FuncType = (ArgType > Type),
    syntaxCheck((Func,FuncType)),
    syntaxCheck((Arg,ArgType)), !.
syntaxCheck((lam((Var,VarType),(Body,BodyType)),(VarType > BodyType))) :-
    var(Var),
    syntaxCheck((Body,BodyType)), !.
syntaxCheck((Term,Type)) :-
    isTy2Constant((Term,Type)).
syntaxCheck(Term) :-
    write('syntaxCheck: '),write(Term),nl,fail.

preTranslate(Term,Term) :-
    (var(Term);atom(Term); isTy2Constant((Term,_))), !.
preTranslate(A @ B, A2 @ B2) :-
   preTranslate(A,A2),
   preTranslate(B,B2).
preTranslate(app(A,B), A2 @ B2) :-
   preTranslate(A,A2),
   preTranslate(B, B2).
preTranslate(lam(A,B), lam(A,B2)) :-
   preTranslate(B,B2).
preTranslate(A,A) :-
   write('preTranslate '),write(A),nl.

type(Term,(Term,_)) :-
    (var(Term);atom(Term)), !.
type(A @ B, ((A2 @ B2),Type)) :-
    A2 = (_,(TypeB > Type)),
    type(A, A2),
    B2 = (_, TypeB),
    type(B, B2).
type(lam(Var,Term), (lam(Var2,Term2), Type)) :-
    Var2 = (Var, TypeVar),
    Term2 = (_, TypeTerm),
    Type = (TypeVar > TypeTerm),
    type(Term, Term2).
type(Term,(Term,Type)) :-
    isTy2Constant((Term,Type)).
type(A,A) :-
    write('type '),write(A),nl.

instantiateTypes((Term,Type)) :-
     (var(Term);atom(Term)),!,
     instantiateType(Type).
instantiateTypes((lam(A,B),_)) :- !,
     instantiateTypes(A),
     instantiateTypes(B).
instantiateTypes((A @ B, _)) :- !,
     instantiateTypes(A),
     instantiateTypes(B).
instantiateTypes((A,T)) :-
     isTy2Constant((A,T)),!,
     instantiateType(T).
instantiateTypes(F) :-
     print(instantiateTypes(F)),nl,fail.

instantiateType(Type) :-
     var(Type), !, Type = t.
instantiateType(A > B) :- !,
     instantiateType(A),
     instantiateType(B).
instantiateType(_) :- true.

completeAndUnifyTypes(Term,Typed) :-
    completeTyping(Term,Typed),
    unifyTypes(Typed),!.

completeTyping(Term,(Term,_)) :-
    (var(Term)
     ), !.
completeTyping(A @ B, ((A2 @ B2),Type)) :- %trace,
    A2 = (_,(TypeB > Type)),
    completeTyping(A, A2),
    B2 = (_, TypeB),
    completeTyping(B, B2).
completeTyping(lam(Var,Term), (lam(Var2,Term2), Type)) :- %trace,
    Var2 = (_, TypeVar),
    completeTyping(Var,Var2),
    Term2 = (_, TypeTerm),
    Type = (TypeVar > TypeTerm),
    completeTyping(Term, Term2).
completeTyping((Term,Type), (Term2, Type)) :- %trace,
    completeTyping(Term, (Term2, Type)).
completeTyping(Term,(Term,Type)) :- %trace,
    isTy2Constant((Term,Type)), !.
completeTyping(A,(fail,Type)) :- %trace,
    write(completeTyping(A,(_,Type))),nl,fail.

unifyTypes(T) :-
    unifyTypes(T,[],[]-_).

unifyTypes((Term,Type),Bindings,ConstantsTypes-ConstantsTypes) :-
    var(Term),!,
    findType(Bindings,Term,Type).
unifyTypes((Term, Type), _, ConstantsTypesIn-ConstantsTypesOut) :-
    atom(Term),!, findConstantTypeAndAddIfNecessary(ConstantsTypesIn,ConstantsTypesOut,Term,Type).
unifyTypes(((A @ B), _), Bindings, CIn-COut) :-
    unifyTypes(A, Bindings,CIn-CMid),
    unifyTypes(B, Bindings,CMid-COut),!.
unifyTypes((lam((Var,Type),Term),_), Bindings,Cs) :-
    unifyTypes(Term, [Var:Type|Bindings], Cs),!.
unifyTypes((Term,Type), _, C-C) :-
    isTy2Constant((Term,Type)).
unifyTypes(A,B, C) :-
    write(unifyTypes(A,B, C)),nl,fail.

findConstantTypeAndAddIfNecessary([],[Term:Type],Term,Type).
findConstantTypeAndAddIfNecessary([Term:Type|Tail], [Term:Type|Tail],Term, Type2) :- !,
    Type = Type2.
findConstantTypeAndAddIfNecessary([A|T],[A|T2], Term,Type) :-
    findConstantTypeAndAddIfNecessary(T,T2,Term,Type).

findType([], _, _).
findType([Var:Type|_], Var2, Type2) :-
    Var == Var2,!, Type = Type2.
findType([_|T], V, T2) :-
    findType(T, V, T2).

    

/*========================================================================
   Beta-Conversion (core stuff)
========================================================================*/

betaConvert(A0,B) :-
     %A = A0,
     alphaConvert(A0,A),
     betaConvert2(A,C),!,
     ((A = C,!,A=B); betaConvert(C,B)).

betaConvert(A,A) :-
     write('beta '),write(A),nl.

betaConvert2((Term,Type),(Term2,Type)) :-
      var(Term), !, Term = Term2.
betaConvert2((((Func, FuncType) @ Arg), AppType), ((Functor2 @ Arg2), AppType)) :-
        var(Func),!,
        betaConvert2((Func, FuncType), (Functor2)),
        betaConvert2(Arg, Arg2).
betaConvert2((((lam(Variable,Term),_) @ Argument),_),Result) :- !,
       Variable = Argument, betaConvert2(Term,Result),!.
betaConvert2(((A @ B),AppType),((A2 @ B2),AppType)) :-
       betaConvert2(A,A2),
       betaConvert2(B,B2),!.
betaConvert2((lam(A,B),LamType),(lam(A,B2),LamType)) :-
       betaConvert2(B,B2),!.
betaConvert2((Term,Type),(Term2,Type)) :-
       atom(Term),Term=Term2,!.
betaConvert2((Term,Type),(Term,Type)) :-
       isTy2Constant((Term,Type)).
betaConvert2(X,('failure',Type)) :-
       write(betaConvert2(X,('failure',Type))), fail.
     
substituteVariable((Term, Type), (Term2, Type), (Variable, Type), (Argument, Type)) :-
       Term == Variable,!,
       Term2 = Argument.
substituteVariable((Term, Type), (Term, Type), _, _) :-
       var(Term), !.
substituteVariable((A @ B, Type), (A2 @ B2, Type), Var, Arg) :-
       substituteVariable(A, A2, Var, Arg),
       substituteVariable(B, B2, Var, Arg).
substituteVariable((lam(LamVar, Term), Type), (lam(LamVar, Term2), Type), Var, Arg) :-
       substituteVariable(Term, Term2, Var, Arg).
substituteVariable((Term,Type),(Term, Type),_,_) :-
       isTy2Constant((Term,Type)).
substituteVariable(A,B,C,D) :-
       write('sub: '),write(A),nl,write(B),nl,write(C),nl,write(D),nl,nl.





/*========================================================================
   Beta-Convert a list
========================================================================*/

betaConvertList([],[]).

betaConvertList([Formula|Others],[Result|ResultOthers]):-
   betaConvert(Formula,Result,[]),
   betaConvertList(Others,ResultOthers).

/*========================================================================
     Auxiliary Predicates
========================================================================*/

findFreeVariables((Var,_),FreeVars-FreeVarsR,BoundVars) :-
      var(Var),
    (((memberNoUnification(Var,BoundVars); memberNoUnification(Var,FreeVars)),
      FreeVars = FreeVarsR) ; 
     (FreeVarsR = [Var|FreeVars])).
findFreeVariables(((A @ B),_), FV-FVR, BV) :-
     findFreeVariables(A,FV-FV2,BV),
     findFreeVariables(B,FV2-FVR,BV).
findFreeVariables((lam((Var,_),Term),_), FV-FVR, BV) :-
     findFreeVariables(Term, FV-FVR, [Var|BV]).
findFreeVariables((Term,_), FV-FV, _) :-
     atom(Term).
findFreeVariables(X,FV-FV,_) :-
     write('findFreeVariables/3 '),write(X),nl,nl.

memberNoUnification(_,[]) :- !,fail.
memberNoUnification(X,[Y|_]) :-
     X == Y.
memberNoUnification(X,[_|T]) :-
     memberNoUnification(X,T).

% 'noUnification' only refers to elements in the first two arguments
unionNoUnification([], A, A) :- !.
unionNoUnification([A|C], B, D) :-
     memberNoUnification(A,B), !,
     unionNoUnification(C,B,D).
unionNoUnification([A|B], C, [A|D]) :-
     unionNoUnification(B,C,D).

deleteNoUnification(A,B,C) :-
     deleteNoUnification(A,B,C,multiple).
deleteNoUnification([], _, [],_) :- !.
deleteNoUnification([A|B], A2, C, Mode) :- A == A2, !,
        ((Mode = multiple,deleteNoUnification(B, A2, C)); (Mode = single, C = B)).
deleteNoUnification([A|B], C, [A|D], Mode) :-
	deleteNoUnification(B, C, D, Mode).


isTy2Constant((and, t > (t > t))) :- !.
isTy2Constant((or, t > (t > t))) :- !.
isTy2Constant((imp, t > (t > t))) :- !.
isTy2Constant((not, t > t)) :- !.
isTy2Constant((iff, t > (t > t))) :- !.
isTy2Constant((Term,_)) :-
    atom(Term), !.
isTy2Constant(T) :-
     isParametrizedTy2Constant(T).

isParametrizedTy2Constant((i(_),_)).
isParametrizedTy2Constant((k(_,_), _)).
isParametrizedTy2Constant((sc(X,Y,Z),((X > (Y > Z)) > ((X > Y) > (X > Z))))).
isParametrizedTy2Constant((iota(X),(X > t) > X)).
isParametrizedTy2Constant((eq(Type), Type > (Type > t))) :- !.
isParametrizedTy2Constant((Term,((ArgType > t) > t))) :-
    Term =.. [_,ArgType], !.
isParametrizedTy2Constant((Term,(ArgType > t) > ((ArgType > t) > t))) :-
    Term =.. [Functor,ArgType,g],
    !.



/*========================================================================
   Prove all formulas from the test suite
========================================================================*/

betaConvertTestSuite:-
   format('~n>>>>> BETA CONVERSION ON TEST SUITE <<<<<~n',[]), 
   expression(Expression,Expected),
   format('~n~nExpression: ~p~nExpected: ~p',[Expression,Expected]),
   betaConvert(Expression,Converted,[]),
   format('~nConverted: ~p',[Converted]),
   compareResults(Expected,Converted,Result),
   format('~nResult: ~p',[Result]),
   fail.

betaConvertTestSuite.


/*========================================================================
   Compare Results of the Test Suite
========================================================================*/

compareResults(A,B,Result):-
    (
     alphabeticVariants(A,B),
     !,
     Result=ok
    ;
     Result=error
    ).


/*========================================================================
   Info
========================================================================*/

info:-
   format('~n> ------------------------------------------------------------------- <',[]),
   format('~n> betaConversion.pl, by Patrick Blackburn and Johan Bos               <',[]),
   format('~n>                                                                     <',[]),
   format('~n> ?- betaConvert(F,C).         - beta-convert a formula               <',[]),
   format('~n> ?- betaConvertTestSuite.     - run the test suite                   <',[]),
   format('~n> ?- infix.                    - switches to infix display mode       <',[]),
   format('~n> ?- prefix.                   - switches to prefix display mode      <',[]),
   format('~n> ?- info.                     - shows this information               <',[]),
   format('~n> ------------------------------------------------------------------- <',[]),
   format('~n~n',[]).


/*========================================================================
   Display info at start
========================================================================*/

:- info.
