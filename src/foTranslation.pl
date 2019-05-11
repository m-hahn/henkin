/*************************************************************************

    File: foTranslation.pl
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


:- module(foTranslation,[translate/3, translate/2, translateWithAxioms/2, translate/6,projectToTermComponent/2,translateParametrizedTy2Constant/3]).

:- [translationTypedTotal, translationTypedTotalHybrid, combinators, translationTypedTotalAxioms].

/*===========================================
    Modulate the Strength of the Translation
============================================*/

translationStrategy(hybrid,weak).


/*===========================================
    High-Level Predicates for Translation
============================================*/

translate(Term,Formula) :-
      translate(Term,Formula,_).

translateWithAxioms(Term, Formula) :-
      translate(Term,BareFormula,Constants),!,
      translationStrategy(_,PostulatesStrategy),
      addPostulates(BareFormula,Constants,Formula,PostulatesStrategy).

addPostulates(BareFormula,Constants,Formula,weak) :-
      addPostulates([(sig,[1]),(axiom,[1]),lingax(Constants),constAxiom(Constants)],BareFormula,Formula).
addPostulates(BareFormula,Constants,Formula,medium) :-
      addPostulates([(sig,[1]),(axiom,[1]),lingax(Constants),constAxiom(any)],BareFormula,Formula).
addPostulates(BareFormula,Constants,Formula,strong) :-
      addPostulates([(sig,[1]),(axiom,[1]),lingax(any),constAxiom(any)],BareFormula,Formula).
addPostulates(BareFormula,Constants,Formula,hyperstrong) :-
      addPostulates([(sig,[0,1]),(axiom,[0,1]),lingax(any),constAxiom(any)],BareFormula,Formula).

translate(Term, Formula,Constants) :-
      translationStrategy(Strategy,_),
      translate(Strategy,Term, Matrix, Conds, TypeStatements,Constants),
      buildFormula(Matrix, Conds, FormulaWithConditions),
      Formula = imp(TypeStatements, FormulaWithConditions).

translate(basic,A,B,C,D,E) :-
      translateBasic(A,B,C,D,E).
translate(hybrid,A,B,C,D,E) :-
      translateHybrid(A,B,C,D,E).
/*translate(combHybrid,A,B,C,D,E) :-
      translateCombHybrid(A,B,C,D,E).*/
translate(comb,A,B,C,D,E) :-
      translateCombBasic(A,B,C,D,E).

buildFormula(Matrix,Conds, FormulaResult) :-
      buildConditions(Conds, Matrix, FormulaResult).


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

% does not add linguistic axioms!
addPostulates(Bare,Formula) :-
      addPostulates([sig,axiom],Bare,Formula).


/*===========================================
    Adding Axioms
============================================*/

addPostulates([],Formula,Formula).
addPostulates([Pred|T],In,Result) :-
      addPostulate(In,Out,Pred),
      addPostulates(T,Out,Result).

addPostulate(Bare,Formula,constAxiom(any)) :- !,
      addAllConstantAxioms(Bare,Formula).
addPostulate(Bare,Formula,constAxiom(Constants)) :- !,
      addConstantAxioms(Bare,Formula,Constants).
addPostulate(Bare,Formula,lingax(any)) :- !,
      addAllLinguisticAxioms(Bare,Formula).
addPostulate(Bare,Formula,lingax(Constants)) :- !,
      addLinguisticAxioms(Bare,Formula,Constants).
addPostulate(Bare,Formula,(Predicate,Values)) :-
      Literal =.. [Predicate,Value,B],
      L = (Literal, member(Value,Values)),
      findall(B,L,List),
      buildFormulaWithPreconditions(List,Bare,Formula).

addAllConstantAxioms(Bare,Formula) :-
     L = constAxiom(_,Ax),
     findall(Ax,L,List),
     buildFormulaWithPreconditions(List,Bare,Formula).

addConstantAxioms(Bare,Formula,Constants) :-
     L = (constAxiom(Cons,Ax),subset(Cons,Constants)),
     findall(Ax,L,List),
     buildFormulaWithPreconditions(List,Bare,Formula).

addAllLinguisticAxioms(Bare,Formula) :-
     L = lingax(_,Ax,Matrix),
     findall((Ax,Matrix),L,List),
     buildFormulaWithPreconditionsWithMatrixParameter(List,Bare,Formula).

addLinguisticAxioms(Bare,Formula,Constants) :-
     L = (lingax(Cons,Ax,Matrix),subset(Cons,Constants)),
     findall((Ax,Matrix),L,List),
     buildFormulaWithPreconditionsWithMatrixParameter(List,Bare,Formula).

buildFormulaWithPreconditionsWithMatrixParameter([],Formula,Formula).
buildFormulaWithPreconditionsWithMatrixParameter([(Ax,Matrix)|T],Matrix,Result) :-
     buildFormulaWithPreconditionsWithMatrixParameter(T,Ax,Result).

buildFormulaWithPreconditions([],Formula,Formula).
buildFormulaWithPreconditions([Cond|T], Formula, FormulaResult) :-
      buildFormulaWithPreconditions(T, imp(Cond, Formula), FormulaResult).


/*===============================================
     Auxiliary Predicates
================================================*/

translateType(T,T) :- var(T), !.
translateType('s','s') :- !.
translateType(t,t) :- !.
translateType(e,e) :- !.
translateType((A > B), f(A2,B2)) :-
      translateType(A,A2),
      translateType(B,B2).

projectToTermComponent([],[]).
projectToTermComponent([(A,_)|C], [A|D]) :-
      projectToTermComponent(C,D).

findTerm([(Name,Term, FreeVars)|_], HOTerm, Name, FreeVars) :-
    (Term =@= HOTerm),
    !.
findTerm([_|Tail], Term, Name, FreeVars) :-
    findTerm(Tail, Term, Name, FreeVars).

createConstant(C, I, J, Args) :-
      J is I + 1,
      length(Args,Length),
      atom_concat(c,Length,CName),
      C =.. [CName,I|Args].

translateParametrizedTy2Constant((eq(Type), Type > (Type > t)), eq(TypeR), has_type(eq(TypeR), f(TypeR,f(TypeR,t)))) :- !,
     foTranslation:translateType(Type,TypeR).
translateParametrizedTy2Constant((Term, (ArgType > t) > ((ArgType > t) > t)), TermResu, has_type(TermResu, f(f(ArgTypeR,t),f(f(ArgTypeR,t),t)))) :-
     Term =.. [Q,ArgType,g], !,
     TermResu =.. [Q,ArgTypeR],
     foTranslation:translateType(ArgType,ArgTypeR).
translateParametrizedTy2Constant((Term, Type), TermResu, has_type(TermResu, TypeResu)) :- %trace,
     Term =.. [Q|ArgTypes], !,
     translateTypesList(ArgTypes,ArgTypesR),
     TermResu =.. [Q|ArgTypesR],
     translateType(Type,TypeResu).

translateTypesList([],[]).
translateTypesList([A|T],[A2|T2]) :-
     translateType(A,A2),translateTypesList(T,T2).

/*===========================================
     higher-order axioms
=============================================*/

transformAxiom(HO,Result,FreeTypeVariables,Matrix) :-
    betaConversion:completeTyping(HO,HO2),betaConversion:unifyTypes(HO2),
    translationTypedTotalHybrid:translate(HO2, FOTerm, [] - Conds, ((true = true) - TypeStatements), 0 - _, [] - _, _, formula, []-Predicates,[]-Constants),
    buildFormula(imp(FOTerm,Matrix), Conds, FormulaWithConditions),!,
    Result = imp(TypeStatements, FormulaWithConditions),
    !.

:- [linguisticAxioms].

:- retractall(lingax(_,_,_)).
:- \+ (lingaxHO(Constants,FreeTypeVariables,HO,_), \+((transformAxiom(HO,Result,FreeTypeVariables,Matrix),asserta(lingax(Constants,Result,Matrix))))).


