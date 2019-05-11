/*************************************************************************

    File: HOI.pl
    Copyright (C) 2015 Michael Hahn

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de

    This file is adapted from the file lambda.pl of BB1,
    version 1.3, Copyright (C) 2004,2005,2006 Patrick Blackburn & Johan Bos

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




:- module(hoi,[info/0,
                  infix/0,
                  prefix/0,
                  lambdaHOI/0,
                  lambdaHOI/2,
                  lambdaHOITestSuite/0]).

:- op(500, xfx, @).

:- use_module(readLine,[readLine/1]).

:- use_module(comsemPredicates,[infix/0,
                                prefix/0,
                                printRepresentations/1,
				compose/3]).

:- use_module(betaConversion,[betaConvert/2]).

:- use_module(hoInferenceTestSuite,[testItemFO/5]).

:- [englishGrammar].

:- [englishLexicon].

:- [semLexHOI].

:- [semRulesHOI].

:- [foTranslation].

:- [callInference].

:- use_module(hoInferenceTestSuite,sentence/3).





/*========================================================================
   Driver Predicates
========================================================================*/

lambdaHOI :-
	readLine(Sentence),
        lambdaHOI(Sentence,Sems),
	printRepresentations(Sems).

lambdaHOI(Sentence,Sems):-
	setof(Sem,(t([sem:Sem],Sentence,[])),Sems).

lambdaHOIList([],[]).
lambdaHOIList([S|T],[S2|T2]) :-
        lambdaHOI(S,S2),
        lambdaHOIList(T,T2).



lambdaHOI2FO(Sentence,Sems) :-
       lambdaHOI(Sentence,HOs),
       translateList(HOs,Sems,translate).

lambdaHOI2FOPlusAxioms(Sentence,Sems) :-
       lambdaHOI(Sentence,HOs),
       translateList(HOs,Sems,translateWithAxioms).

translateList([],[],_).
translateList([A|T],[A2|T2],Pred) :-
       Call =.. [Pred, A, A2],
       Call,
       translateList(T,T2,Pred).


/*========================================================================
   Test Suite Predicates
========================================================================*/

lambdaHOITestSuite:-
	nl, write('>>>>> LAMBDA ON SENTENCE TEST SUITE <<<<< '), nl,
        hoInferenceTestSuite:sentence(Num,_,Sentence,_),
        nl, write('Sentence: '), write(Num), write(' '),write(Sentence),
	lambdaHOI(Sentence,Formulas),
	printRepresentations(Formulas),
        fail.

lambdaHOTestSuite.


higherOrderNaturalLangugeTestSuite :-
     forall(testItemFO(A,C,D-E,HO,FO),callTPOnFO(FO,_,_,[])).

testInferenceFormula(A) :-
     betaConversion:completeAndUnifyTypes(A,HO),betaConversion:instantiateTypes(HO),translateWithAxioms(HO,FO),callTPOnFO(FO,P,E,[timeout:10]).

testInferenceSentence(A) :-
     callTPOnSentence(A,P,E,[timeout:10]).



buildImplicationTerm([],Hyp,Hyp).
buildImplicationTerm([[A|_]|T],Hyp,(((imp, t>(t>t)) @ A, t>t) @ Resu, t)) :-
      buildImplicationTerm(T,Hyp,Resu).


/* Creates input files for the provers and model builders in tpinput, where
   they can be called by perl scripts testTP.perl and testMB.perl.
   Requires both hoInferenceTestSuite.pl and fracas.pl */
initTheoremProversOnTestsuite :-
     forall(testItemFO(B,C,D-E,HO,FO-NegFO),initTheoremProversOnItem(own,B,C,FO,NegFO)),
     forall(fracasTestItemFO(A,B,C,D-E,HO,FO-NegFO),initTheoremProversOnItem(fracas,B,C,FO,NegFO)).

initTheoremProversOnItem(A,B,C,FO,NegFO) :-
    initTheoremProversOnItem2(A,B,C,FO,pos),
    initTheoremProversOnItem2(A,B,C,NegFO,neg).

initTheoremProversOnItem2(A,B,C,FO,Pol) :-
    concat_atom([A,'-',B,'-',C,'-',Pol],Info),
    fo2bb(FO,FO2),
    initTheoremProvers(FO2,Info).

/*======================================================================
   Call theorem provers
=======================================================================*/

callTPOnSentence(Sentence, Proof, Engine,Parameters) :-
   lambdaHOI(Sentence, [Sem|_]),
   translateWithAxioms(Sem, FO),
   callTPOnFO(FO, Proof, Engine,Parameters).

callTPOnFOPlusAxioms(Formula, Proof, Engine) :-
    addPostulates([sig,axiom,lingax],Formula,Enriched),
    callTPOnFO(Enriched,Proof,Engine,Parameters).

callTPOnFO(Formula, Proof, Engine,Parameters) :-
    fo2bb(Formula,F2),!,
    callTP(F2,Proof,Engine,Parameters).

/*=======================================================================
     Convert FO formulas from our format to the BB1 format
=======================================================================*/

fo2bb(X,Y) :-
   fo2bb(X,Y,formula).

fo2bb(X,X, term) :-
    var(X),!.
fo2bb(A = B, eq(A2,B2), formula) :-
    fo2bb(A,A2, term),fo2bb(B,B2, term).
fo2bb(fi(A,B),imp(B2,A2),formula) :-
    fo2bb(A,A2),fo2bb(B,B2).
fo2bb(iff(A,B),and(imp(A2,B2),imp(B2,A2)), formula) :-
    fo2bb(A,A2, formula), fo2bb(B,B2, formula).
fo2bb(Form, Resu, formula) :-
    Form =.. [exactlyOne,Arg1,Arg2,Arg3],
    fo2bb(Arg1,Arg1b, formula),
    fo2bb(Arg2,Arg2b, formula),
    fo2bb(Arg3,Arg3b, formula),
    Resu = or(or(and(Arg1b,not(or(Arg2b,Arg3b))), and(Arg2b, not(or(Arg1b,Arg3b)))), and(Arg3b, not(or(Arg1b,Arg2b)))).
fo2bb(Atom,Atom, _) :-
    atomic(Atom).
fo2bb(Form,Resu, _) :-
    Form =.. [Func|Args],
    fo2bbList(Args,ArgsB),
    Resu =.. [Func|ArgsB].
fo2bb(Form, Resu, _) :-
    Form =.. [Func,Arg],
    Resu =.. [Func,ArgB],
    fo2bb(Arg,ArgB, _).
fo2bb(A,fail, Type) :-
    write(fo2bb(A,fail, Type)),nl.

fo2bbList([],[]).
fo2bbList([A|T],[A2|T2]) :-
    fo2bb(A,A2,_),
    fo2bbList(T,T2).

/*=======================================================================
     LaTeX
========================================================================*/
% Mode = strict(total) [with all types], strict(partial) [no types for complex terms], short [no types]
%StrucMode = ho (curried), fo (uncurried + primitive quantifiers)
ho2Latex(Term,Mode) :-
    ho2Latex(Term,Mode,ho).
ho2Latex(Term,Mode,StrucMode) :-
    current_stream(1,write,S),
    ho2Latex(Term,S,Mode,StrucMode),!.
ho2LatexFile(Term,File,Mode,StrucMode) :-
    open(File,write,Stream),
    ho2Latex(Term,Stream,Mode,StrucMode),
    close(Stream),!.

getVariables(Term, Variables) :-
    getVariables(Term, [(x,[]), (w,[]), (f,[]), ('P',[])],Variables2,[],_), % note that there are multiple lines where the available letters are hard-coded
    postProcessVariables(Variables2, [], Variables).

postProcessVariables([], V, V).
postProcessVariables([(Kind,Vars)|VariablesStructure], Var2Print, Var2PrintR) :-
    reverse(Vars,Vars2),
    processVarsFromKind(Kind, Vars2, Var2Print, Var2Print2, n, 0),
    postProcessVariables(VariablesStructure, Var2Print2, Var2PrintR).

% Kind, Nums, Var2PrintIn, Var2PrintOut, HasFoundVar, Counter
processVarsFromKind(_, [], Vars,Vars,_,_).
processVarsFromKind(Kind, [Num], Var2Print, [(Num,Kind)|Var2Print],n,_).
processVarsFromKind(Kind, [Num|NumT], Var2Print, Var2PrintR, _, Index) :-
    Index2 is Index+1,
    atomic_list_concat([Kind,'^',Index2],Print),
    processVarsFromKind(Kind, NumT, [(Num, Print)|Var2Print], Var2PrintR, y, Index2).


addToVariablesStore(Kind, VarNum, [(Kind,List)|T], [(Kind,[VarNum|List ])|T]).
addToVariablesStore(Kind, VarNum, [A|T], [A|R]) :-
    addToVariablesStore(Kind, VarNum, T, R).
addToVariablesStore(A, B, C, D) :- print(addToVariablesStore(A, B, C, D)),nl.

getVariables(('$VAR'(VarNum), Type), Vars, Vars, Cache, Cache) :-
    member(VarNum, Cache).
getVariables(('$VAR'(VarNum), Type), Vars, VarsBack,Cache, [VarNum|Cache]) :-
    member((Type,Kind),[(e,x), (s, 'w'), ((_>e), f ), (_, 'P')]), % note that there are multiple lines where the available letters are hard-coded
    addToVariablesStore(Kind, VarNum, Vars, VarsBack).
getVariables((A @ B, _), Vars, VarsR, C, CR) :-
    getVariables(A, Vars, Vars2, C, C2),
    getVariables(B, Vars2, VarsR, C2, CR).
getVariables((lam(A,B),_), Vars, VarsR, C, CR) :-
    getVariables(A, Vars, Vars2, C, C2),
    getVariables(B, Vars2, VarsR, C2, CR).
getVariables(_,Vars,Vars,C,C) :- !.
getVariables(A,B,C,D,E) :- write(getVariables(A,B,C,D,E)).


ho2Latex2VariableName('$VAR'(VarNum), Type, VariableName, Vars) :-
    member((VarNum, VariableName), Vars).


ho2Latex(Term,Stream,Mode,SMode) :-
    copy_term(Term,Term2), 
    numbervars(Term,0,_),
    getVariables(Term, Variables),
    ho2Latex2(Term,Stream,Mode,SMode, Variables).

ho2Latex2(('$VAR'(VarNum),Type),Stream,Mode,_, Variables) :-
    ho2Latex2VariableName('$VAR'(VarNum), Type, VariableName, Variables),
    write(Stream,VariableName),
    type2Latex(Type,TypeLatex),
    ((Mode = strict(_),write(Stream,'_'),write(Stream,TypeLatex)); (Mode = short)).

ho2Latex2((lam(X,A),Type),Stream,Mode,SMode, Variables) :-
    write(Stream,'(\\lambda '),
    ho2Latex2(X,Stream,Mode,SMode, Variables),write(Stream,' '),
    ho2Latex2(A,Stream,Mode,SMode, Variables),
    type2Latex(Type,TypeLatex),
    write(Stream,')'),
    ((Mode = strict(total), write(Stream,'_'),write(Stream,TypeLatex)); (Mode = short; Mode = strict(partial))).

ho2Latex2(((Not, _) @ (((Eq, Type>(Type>t)) @ A, _) @ B, t), t), Stream, short, SMode,  Variables) :-
    Not == not,
    Eq == eq(Type),\+(Type = t),
    ho2Latex2(A, Stream, short, SMode, Variables),
    write(' \\not\\equiv '),
    ho2Latex2(B,Stream, short, SMode, Variables).

ho2Latex2(((Functor,t>t) @ B,t),Stream,short,SMode, Variables) :-
    Functor == not,
    write(Stream,'\\neg '),
    ho2Latex2(B,Stream,short,SMode, Variables).

ho2Latex2((((Quantifier,Type2) @ (lam((Var,VarType),A),Type3)), Type4), Stream, Mode, fo, Variables) :- 
    member((Quantifier, QuantifierTranslation), [(all(_), '\\forall'), (some(_), '\\exists')]),
    write(Stream, QuantifierTranslation),  write(Stream, ' '),
    ho2Latex2VariableName(Var,VarType, VarName, Variables), 
    write(Stream, VarName), 
    writeType(Stream,VarType), 
    write(Stream, ' '), 
    ho2Latex2(A,Stream,Mode,fo, Variables).

ho2Latex2((((Functor,t>(t>t)) @ A, _) @ B, t), Stream,short,SMode, Variables) :-
    betaConversion:memberNoUnification(Functor,[and,or,iff,imp]),!,
    write(Stream,'('),
    ho2Latex2(A,Stream,short,SMode, Variables),
    write(Stream,' '),
    connective2Latex(Functor,FunctorLatex),
    write(Stream,FunctorLatex),
    write(Stream,' '),
    ho2Latex2(B,Stream,short,SMode, Variables),
    write(Stream,')').

ho2Latex2((((Eq, Type>(Type>t)) @ A, _) @ B, t), Stream, short, SMode, Variables) :-
    Eq == eq(Type),
    ho2Latex2(A, Stream, short, SMode, Variables),
    ((Type = t, write(Stream,' \\leftrightarrow '));
    (write(' \\equiv '))),
    ho2Latex2(B,Stream, short, SMode, Variables).



ho2Latex2((A @ B, Type), Stream,Mode,fo, Variables) :-
    getArgumentList(A, [B], Functor, Arguments),
    printFunctorArgument(Functor, Arguments, Stream, Mode, fo, Variables).

printFunctorArgument(Functor, Arguments, Stream, Mode, fo, Variables) :-
    ho2Latex2(Functor,Stream,Mode,fo, Variables),write('('),
    printArguments(Arguments, Stream, Mode, fo, Variables),write(')').

getArgumentList(('$VAR'(VarNum),Type), Args, ('$VAR'(VarNum),Type), Args) :- !.
getArgumentList((A @ B, _), Args, Functor, ArgsR) :- !,
    getArgumentList(A, [B|Args], Functor, ArgsR).
getArgumentList((Functor,Type), Args, (Functor,Type), Args).

printArguments([], Stream, Mode, fo, Variables).
printArguments([Arg|ArgT], Stream, Mode, fo, Variables) :-
      ho2Latex2(Arg, Stream, Mode, fo, Variables), ((ArgT = [], !); (write(', '))),
      printArguments(ArgT,Stream, Mode, fo, Variables).

ho2Latex2((A @ B, Type), Stream,Mode,SMode, Variables) :-
    write(Stream,'('),
    ho2Latex2(A,Stream,Mode,SMode, Variables),
    write(Stream,'\\ '),
    ho2Latex2(B,Stream,Mode,SMode, Variables),
    write(Stream,')'),
    type2Latex(Type,TypeLatex),
    ((Mode = strict(total), write(Stream,'_'),write(Stream,TypeLatex)); (Mode = short); (Mode = strict(partial))).

ho2Latex2((A,Type),Stream,Mode,SMode, _) :-
    A =.. [Functor,Parameter|_],
    type2Latex(Type,TypeLatex),
    functor2Latex(Functor,FunctorLatex),
    write(Stream,FunctorLatex),
    write(Stream,'^{'),
    type2Latex(Parameter,ParameterLatex),
    write(Stream,ParameterLatex),
    write(Stream,'}'),
    ((Mode = strict(_),write(Stream,'_'),write(Stream,TypeLatex)); (Mode = short)).

ho2Latex2((Functor,_),Stream,short,SMode,_) :-
    member(Functor,[and,or,imp,iff,not,all,some,k,i,sc]),
    write(Stream,Functor).

ho2Latex2((Functor,Type),Stream,Mode,SMode,_) :-
    write(Stream,'\\textit{'),write(Stream,Functor),write(Stream,'}'),
    writeType(Stream,Type,Mode,atom).

writeType(_,_,short,_).
writeType(Stream,Type, strict(_), atom) :-
    writeType(Stream,Type).
writeType(Stream,Type) :-
    type2Latex(Type,TypeLatex),
    write(Stream,'_'),
    write(Stream,TypeLatex).

ho2Latex2(A,Stream,Mode,SMode, Variables) :-
    write(ho2Latex2(A,Stream,Mode,SMode, Variables)).





functor2Latex(all,'\\forall') :- !.
functor2Latex(some,'\\exists') :- !.
functor2Latex(iota,'\\iota') :- !.
functor2Latex(A,A).

connective2Latex(and,'\\wedge').
connective2Latex(imp,'\\rightarrow').
connective2Latex(or,'\\vee').
connective2Latex(iff,'\\leftrightarrow').

type2Latex('$VAR'(VarNum),Trans) :- !,
    atomic_list_concat(['{\\sigma_',VarNum,'} '],Trans).
type2Latex(A > B, Trans) :- !,
    type2Latex(A,A2),type2Latex(B,B2),
    atomic_list_concat(['{\\langle ',A2,B2,' \\rangle} '],Trans).
type2Latex(A,A2) :-
    atomic_list_concat(['',A,''],A2).

/*========================================================================
   Info
========================================================================*/

info:-
   format('~n> ------------------------------------------------------------------ <',[]),
   format('~n> HOI.pl,                                                            <',[]),
   format('~n>                                                                    <',[]),
   format('~n> ?- lambdaHOI.              - parse a typed-in sentence             <',[]),
   format('~n> ?- lambdaHOI(S,F).         - parse a sentence and return formula   <',[]),
   format('~n> ?- lambdaHOITestSuite.     - run the test suite                    <',[]),
   format('~n> ?- info.                - shows this information                   <',[]),
   format('~n> ------------------------------------------------------------------ <',[]),
   format('~n~n',[]).


/*========================================================================
   Display info at start
========================================================================*/

:- info.
