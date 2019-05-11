/*************************************************************************

    File: foResolutionInteractive.pl
    Copyright (C) 2004,2005,2006 Patrick Blackburn & Johan Bos
    Modified by Michael Hahn (2015).

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de

    It is adapted from the file foResolution.pl of BB1, version 1.3
    by Patrick Blackburn & Johan Bos.

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

:- module(foResolutionInteractive,[
                        rproveInteractive/1,
                        rproveInteractive/2]).

:- use_module(comsemPredicates,[infix/0,
                                prefix/0,
                                memberList/2,
				appendLists/3,
                                unionSets/3,
				selectFromList/3]).

:- use_module(folTestSuite,[formula/2]).

:- use_module(cnfFOL,[cnf/2]).

:- dynamic(proofLogStream/1).

/*========================================================================
   Main Predicate
========================================================================*/

% Input must be in B&B format (apply mine2BB/2).

rproveInteractive(Formula):-
   openProofLogFile,
   cnf(not(Formula),CNF),
   nonRedundantFactors(CNF,NRF),
   refuteWithInteraction(NRF),closeProofLogFile,!.

rproveInteractive(Formula,Result):-
   openProofLogFile,
   cnf(not(Formula),CNF),
   nonRedundantFactors(CNF,NRF),
   (
      refuteWithInteraction(NRF), !,
      Result = 'theorem'
   ;
      Result = 'not a theorem'
   ),closeProofLogFile,!.

openProofLogFile :-
     open('proofLog.txt', write, Stream),
     retractall(proofLogStream(_)),
     asserta(proofLogStream(Stream)).

closeProofLogFile :-
    proofLogStream(Stream),
    close(Stream).

/*========================================================================
   Refute
========================================================================*/

refuteWithInteraction(C) :-
   addNumbers(C,NumberedClauses,0,Num),!,
   %printClauses(NumberedClauses),!,
   refuteInteractive(NumberedClauses,Num).
refuteWithInteraction(_) :-
   write('Error!'),nl.

addNumbers([],[],A,A).
addNumbers([A|T],[(Num,A)|T2],Num,Max) :-
   Num2 is Num+1,
   addNumbers(T,T2,Num2,Max).

printClauses([]).
printClauses([(Num,Clause)|T]) :-
   write(Num),write('  '),write(Clause),nl,
   proofLogStream(Stream),
   write(Stream,Num),write(Stream,'  '),write(Stream,Clause),nl(Stream),
   printClauses(T).

refuteInteractive(C,_) :-
   memberList((_,[]),C),!,
   printClauses(C),
   proofLogStream(Stream),
   write(Stream,'----QED----\n'),
   write('Done.'),nl.

refuteInteractive(C,Num) :-
   write('~~~~\n'),
   proofLogStream(Stream),write(Stream,'~~~~~\n'),
   printClauses(C),
   write('Command '),nl,
   getCommand(Input),
   processResolutionCommand(Input,C,Num).

refuteInteractive(C,Num) :-
   write('Call failed.\n'),
   refuteInteractive(C,Num).

getClause(Num,C1,Clauses) :-
   member((Num,C1),Clauses).
getClause(_,_,_) :-
   write('Could not find clause'),nl,fail.

getCommand(Command) :-
    proofLogStream(Stream),
    read(Command),
    write(Stream,Command),
    nl(Stream).

processResolutionCommand(quit,_,_) :- !.
processResolutionCommand(C1Num-C2Num,C,Num) :-!,
    getClause(C1Num,C1,C),
    getClause(C2Num,C2,C),
    attemptResolution(C1,C2,C,ClausesNew,Num,NumNew),
    refuteInteractive(ClausesNew,NumNew).
    %resolveClausePair(C1,C2,C,Num).
processResolutionCommand(eq(CNum),Clauses,Num) :-!,
    getClause(CNum,C1,Clauses),
    applyEquality(C1,CNew),
    write('Simplified '),write(C1),write(' -> '),write(CNew),nl,
    addClause(Clauses,Num,CNew,ClausesNew,NumNew),
    refuteInteractive(ClausesNew,NumNew).
processResolutionCommand(unit(CNum),C,Num) :-!,
    getClause(CNum,C1,C),
    applyAllUnitClauses(C1,C,NewC),
    write('Simplified '),write(C1),write(' -> '),write(NewC),nl,
    addClause(C,Num,NewC,ClausesNew,NumNew),
    refuteInteractive(ClausesNew,NumNew).
processResolutionCommand(simplify(CNum),C,Num) :-!,
    getClause(CNum,C1,C),
    applyAllUnitClauses(C1,C,NewC1),
    applyEquality(NewC1,NewC),
    write('Simplified '),write(C1),write(' -> '),write(NewC),nl,
    addClause(C,Num,NewC,ClausesNew,NumNew),
    refuteInteractive(ClausesNew,NumNew).
processResolutionCommand(eqsub,Clauses,Num) :-
    print('eqsub(Term1=Term2,Formula,Var)'),nl,
    getCommand(Command),
    processResolutionCommand(Command,Clauses,Num).
processResolutionCommand(rm([CN1,CN2]),Clauses,Num) :-
    removeClauses(CN1,CN2,Clauses,ClausesNew),
    refuteInteractive(ClausesNew,Num).
processResolutionCommand(rm(CNum),Clauses,Num) :-
    removeClause(CNum,Clauses,ClausesNew),
    refuteInteractive(ClausesNew,Num).
processResolutionCommand(rmsym(Symbol),Clauses,Num) :-
    removeSymbol(Symbol,Clauses,ClausesNew),
    refuteInteractive(ClausesNew,Num).

removeSymbol(_,[],[]).
removeSymbol(Symbol,[(_,Clause)|T],T2) :-
    contains_var(Symbol,Clause),!,
    removeSymbol(Symbol,T,T2).
removeSymbol(Symbol,[A|T],[A|T2]) :-
    removeSymbol(Symbol,T,T2).

removeClauses(CN1,CN2,Clauses,Clauses) :-
    CN1 > CN2.
removeClauses(CN1,CN2,Clauses,ClausesR) :-
    removeClause(CN1,Clauses,ClausesMid),
    CN11 is CN1+1,
    removeClauses(CN11,CN2,ClausesMid,ClausesR).

removeClause(_,[],[]) :- write('Warning: clause does not exist'),nl.
removeClause(CNum,[(CNum,_)|T],T).
removeClause(CNum,[A|T],[A|T2]) :-
    removeClause(CNum,T,T2).

processResolutionCommand(add(Clause),Clauses,Num) :-
    addClause(Clauses,Num,Clause,ClausesNew,NumNew),
    refuteInteractive(ClausesNew,NumNew).

processResolutionCommand(eqsub(Term1=Term2,Formula,Var),Clauses,Num) :-
     comsemPredicates:substitute(Term1,Var,Formula,Formula1),
     comsemPredicates:substitute(Term2,Var,Formula,Formula2),
     Clause2 = [not(eq(Term1,Term2)),not(Formula1),Formula2],
     Clause3 = [not(eq(Term1,Term2)),not(Formula2),Formula1],
     addClause(Clauses,Num,Clause2,ClausesMid,NumMid),
     addClause(ClausesMid,NumMid,Clause3,ClausesNew,NumNew),
     refuteInteractive(ClausesNew,NumNew).
processResolutionCommand(removeGroundUnit,Clauses,Num) :-
     removeGroundUnit(Clauses,ClausesNew),
     refuteInteractive(ClausesNew,Num).
processResolutionCommand(clean,Clauses,Num) :-
     cleanUp(Clauses,ClausesNew),
     refuteInteractive(ClausesNew,Num).
processResolutionCommand(res(CNum),Clauses,Num) :-
     getClause(CNum,C1,Clauses),
     resolveWithEveryClause(C1,Clauses,Clauses,ClausesNew,Num,NumNew),
     refuteInteractive(ClausesNew,NumNew).

resolveWithEveryClause(_,[],Clauses,Clauses,Num,Num).
resolveWithEveryClause(C1,[(_,C2)|T],Clauses,ClausesR,Num,NumR) :-
     attemptResolution(C1,C2,Clauses,ClausesNew,Num,NumNew),
     resolveWithEveryClause(C1,T,ClausesNew,ClausesR,NumNew,NumR).
resolveWithEveryClause(A,B,C,D,E,F) :-
     write(resolveWithEveryClause(A,B,C,D,E,F)),nl,fail.


findUnitClauses([],[]).
findUnitClauses([(Num,[L])|T],[(Num,[L])|T2]) :- !,
     findUnitClauses(T,T2).
findUnitClauses([_|T],T2) :-
     findUnitClauses(T,T2).

removeGroundUnit(C,CN) :-
     findUnitClauses(C,Unit),
     removeGroundUnit(Unit,C,CN).

removeGroundUnit(_,[],[]) :- !.
removeGroundUnit(Unit,[(CNum,Clause)|T],Resu) :-
   %write(Clause),write('  ->  '),
   % trace,
     removeGroundUnitFromClause(Unit,Clause,ClauseNew),
     Resu = [(CNum,ClauseNew)|T2],
   %write(ClauseNew),nl,
     removeGroundUnit(Unit,T,T2).

removeGroundUnitFromClause(_,[],[]) :- !.


removeGroundUnitFromClause(Unit,[Literal|T],T2) :-
     ground(Literal),
     %write(Literal),nl,
     (
     (Literal = not(Atom),(\+ \+ member((_,[Atom]),Unit)), !);
     ((\+ Literal = not(_)),( \+ \+ member((_,[not(Literal)]),Unit)),  !)),
     % write('found!'),nl,
     removeGroundUnitFromClause(Unit,T,T2).



removeGroundUnitFromClause(Unit,[Literal|T],[Literal|T2]) :-
     %write('*'),write(Literal),nl,
     removeGroundUnitFromClause(Unit,T,T2).

cleanUp([],[]).
cleanUp([(Num,Clause)|T],Resu) :-
     removeEqualityTautologies(Clause,NewClause,Status),
     ((Status = tautology, Resu = ResuT);
      (Status = shorter, Resu = [(Num,NewClause)|ResuT],
(NewClause = [_|_]; (write('Shorter: '),write(Clause),write(' --> '),write(NewClause)))
     )),
     cleanUp(T,ResuT).

removeEqualityTautologies([],[],shorter).
removeEqualityTautologies([eq(A,B)|T],T,tautology) :-
     A == B.
removeEqualityTautologies([not(eq(A,B))|T],T2,Status) :-
     A == B,
     removeEqualityTautologies(T,T2,Status).
removeEqualityTautologies([A|T],[A|T2],Status) :-
     removeEqualityTautologies(T,T2,Status).

/*processResolutionCommand(eqsub(CNum,Term1=Term2,Formula,Var),Clauses,Num) :-
     comsemPredicates:substitute(Term1,Var,Formula,Formula1),
     comsemPredicates:substitute(Term2,Var,Formula,Formula2),
     Clause2 = [not(eq(Term1,Term2)),not(Formula1),Formula2],
     Clause3 = [not(eq(Term1,Term2)),not(Formula2),Formula1],
     getClause(CNum,Clause1,Clauses),
     attemptResolution(Clause1,Clause2,Clauses,ClausesMid,Num,NumMid),
     attemptResolution(Clause1,CLause3,ClausesMid,ClausesNew,NumMid,NumNew),
     refuteInteractive(ClausesNew,NumNew).*/

processResolutionCommand(simplify,C,Num) :-
    simplifyClauses(C,C,ClausesNew,Num,NumNew),
    refuteInteractive(ClausesNew,NumNew).

attemptResolution(Clause1,Clause2,Clauses,ClausesNew,Num,NumNew) :-
    bagof(ClauseNew,
    resolve(Clause1,Clause2,ClauseNew),%!, %HULLU
    %addClause(Clauses,Num,ClauseNew,ClausesNew,NumNew),
    Bag),
    addAllClauses(Clauses,Bag,ClausesNew,Num,NumNew).
attemptResolution(Clause1,Clause2,Clauses,Clauses,Num,Num) :-
    write('Warning: could not resolve '),write(Clause1),write('   *    '),write(Clause2),nl.

addAllClauses(Clauses,[],Clauses,Num,Num) :- !.
addAllClauses(Clauses,[Clause|T],R,Num,NumR) :-
    addClause(Clauses,Num,Clause,ClausesNew,NumNew),
    addAllClauses(ClausesNew,T,R,NumNew,NumR).

applyEquality(Clause,ClauseNew) :-
    resolve(Clause,[eq(X,X)],ClauseNew),!.
applyEquality(Clause,Clause).

simplifyClauses([],Clauses,Clauses,Num,Num) :- !.
simplifyClauses([(_,Clause)|T],Clauses,Result,Num,NumResu) :-
    applyAllUnitClauses(Clause,Clauses,ClauseMid),
    applyEquality(ClauseMid,ClauseNew),
    (resolve(ClauseMid,[eq(X,X)],ClauseNew);ClauseMid = ClauseNew),
    write('Simplified '),write(Clause),write(' -> '),write(ClauseNew),nl,
    addClause(Clauses,Num,ClauseNew,ClausesNew,NumNew),
    %replaceClause(Clauses,CNum,ClauseNew,ClausesNew),
    %getClause(CNum,ClauseNew,ClausesNew),write(CNum),write(' are same'),nl,
    simplifyClauses(T,ClausesNew,Result,NumNew,NumResu).

%    ((memberList((_,NewC),C),!,NewNum = Num,NewClauseList = C,write('Clause already in set'),nl);
%    (NewNum is Num+1,
%     NewClauseList = [(NewNum,NewC)|C]
%    )),
%   write('~~~~\n'),
%   refuteInteractive(NewClauseList,NewNum).

pocessResolutionCommand(_,_,_) :-
    write('Unknown Command'),nl,fail.

addClause(Clauses,Num,NewClause,Clauses,Num) :-
    memberOnlyLexicalVariant((OtherNum,NewClause),Clauses),!,
    print('Warning: Clause exists: '),write(OtherNum),write('\n').
addClause(Clauses,Num,NewClause,[(Num,NewClause)|Clauses],NewNum) :-
    NewNum is Num+1.

%replaceClause([(CNum,_)|T],CNum,NewClause,[(CNum,NewClause)|T]) :- !.
%replaceClause([A|T],CNum,NewClause,[A|T2]) :-
%    replaceClause(T,CNum,NewClause,T2).

applyAllUnitClauses(C1,[],C1) :- !.
applyAllUnitClauses(C1,[(_,C2)|T],Result) :-
    C2 = [_],write(rESOLVE(C1,C2)),nl,
    resolve(C1,C2,CNew),!,
    applyAllUnitClauses(CNew,T,Result).
applyAllUnitClauses(C1,[_|T],Result) :-
    applyAllUnitClauses(C1,T,Result).
   

resolveClausePair(C1,C2,C,Num) :-
   ((resolve(C1,C2,New));(write('Could not resolve'),nl,fail)),
    ((memberList((OtherNum,New),C),!,NewNum = Num,NewC = C,write('Clause already in set: '),write(OtherNum),nl);
    (NewNum is Num+1,
     NewC = [(NewNum,New)|C]
    )),
   write('~~~~\n'),
   refuteInteractive(NewC,NewNum).


memberOnlyLexicalVariant(A,B) :-
     var(B),!,trace,fail.
memberOnlyLexicalVariant(X,[Y|_]) :-
     X =@= Y,!.
memberOnlyLexicalVariant(X,[_|T]) :-
     memberOnlyLexicalVariant(X,T).


/*========================================================================
   Resolve two clauses
========================================================================*/


resolve(Clause1I,Clause2I,NewClause):-
   copy_term(Clause1I,Clause1), %(mhahn)
   copy_term(Clause2I,Clause2),
   selectFromList(Lit1,Clause1,Temp1),
   selectFromList(not(Lit2),Clause2,Temp2), write([Lit1,Lit2]),nl,
   unify_with_occurs_check(Lit1,Lit2),
   unionSets(Temp1,Temp2,NewClause).

resolve(Clause1I,Clause2I,NewClause):-
   copy_term(Clause1I,Clause1), %(mhahn)
   copy_term(Clause2I,Clause2),
   selectFromList(not(Lit1),Clause1,Temp1),
   selectFromList(Lit2,Clause2,Temp2), write([Lit1,Lit2]),nl,
   unify_with_occurs_check(Lit1,Lit2),
   unionSets(Temp1,Temp2,NewClause).


/*========================================================================
   Compute Non-Redundant Factors for a list of clauses
========================================================================*/

nonRedundantFactors([],[]).

nonRedundantFactors([C1|L1],L4):-
   findall(C2,nonRedFact(C1,C2),L3),
   nonRedundantFactors(L1,L2),
   appendLists(L3,L2,L4).


/*========================================================================
   Compute Non-Redundant Factors for a Clause
========================================================================*/

nonRedFact([],[]).
   
nonRedFact([X|C1],C2):-
   memberList(Y,C1),
   unify_with_occurs_check(X,Y),
   nonRedFact(C1,C2).

nonRedFact([X|C1],[X|C2]):-
   nonRedFact(C1,C2).


/*========================================================================
   Info
========================================================================*/

info:-
   format('~n> -------------------------------------------------------------------- <',[]),
   format('~n> foResolutionInteractive.pl                                           <',[]),
   format('~n>                                                                      <',[]),
   format('~n> ?- rproveInteractive(Formula). - Interactively prove a formula       <',[]),
   format('~n> ?- info.                    - show this information                  <',[]),
   format('~n> -------------------------------------------------------------------- <',[]),
   format('~n~n',[]).


/*========================================================================
   Display info at start
========================================================================*/

:- info.

