/*************************************************************************

    File: hoInferenceTestSuite.pl
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

:- module( hoInferenceTestSuite,[sentence/4, testItemFO/5]).

:- op(500,xfx,@).

/*========================================================================
   Make sure names are unique.
========================================================================*/

checkWhetherThereAreItemsWithTheSameName :-
      sentence(A,B,C,D), 
      sentence(A,E,F,G), 
      \+((B,C,D) = (E,F,G)),
      !, 
      write('Warning: two test items with the same number '),write((A,B,C,D)),nl,write((A,D,E,F)),nl.
checkWhetherThereAreItemsWithTheSameName.




/*========================================================================
   Process a test item and generate its first-order translation
========================================================================*/


testItemFO(A,C,D-E,HO,FO-FONeg) :-
      sentence(A,D,E,C),
      hoi:lambdaHOI(E,[Hyp|_]),
      hoi:lambdaHOIList(D,Prem),
      hoi:buildImplicationTerm(Prem,Hyp,HO),
      hoi:buildImplicationTerm(Prem,(@((not,t>t),Hyp),t),HONeg),
      betaConversion:instantiateTypes(HO),
      betaConversion:instantiateTypes(HONeg),
      hoi:translateWithAxioms(HO,FO),
      hoi:translateWithAxioms(HONeg,FONeg).


/*========================================================================
   The testsuite
========================================================================*/

section(0,99,'FO').
section(100,199,'Modality').
section(200,299,'Knowledge and Belief').
section(300,399,'Generalized Quantifiers').
section(400,499,'Modifiers').
section(500,599,'De dicto').


sentence(1,[],[mia,dances,and,does,not,dance],contradictory).
sentence(0,[[mia,dances,and,does,not,dance]],[mia,dances],valid).
sentence(2,[],[every,man,dances,or,does,not,dance],valid).
sentence(3,[[mia,is,a,woman],[mia,dances]],[a,woman,dances],valid).
sentence(4,[[mia,is,a,robber]],[mia,is,a,man],contingent).
sentence(5,[[mia,is,a,woman],[every,woman,dances]],[mia,dances],valid).

% MODALITY

sentence(100,[[mia,dances]],[mia,possibly,dances],valid).
sentence(101,[[mia,dances]],[mia,necessarily,dances],contingent).
sentence(102,[[mia,is,a,robber]],[mia,allegedly,is,a,robber],contingent).

sentence(103,[[mia,necessarily,dances]],[mia,dances],valid).
sentence(104,[[mia,possibly,dances]],[mia,dances],contingent).
sentence(105,[[mia,allegedly,is,a,robber]],[mia,is,a,robber],contingent).

sentence(106,[[mia,necessarily,dances]],[mia,possibly,dances],valid).
sentence(107,[[mia,possibly,dances]],[mia,necessarily,dances],contingent).

sentence(108,[[mia,does,not,possibly,dance]],[mia,necessarily,does,not,dance],valid).
sentence(109,[[mia,does,not,dance]],[mia,does,not,necessarily,dance],valid).
sentence(110,[[mia,does,not,possibly,dance]],[mia,does,not,dance],valid).
sentence(111,[],[mia,dances,or,does,not,necessarily,dance],valid).
sentence(112,[[mia,is,an,alleged,robber]],[mia,allegedly,is,a,robber],valid).
sentence(113,[[mia,necessarily,is,a,robber]],[mia,allegedly,is,a,robber],contingent).
sentence(114,[[mia,allegedly,is,a,robber]],[mia,possibly,is,a,robber],contingent).




% KNOWLEDGE AND BELIEF

% Deductivity
%sentence(200,[[mia,thinks,that,john,dances],[mia,thinks,that,if,john,dances,then,john,plays,air,guitar]],[mia,thinks,that,john,plays,air,guitar],valid).


% Deductivity + Logical omniscience
sentence(200,[[mia,thinks,that,john,necessarily,dances]],[mia,thinks,that,john,dances],valid).
sentence(201,[[john,thinks,that,mia,knows,that,vincent,dances]],[john,thinks,that,vincent,dances],valid).
sentence(202,[[john,thinks,that,mia,eats,several,burgers]],[john,thinks,that,mia,eats,a,burger],valid).
sentence(203,[[john,thinks,that,mia,is,a,tall,woman]],[john,thinks,that,mia,is,a,woman],valid).
sentence(204,[[john,thinks,that,mia,is,an,alleged,robber]],[john,thinks,that,mia,is,a,robber],contingent).


% Veracity of Knowledge
sentence(206,[[john,knows,that,mia,dances]],[mia,dances],valid).
sentence(207,[[john,thinks,that,mia,dances]],[mia,dances],contingent).
sentence(208,[[mia,necessarily,knows,that,mia,dances]],[mia,necessarily,dances],valid).



% Intensional Context
sentence(209,[[mia,knows,that,john,dances],[john,is,the,chairman]],[mia,knows,that,the,chairman,dances],contingent).
sentence(210,[[mia,knows,that,john,saw,a,unicorn]],[some,unicorn,is,a,unicorn],valid).
sentence(211,[[mia,thinks,that,john,saw,a,unicorn]],[some,unicorn,is,a,unicorn],contingent).





% GENERALIZED QUANTIFIERS

%Definition of MANY, FEW
sentence(300, [[few,women,dance]],[many,women,dance],contradictory).
sentence(301,[[no,women,dance]],[few,women,dance],valid).
sentence(302,[[no,women,dance]],[many,women,dance],contradictory).
sentence(303,[[few,women,dance]],[no,women,dance],contingent).
sentence(304,[[many,women,dance]],[all,women,dance],contingent).
sentence(305,[[all,women,dance]],[many,women,dance],contingent).

%Definition of MOST
sentence(306,[[mia,eats,every,burger],[mia,eats,a,burger]],[mia,eats,most,burger],valid).
sentence(307,[[every,man,dances],[a,man,dances]],[most,man,dances],valid).
sentence(308,[[mia,eats,a,burger]],[mia,eats,most,burger],contingent).
sentence(309,[[mia,eats,most,burgers]],[mia,eats,all,burgers],contingent).

%Definition of ONLY, THE, ...
sentence(310,[[only,men,dance],[no,woman,is,a,man]],[no,woman,dances],valid).
sentence(311,[[john,is,a,man],[every,man,dances]],[the,man,dances],valid).
sentence(312,[[at,least,three,women,dance]],[at,most,two,women,dance],contradictory).



%Conservativity
sentence(313,[[the,man,dances],[john,is,a,man]],[a,man,dances], valid).
sentence(314,[[many,women,dance]],[some,women,dance],valid).
sentence(315,[[few,women,dance]],[some,women,dance],contingent).
sentence(316,[[several,women,dance]],[some,women,dance],valid).
sentence(317,[[most,women,dance]],[some,women,dance],valid).
sentence(318,[[at,least,three,women,dance]],[some,women,dance],valid).
sentence(319,[[at,most,two,women,dance]],[some,women,dance],contingent).

% Monotonicity: upward on the second argument [used propositional monotonicity to isolate the property of the quantifier]
sentence(320,[[the,man,dances,and,plays,air,guitar]],[the,man,dances],valid).
sentence(321,[[many,men,dance,and,play,air,guitar]],[many,men,dance],valid).
sentence(322,[[few,men,dance,and,play,air,guitar]],[few,men,dance],contingent).
sentence(323,[[several,men,dance,and,play,air,guitar]],[several,men,dance],valid).
sentence(324,[[most,men,dance,and,play,air,guitar]],[most,men,dance],valid).
sentence(325,[[at,least,three,men,dance,and,play,air,guitar]],[at,least,three,men,dance],valid).
sentence(326,[[at,most,two,men,dance,and,play,air,guitar]],[at,most,two,men,dance],contingent).

% Monotonicity: downward on the second argument
sentence(327,[[the,man,dances]],[the,man,dances,and,plays,air,guitar],contingent).
sentence(328,[[many,men,dance]],[many,men,dance,and,play,air,guitar],contingent).
sentence(329,[[few,men,dance]],[few,men,dance,and,play,air,guitar],valid).
sentence(330,[[several,men,dance]],[several,men,dance,and,play,air,guitar],contingent).
sentence(331,[[most,men,dance]],[most,men,dance,and,play,air,guitar],contingent).
sentence(332,[[at,least,three,men,dance]],[at,least,three,men,dance,and,play,air,guitar],contingent).
sentence(333,[[at,most,two,men,dance]],[at,most,two,men,dance,and,play,air,guitar],valid).

% Monotonicity: upward on the first argument
sentence(334,[[the,tall,man,dances]],[the,man,dances],contingent).
sentence(335,[[many,tall,men,dance]],[many,men,dance],valid). % NAJA
sentence(336,[[few,tall,men,dance]],[few,men,dance],contingent).
sentence(337,[[several,tall,men,dance]],[several,men,dance],valid).
sentence(338,[[most,tall,men,dance]],[most,men,dance],contingent).
sentence(339,[[at,least,three,tall,men,dance]],[at,least,three,men,dance],valid).
sentence(340,[[at,most,two,tall,men,dance]],[at,most,two,men,dance],contingent).

% Monotonicity: downward on first argument
sentence(341,[[the,man,dances]],[the,tall,man,dances],contingent).
sentence(342,[[many,men,dance]],[many,tall,men,dance],contingent).
sentence(343,[[few,men,dance]],[few,tall,men,dance],valid).
sentence(344,[[several,men,dance]],[several,tall,men,dance],contingent).
sentence(345,[[most,men,dance]],[most,tall,men,dance],contingent).
sentence(346,[[at,least,three,men,dance]],[at,least,three,tall,men,dance],contingent).
sentence(347,[[at,most,three,men,dance]],[at,most,three,tall,men,dance],valid).





% MODIFIERS

% INTERSECTIVE
sentence(400,[[mia,is,a,tall,woman]],[mia,is,a,woman],valid).
sentence(401,[[mia,is,tall],[mia,is,a,woman]],[mia,is,a,tall,woman],valid).
sentence(402,[[mia,is,a,tall,woman],[mia,is,a,robber]],[mia,is,a,tall,robber],valid).

% SUBSECTIVE
sentence(403,[[mia,has,a,genuine,diamond]],[mia,has,a,diamond],valid).
sentence(404,[[mia,is,a,skillful,robber],[mia,is,a,boxer]],[mia,is,a,skillful,boxer],contingent).

% FAKE
sentence(405,[[excalibur,is,a,fake,sword]],[excalibur,is,a,sword],contradictory).
sentence(406,[],[no,fake,sword,is,a,sword],valid).
sentence(407,[[excalibur,is,a,weapon],[excalibur,is,a,fake,sword]],[excalibur,is,a,fake,weapon],contradictory).

% MODAL
sentence(408,[[mia,is,an,alleged,robber]],[mia,is,a,robber],contingent).
sentence(409,[[mia,is,an,alleged,robber],[mia,is,a,boxer]],[mia,is,an,alleged,boxer],contingent).

% DE-DICTO

sentence(500,[[mia,seeks,a,unicorn]],[some,unicorn,is,a,unicorn],contingent).
sentence(501,[[mia,sees,a,unicorn]],[some,unicorn,is,a,unicorn],valid).



/*========================================================================
   Printing the testsuite
========================================================================*/

printTestSuite :-
   findall((A,B-C,D),sentence(A,B,C,D),List),
   printTestSuite(List,ours,implicit).
printFracasTestSuite :-
   findall((B,D,C),fracasTestItem(_,B,C,D,_),List),
   sort(List,List2),
   printTestSuite(List2,fracas,implicit).

printTestSuite([],_,_).
printTestSuite([(Number,Premises-Hyp,Status)|T],Format,Mode) :-
    writeNumberInFormat(Number,Format,Mode),writeSentences(Premises),
    member((Status,Symb),[(valid,' $\\vdash$ '),(contingent, ' $\\nvdash$ '),(contradictory, ' $\\vdash$ NON')]),
    write(Symb),
    writeSentence(Hyp),
    finalComment(Number,Format,Mode),
    nl,
    printTestSuite(T,Format,Mode).

finalComment(Number,_,implicit) :- !,write(' % '),write(Number).
finalComment(_,_,_).

writeNumberInFormat(Number,fracas,explicit) :-
     write('\\ex (F'),write(Number),write(') ').
writeNumberInFormat(Number,fracas,implicit) :-
    write('\\setcounter{enumi}{'),Number2 is Number-1, write(Number2),write('}'),write('\\ex ').
writeNumberInFormat(Number,ours,implicit) :- write('\\ex ').
writeNumberInFormat(Number,ours,explicit) :-
     atom_chars(Number,Digits),
     split(Digits,Section,Example),
     write('\\ex ('),write(Section),write(.),write(Example),write(') ').

split([A,B,C],A,BC) :- atom_chars(BC,[B,C]).
split([A],0,A0) :- atom_chars(A0,['0',A]).
split(A,B,C) :-
    write(A,B,C).

writeSentences([]).
writeSentences([A|T]) :-
    writeSentence(A),
    writeSentences(T).

writeSentence(A) :- writeSentence(A,start).
writeSentence([],_) :-
    write('. ').
writeSentence([A|T],Pos) :-
    write(' '),capitalizeIfNecessary(A,A2,Pos),write(A2),
    writeSentence(T,other).

capitalizeIfNecessary(A,A2,start) :- !,capitalize(A,A2).
capitalizeIfNecessary(A,A2,_) :- member(A,[mia,john,scandinavian,british,irish,excalibur,micky,dumbo,fido,kim]),!,capitalize(A,A2).
capitalizeIfNecessary(A,A,_).

capitalize(A,A2) :-
    atom_chars(A,[First|Rest]),
    upcase_atom(First,FirstCap),
    atom_chars(A2,[FirstCap|Rest]).

:- checkWhetherThereAreItemsWithTheSameName.
