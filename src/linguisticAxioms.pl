/*************************************************************************

    File: linguisticAxioms.pl
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

:- op(500,xfx,@).


/*========================================================================
    Meaning postulates
========================================================================*/



% Intersective adjectives
lingaxHO([(Symbol,_)],[],(some(s>(e>t)) @ lam(P,all(s) @ lam(W, all(s>(e>t)) @ lam(Q,all(e) @ lam(X, (iff @ ((((Symbol, s> ((s> ((e)>t))> ((e)>t))) @ W) @ Q) @ X)) @ ((and @ ((P @ W) @ X)) @ ((Q @ W) @ X))))))),'Intersective adjectives: \\textit{blue, tall, scandinavian, irish, british, female, male, fat}') :- member(Symbol, [blue,tall,scandinavian,irish,british,female,male,fat]).

% Subsective, not intersective adjectives
lingaxHO([(Symbol,_)],[],(all(s> ((e)>t)) @ lam(P,(all(e) @ lam(X,all(s) @ lam(W,(imp @ (((( Symbol,s> ((s> ((e)>t))> ((e)>t))) @ W) @ P) @ X)) @ ( ((P @ W) @ X))))))), 'Subsective, non-intersective adjectives: \\textit{genuine, skillful, successful, interesting, large, small}') :- member(Symbol, [genuine,skillful,successful, interesting,large,small]).

% Privative adjectives
lingaxHO([(Symbol,_)],[],(all(s> ((e)>t)) @ lam(P,(all(e) @ lam(X,all(s) @ lam(W,(imp @ (((( Symbol,s> ((s> ((e)>t))> ((e)>t))) @ W) @ P) @ X)) @ (not @ ((P @ W) @ X))))))), 'Privative adjectives: \\textit{fake, former}') :- member(Symbol, [fake,former]).

% Modal adjectives
lingaxHO([(alleged,_),(allegedly,_)],[],all(_) @ lam(P, all(e) @ lam(X, all(s) @ lam(W,
(iff @ (((alleged @ W) @ P) @ X)) @ 
(((allegedly,s > ((s > t) > t)) @ W) @ (lam(W2,(P @ W2) @ X)))
))), '\\textit{alleged}').

lingaxHO([(necessarily,_)],[],all(s) @ lam(W,all(s > t) @ lam(P, (
((iff @ ((necessarily @ W) @ P)) @
(all(s) @ lam(W2,(P @ W2))))
))), '\\textit{necessarily}').

lingaxHO([(possibly,_)],[],all(s) @ lam(W,all(s > t) @ lam(P, (
((iff @ ((possibly @ W) @ P)) @
(some(s) @ lam(W2,(P @ W2))))
))), '\\textit{possibly}').

% Quantifiers
lingaxHO([(two(_,g),_)],[],all(Type > t) @ lam(P,all(Type > t) @ lam(Q,(((iff @ ((two(Type,g) @ P) @ Q)) @ (some(Type) @ lam(X1, some(Type) @ lam(X2, (and @ (not @ ((eq(e) @ X1) @ X2))) @ ((and @ (P @ X1)) @ (P @ X2))))))))), '\\textit{two}') :-
      Type = e.


lingaxHO([(at_most_two(e,g),_)],[],
all(e > t) @ lam(P,all(e>t) @ lam(Q,
(iff @ ((at_most_two(e,g) @ P) @ Q)) @
(some(e) @ lam(X1, some(e) @ lam(X2,
all(e) @ lam(Y, ((imp @ (not @ ((eq(e) @ Y) @ X1))) @ ((imp @ (not @ ((eq(e) @ Y) @ X2))) @ (not @ ((and @ (P @ Y)) @ (Q @ Y)))))))))))
,'\\textit{at-most-two}').

lingaxHO([(at_least_three(e,g),_)],[],
all(e>t) @ lam(P,all(e>t) @ lam(Q,

((iff @ ((at_least_three(e,g) @ P) @ Q)) @

(some(e) @ lam(X1,some(e) @ lam(X2,some(e) @ lam(X3,

(and @ ((and @ ((and @ ((and @ ((and @ ((and @ ((and @ ((and @ (not @ ((eq(e) @ X1) @ X2))) @ (not @ ((eq(e) @ X1) @ X3)))) @ (not @ ((eq(e) @ X2) @ X3)))) @ (P @ X1))) @ (Q @ X1))) @ (P @ X2))) @ (Q @ X2))) @ (P @ X3))) @ (Q @ X3)

))))))),'\\textit{at-least-three}').

% 'most'
lingaxHO([(most(_,g),_)],[],all(Type > t) @ lam(P,all(Type > t) @ lam(Q,(((iff @ ((most(Type,g) @ P) @ Q))
               @ (all(Type > Type) @ lam(F,
                                         % F(P \cap CQ) \subseteq P \cap Q
                                         ((imp @ (all(Type) @ lam(Y,(imp @ ((and @ (P @ Y)) @ (not @ (Q @ Y)))) @ ((and @ (P @ (F @ Y))) @ ((Q @ (F @ Y))))))) @ 
                                         % F not surjective
                                         (some(Type) @ lam(Z,((and @ ((and @ (P @ Z)) @ ((Q @ Z)))) @ (all(Type) @ lam(R, (imp @ ((and @ (P @ R)) @ (not @ (Q @ R)))) @ (not @ ((eq(Type) @ (F @ R)) @ Z))
                                                         )
                                         )
                 )))))))))),'\\textit{most}') :- Type = e.

lingaxHO([(only(_,g),_)],[],(all(Type > t) @ lam(P,all(Type > t) @ lam(Q, (iff @ ((only(Type,g) @ P) @ Q)) @ (all(Type) @ lam(X, ((imp @ (Q @ X)) @ (P @ X))))))),'\\textit{only}') :- Type = e.

% Conservativity

lingaxHO([(Det,_)],[],
all(e > t) @ lam(P,all(e>t) @ lam(Q,
((imp @ ((Det @ P) @ Q)) @
(some(e) @ lam(X,(((and @ (P @ X)) @ (Q @ X))))))
)),'Conservativity of SEVERAL') :-
   member(Det,[several(e,g)]).

% Monotonicity: upwards on first argument

lingaxHO([(Det,_)],[],
all(e > t) @ lam(P,all(e>t) @ lam(Q,all(e>t) @ lam(P2,
((imp @ (((Det @ P) @ Q))) @
((imp @ (
all(e) @ lam(X,(imp @ (P @ X)) @ (P2 @ X)))) @
((Det @ P2) @ Q))
))))
,'Monotonicity: upwards on first argument: SEVERAL, MANY') :- member(Det,[several(e,g),many(e,g)]).

% Monotonicity: upwards on second argument

lingaxHO([(Det,_)],[],
all(e > t) @ lam(P,all(e>t) @ lam(Q,all(e>t) @ lam(Q2,
((imp @ (((Det @ P) @ Q))) @
((imp @ (
all(e) @ lam(X,(imp @ (Q @ X)) @ (Q2 @ X)))) @
((Det @ P) @ Q2))
))))
, 'Monotonicity: upwards on second argument: SEVERAL, MANY') :- member(Det,[several(e,g),many(e,g)]).

% Monotonicity: downwards on first argument

lingaxHO([(Det,_)],[],
all(e > t) @ lam(P,all(e>t) @ lam(Q,all(e>t) @ lam(P2,
((imp @ (((Det @ P) @ Q))) @
((imp @ (
all(e) @ lam(X,(imp @ (P2 @ X)) @ (P @ X)))) @
((Det @ P2) @ Q))
))))
, 'Monotonicity: downwards on first argument: FEW') :- member(Det,[few(e,g)]).

% Monotonicity: downwards on second argument

lingaxHO([(Det,_)],[],
all(e > t) @ lam(P,all(e>t) @ lam(Q,all(e>t) @ lam(Q2,
((imp @ (((Det @ P) @ Q))) @
((imp @ (
all(e) @ lam(X,(imp @ (Q2 @ X)) @ (Q @ X)))) @
((Det @ P) @ Q2))
))))
, 'Monotonicity: downwards on second argument: FEW') :- member(Det,[few(e,g)]).

% Non-empty extension

lingaxHO([(few(e,g),_)],[],

all(e>t) @ lam(P, all(e>t) @ lam(Q,((imp @ (all(e) @ lam(X,(not @ ((and @ (P @ X)) @ (Q @ X))))))

@ ((few(e,g) @ P) @ Q)))), 'Non-empty Extension: FEW').


% Mutual exclusivity of MANY and FEW

lingaxHO([(many(e,g),_),(few(e,g),_)],[],
all(e>t) @ lam(P, all(e>t) @ lam(Q, not @ ((and @ ((many(e,g) @ P) @ Q)) @ ((few(e,g) @ P) @ Q)))), 'Mutual exclusiveness of MANY and FEW').


% 'belief'
  % Modus Ponens under belief
lingaxHO([(Constant,_)],[],
all(e) @ lam(X,all(s>t) @ lam(P, all(s>t) @ lam(Q, all(s) @ lam(W,

((imp @

((and @ (((Constant @ W) @ P) @ X)) @

(all(s) @ lam(W2, ((imp @ (P @ W2)) @ (Q @ W2)))))) @

(((Constant @ W) @ Q) @ X))
)))), 'Deductivity: \\textit{think, know}') :-
        member(Constant,[think,know]).



% Veracity of Knowledge
lingaxHO([(know,_)],[],all(e) @ lam(X,all(s>t) @ lam(P, all(s) @ lam(W,((imp @ (((know @ W) @ P) @ X)) @ (P @ W))))), 'Veridicality: \\textit{know}').

lingaxHO([(seeECM,_)],[],
all(e) @ lam(X,all(s>t) @ lam(P, all(s) @ lam(W,((imp @ (((seeECM @ W) @ P) @ X)) @ (P @ W))))), 'seeECM').

lingaxHO([(small,_),(large,_)],[],
all(s) @ lam(W, all(e) @ lam(X,all(s>(e>t)) @ lam(P,
(imp @ (((small @ W) @ P) @ X)) @ (not @ ((((large @ W) @ P) @ X)))))), 'Mutual exclusiveness of \\textit{small, large}').


/*========================================================================
    Pretty-printing Meaning Postulates
========================================================================*/

printMeaningPostulates :-
     foreach(clause(lingaxHO(A,B,C,Name),Cond), printLingax(A,B,C,Name,Cond)).

printLingax(Triggers,Vars,Postulate,Name,Cond) :-
     processCond(Cond,ContainsMetaVariable),
     print('\\item '),print(Name),nl,nl,
     betaConversion:completeAndUnifyTypes(Postulate,PostulateComplete),
     write('$'),hoi:ho2Latex(PostulateComplete,short,fo),write('$'),nl,nl.

processCond(true,no).
processCond(member(Constant,_),yes) :-
    Constant = '$\\alpha$'.
processCond(Type = T,no) :- Type = T.
processCond(A,no) :- write(processCond(A)),nl.
