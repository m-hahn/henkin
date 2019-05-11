/*************************************************************************

    File: fol2tptp.pl
    Copyright (C) 2004,2005,2006 Patrick Blackburn & Johan Bos
    Modified by Michael Hahn (2015).

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de

    It is adapted from the file fol2tptp.pl of BB1, version 1.3
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

:- module(fol2tptp,[fol2tptp/3]).

:- use_module(comsemPredicates,[basicFormula/1]).

/*========================================================================
   Translates formula to TPTP syntax on Stream
========================================================================*/

fol2tptp(Formula,Stream, Version):- 
   environment(Version, Command),
   write(Stream,Command),
   \+ \+ ( numbervars(Formula,0,_),printTptp(Formula,Stream) ),
   write(Stream,').'),
   nl(Stream),!.

fol2tptp(A,B,C) :-
   write(fol2tptp(A,B,C)).

environment(eprover, 'input_formula(comsem,conjecture,') :- !.
environment(spass, 'fof(co1,conjecture,') :- !.
environment(_, 'input_formula(comsem,conjecture,').

/*========================================================================
   Print Tptp formulas
========================================================================*/

printTptp(some(X,Formula),Stream):- !,
   write(Stream,'(? ['),
   write_term(Stream,X,[numbervars(true)]),
   write(Stream,']: '),
   printTptp(Formula,Stream),
   write(Stream,')').

printTptp(que(X,Formula),Stream):- !,
   write(Stream,'(? ['),
   write_term(Stream,X,[numbervars(true)]),
   write(Stream,']: '),
   printTptp(Formula,Stream),
   write(Stream,')').

printTptp(all(X,Formula),Stream):- !,
   write(Stream,'(! ['),
   write_term(Stream,X,[numbervars(true)]),
   write(Stream,']: '),
   printTptp(Formula,Stream),
   write(Stream,')').

printTptp(and(Phi,Psi),Stream):- !,
   write(Stream,'('),
   printTptp(Phi,Stream), 
   write(Stream,' & '), 
   printTptp(Psi,Stream), 
   write(Stream,')').

printTptp(or(Phi,Psi),Stream):- !,
   write(Stream,'('),
   printTptp(Phi,Stream), 
   write(Stream,' | '),
   printTptp(Psi,Stream), 
   write(Stream,')').

printTptp(imp(Phi,Psi),Stream):- !,
   write(Stream,'('),
   printTptp(Phi,Stream), 
   write(Stream,' => '),
   printTptp(Psi,Stream), 
   write(Stream,')').

printTptp(imp(Phi,Psi),Stream):- !,
   write(Stream,'('),
   printTptp(Phi,Stream), 
   write(Stream,' <=> '),
   printTptp(Psi,Stream), 
   write(Stream,')').

printTptp(not(Phi),Stream):- !,
   write(Stream,'~ '),
   printTptp(Phi,Stream).

printTptp(eq(X,Y),Stream):- !,
   write_term(Stream,equal(X,Y),[numbervars(true)]).

printTptp(Phi,Stream) :- !,
   print('tptp '),write(Phi),nl,
   write_term(Stream,Phi,[numbervars(true)]).

%printTptp(Phi,Stream):-
 %  basicFormula(Phi),
  % write_term(Stream,Phi,[numbervars(true)]).
