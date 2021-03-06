/*************************************************************************

    File: fol2prover9.pl
    Copyright (C) 2004,2005,2006 Patrick Blackburn & Johan Bos
    Modified by Michael Hahn (2015).

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de

    It is adapted from the file fol2otter.pl of BB1, version 1.3
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

:- module(fol2prover9,[fol2prover9/2]).

:- use_module(comsemPredicates,[basicFormula/1]).


/*========================================================================
   Translates formula to Prover9 syntax on Stream
========================================================================*/

fol2prover9(Formula,Stream):- 
	%format(Stream,'set(auto).~n~n',[]),
	format(Stream,'assign(max_seconds,30).~n~n',[]),
	%format(Stream,'clear(print_proofs).~n~n',[]),
	format(Stream,'set(prolog_style_variables).~n~n',[]),
	format(Stream,'formulas(goals).~n~n',[]),
	printProver9Formula(Stream,Formula),
	format(Stream,'~nend_of_list.~n',[]).




/*========================================================================
   Print a Prover9 formula
========================================================================*/

printProver9Formula(Stream,F):-
	   \+ \+ (
		     numbervars(F,0,_),
		     printProver9(Stream,F,5)
		 ),
	   format(Stream,'.~n',[]).


/*========================================================================
   Print Prover9 formulas
========================================================================*/

printProver9(Stream,some(X,Formula),Tab):- 
   write(Stream,'(exists '),
   write_term(Stream,X,[numbervars(true)]),
   write(Stream,' '),
   printProver9(Stream,Formula,Tab),
   write(Stream,')').

printProver9(Stream,all(X,Formula),Tab):- 
   write(Stream,'(all '),
   write_term(Stream,X,[numbervars(true)]),   
   write(Stream,' '),
   printProver9(Stream,Formula,Tab),
   write(Stream,')').

printProver9(Stream,que(X,Formula1,Formula2),Tab):- 
   write(Stream,'(exists '),
   write_term(Stream,X,[numbervars(true)]),   
   write(Stream,' '),
   printProver9(Stream,and(Formula1,Formula2),Tab),
   write(Stream,')').

printProver9(Stream,and(Phi,Psi),Tab):- 
   write(Stream,'('),
   printProver9(Stream,Phi,Tab), 
   format(Stream,' & ~n',[]),
   tab(Stream,Tab),
   NewTab is Tab + 5,
   printProver9(Stream,Psi,NewTab),
   write(Stream,')').

printProver9(Stream,or(Phi,Psi),Tab):- 
   write(Stream,'('),
   printProver9(Stream,Phi,Tab),
   write(Stream,' | '),
   printProver9(Stream,Psi,Tab),
   write(Stream,')').

printProver9(Stream,imp(Phi,Psi),Tab):- 
   write(Stream,'('),  
   printProver9(Stream,Phi,Tab),
   write(Stream,' -> '),
   printProver9(Stream,Psi,Tab),
   write(Stream,')').

printProver9(Stream,not(Phi),Tab):- 
   write(Stream,'-('),
   printProver9(Stream,Phi,Tab),
   write(Stream,')').

printProver9(Stream,eq(X,Y),_):- 
   write(Stream,'('),  
   write_term(Stream,X,[numbervars(true)]),
   write(Stream,' = '),
   write_term(Stream,Y,[numbervars(true)]),
   write(Stream,')').

printProver9(Stream,Phi,_):-
   %basicFormulaIncludingFunctions(Phi),
   %basicFormula(Phi),
   print('printProver9 '),write(Phi),nl,
   write_term(Stream,Phi,[numbervars(true)]).

printProver9(_,Phi,_) :- % mhahn
   print('printProver9 '),write(Phi),nl,nl.
