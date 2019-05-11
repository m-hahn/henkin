/*************************************************************************

    File: translationTypedTotalAxioms.pl
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

:- op(500,xf,istrue).
:- op(500,xfx,@).

/*=======================================================
   Axioms and Signature
=========================================================*/

/*
* AXIOMS DESCRIBED IN THE PAPER:
*   axiom(1,...): basic axioms
*   constAxiom(ListOfConstants,Axiom): axioms for specific constants
*   sig(1,...): basic axioms ensuring the basic types have nonempty extension
*
* OTHER AXIOMS:
*   sig(0,...): axioms for the type system, required for a super-strong
              axiomatization not described in the paper
*/



% Extensionality
axiom(1,all(X,all(Y, all(Type1, all(Type2, imp(has_type(X,f(Type1,Type2)), imp(has_type(Y,f(Type1,Type2)),imp(all(Z,imp(has_type(Z,Type1),f(X,Z) = f(Y,Z))), X = Y)))))))).
axiom(1,all(X,all(Y,imp(has_type(X,t),imp(has_type(Y,t),imp(iff(X istrue, Y istrue),X = Y)))))).


% Signature
sig(1,all(X,imp(istrue(X),has_type(X,t)))).
sig(1,has_type(w,s)).
sig(1,has_type(mia,e)).
sig(1, some(F, has_type(F,t))).
sig(1,all(X,all(Y,all(Tfxy,imp(some(Ty, and(has_type(X,f(Ty,Tfxy)),has_type(Y, Ty))), has_type(f(X,Y), Tfxy)))))).

% Axioms for Constants
constAxiom([(i(_),_)],all(X,all(T,imp(has_type(X,T),f(i(T),X) = X)))).
constAxiom([(k(_,_),_)],all(X,all(Y,all(S,all(T,imp(has_type(X,S),imp(has_type(Y,T),f(f(k(S,T),X),Y) = X))))))).
constAxiom([(sc(_,_,_),_)],all(X,all(Y,all(Z,all(S,all(T,all(U,imp(has_type(X,f(S,f(T,U))),imp(has_type(Y,f(S,T)),imp(has_type(Z,S),f(f(f('sc'(S,T,U),X),Y),Z) = f(f(X,Z),f(Y,Z)))))))))))).

constAxiom([(k(_,_),_)],all(X,all(Y,imp(some(A,some(B,and(has_type(A,X),has_type(B,Y)))), has_type(k(X,Y),f(X,f(Y,X))))))).
constAxiom([(i(_),_)],all(X,imp(some(A,has_type(A,X)), has_type(i(X),f(X,X))))).
constAxiom([(sc(_,_,_),_)],all(X,all(Y,all(Z,imp(some(A,some(B,some(C,and(has_type(A,X),and(has_type(B,Y),has_type(C,Z)))))), has_type(sc(X,Y,Z),f(f(X,f(Y,Z)),f(f(X,Y),f(X,Z))))))))).

constAxiom([(or,_)],has_type(or, f(t,f(t,t)))).
constAxiom([(and,_)],has_type(and, f(t,f(t,t)))).
constAxiom([(imp,_)],has_type(imp, f(t,f(t,t)))).

constAxiom([(iota(_),_)],all(Type, all(P, imp(has_type(P,f(Type,t)), and(has_type(iota(Type), f(f(Type,t),Type)), imp(some(Y,istrue(f(P,Y))), istrue(f(P,f(iota(Type),P))))))))).

constAxiom([(all(_),_)],all(Type, all(Z,imp(has_type(Z,Type), and(has_type(all(Z),f(Type,t)),all(X,iff(f(all(Type),X) istrue, all(Y, imp(has_type(Y,Type),f(X,Y) istrue))))))))).

constAxiom([(some(_),_)],all(Type, all(Z,imp(has_type(Z,Type), and(has_type(some(Z),f(Type,t)),all(X,iff(f(some(Type),X) istrue, all(Y, imp(has_type(Y,Type),f(X,Y) istrue))))))))).



constAxiom([(not,_)],has_type(not,f(t,t))).
constAxiom([(not,_)],all(X,imp(has_type(X,t),iff(f(not,X) istrue, not(X istrue))))).
constAxiom([(and,_)],all(X,all(Y,iff(f(f(and,X),Y) istrue, and(X istrue, Y istrue))))).
constAxiom([(imp,_)],all(X,imp(has_type(X,t),all(Y,imp(has_type(Y,t),iff(f(f(imp,X),Y) istrue, imp(X istrue, Y istrue))))))).
constAxiom([(or,_)],all(X,imp(has_type(X,t),all(Y,imp(has_type(Y,t),iff(f(f(or,X),Y) istrue, or(X istrue, Y istrue))))))).
constAxiom([(eq(_),_)],all(T,imp(some(Z,has_type(Z,T)),all(X,all(Y,iff(f(f(eq(T),X),Y) istrue, and(has_type(X,T),X = Y))))))).


% Axioms for hyper-strong axiomatization
sig(0,all(X,exactlyOne(some(Object, has_type(Object,X)),some(Type,has_type(X,Type)),X = sinkTerm))). % either type or term
sig(0,all(X,imp(some(Type,has_type(X,Type)),some(Y,all(Z,iff(Z = Y, has_type(X,Z))))))). % every term has exactly one type
sig(0,all(X,all(Y,iff(some(Object, has_type(Object,f(X,Y))),and(some(Object1, has_type(Object1,X)),some(Object2, has_type(Object2,Y))))))). % use of f(.,.)
sig(0,all(X,all(Y,imp(some(Type,has_type(f(X,Y),Type)), and(some(Type1, has_type(X,Type1)),some(Type2, has_type(Y,Type2))))))).

sig(0, all(X, f(X,sinkTerm) = sinkTerm)).
sig(0, all(X, f(sinkTerm, X) = sinkTerm)).

sig(0,not('s' = 'e')).
sig(0,not('t' = 'e')).
sig(0,not('t' = 's')).

