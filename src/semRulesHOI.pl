/*************************************************************************

    File: semRulesHOI.pl
    Copyright (C) 2015 Michael Hahn

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de

    This file is adapted from the file semRulesLambda.pl of BB1,
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

:- op(500,xfx,@).

/*========================================================================
   Semantic Rules
========================================================================*/

combine(t:Converted,[s:Sem]):- 
   betaConversion:completeAndUnifyTypes(Sem,Sem2),  Sem2 = (_,t), betaConvert(Sem2,Converted),hoi:freeWorldArgument(w,Converted).

combine(t:Converted,[q:Sem]):- 
   betaConversion:completeTyping(Sem,Sem2), betaConversion:unifyTypes(Sem2), betaConvert(Sem2,Converted),hoi:freeWorldArgument(w,Converted).

combine(s:(A @ B),[np:A,vp:B]).
combine(s:((A,(t>t)) @ (B,t)),[s:A,s:B]).
combine(s:imp @ S, [if:S]).



combine(s:(or @ S),[either:S]).
combine(s:S,[then:S]).
combine(s:S,[or:S]).
combine(s:((and @ A) @ B), [and:(A,B)]).

combine(negS:(not @ (S,t), t),[s:S]). %mhahn

combine(sinv:(B @ (A @ C)),[av:A,np:B,vp:C]).

combine(q:(A @ B),[whnp:A,vp:B]).
combine(q:A,[sinv:A]).

combine(np:((B @ A) @ C),[np:A,coord:B,np:C]).
combine(np:(A @ B),[det:A,n:B]).
combine(np:A,[pn:A]).
combine(np:A,[qnp:A]).

combine(whnp:(A @ B),[det:A,n:B]).
combine(whnp:A,[qnp:A]).

combine(n:((B @ A) @ C),[n:A,coord:B,n:C]).
combine(n:(A @ B),[adj:A,n:B]).
combine(n:A,[noun:A]).
combine(n:(B @ A),[noun:A,nmod:B]).

combine(nmod:A,[pp:A]).
combine(nmod:A,[rc:A]).
combine(nmod:lam(P,(A @ (B @ P))),[pp:A,nmod:B]).

combine(vp:((B @ A) @ C),[vp:A,coord:B,vp:C]).
combine(vp:(A @ B),[av:A,vp:B]).
combine(vp:(A @ B),[cop:A,np:B]).
combine(vp:lam(W,lam(X,(some(_) @ (lam(P, (((B @ P) @ W) @ X)))))),[cop:_,adj:B]).
combine(vp:A,[iv:A]).
combine(vp:(A @ B),[tv:A,np:B]).
combine(vp:(A @ lam((_,s),B)),[sv:A,s:B]). %(mhahn)
combine(vp:(A @ lam((_,s),B)),[tiv:A,np:B]).  %(mhahn)
combine(vp:(SV @ lam((W,s),(NP @ VPI))),[ecmv:SV,np:NP,vp:VPI]).
combine(vp:(ADV @ VP),[adv:ADV,vp:VP]).

combine(pp:(A @ B),[prep:A,np:B]).

combine(rc:(A @ B),[relpro:A,vp:B]).

combine(ap:lam(P,lam(W,lam(X,((Adv @ (Adj @ P)) @ W) @ X))),[adv:Adv,adj:Adj]).


/*===================================================*/

freeWorldArgument(W, (Term,Type)) :-
     var(Term), Type == s, !, Term = W.
freeWorldArgument(_, (Term, _)) :-
     var(Term), !.
freeWorldArgument(_,(lam((W2,Type), Term),_)) :-
     Type == s, !, freeWorldArgument(W2,Term).
freeWorldArgument(W, (lam(Var, Term), _)) :- !,
    freeWorldArgument(W,Var),
    freeWorldArgument(W,Term).
freeWorldArgument(W, ((Func @ Arg), _)) :- !,
     freeWorldArgument(W, Func),
     freeWorldArgument(W,Arg).
freeWorldArgument(_, (Term, Type)) :-
    betaConversion:isTy2Constant((Term,Type)), !.
freeWorldArgument(_, (Term,_)) :-
    atom(Term), !.
freeWorldArgument(A,B) :-
    write(freeWorldArgument(A,B)),nl.
