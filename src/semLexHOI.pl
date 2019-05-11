/*************************************************************************

    File: semLexHOI.pl
    Copyright (C) 2015 Michael Hahn

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de

    This file is adapted from the file semLexLambda.pl of BB1,
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



:- dynamic(semLex/2).
:- retractall(semLex(_,_)).

:- op(500,xfx,@).

semLexBB(det,M) :-
   M = [type:def,
        sem:lam((P,s>(e>t)),lam((Q,s>(e>t)),((Q @ W) @ (iota(e) @ (P @ W)))))].

semLexBB(det,M):-
   M = [type:uni,
        sem:lam(U,lam(V,all(Type) @ lam((X,Type),(imp @ ((U @ (W,s)) @ X)) @ ((V @ (W,s)) @ (X)))))].

semLexBB(det,M):-
   M = [type:indef,
        sem:lam(P,lam(Q,some(Type) @ lam((X,Type), (and @ ((P @ (W,s)) @ ((X)))) @ ((Q @ (W,s)) @ (X)))))].

semLexBB(det,M) :-
   M = [type:no,
       sem:lam(U,lam(V,all(Type) @ lam((X,Type),(imp @ ((U @ (W,s)) @ X)) @ (not @ ((V @ (W,s)) @ (X))))))].



semLexBB(det,M) :-
   M = [type:Quantifier,
        sem:lam(P,lam(Q,(((QTerm, (Type>t)> ((Type>t)>t)) @ (P @ (W, s))) @ (Q @ (W,s)))))],
  member(Quantifier,[only,most,two,many,few,at_least_three,at_most_two,a_few,several]),
  QTerm =.. [Quantifier,Type,g].



semLexBB(det,M):-
   M = [type:wh,
        sem:lam(P,
                lam(Q,
                    (((que) @ lam((X),
                                  ((P @ (W,s)) @ X)
                                 )
                     ) @ lam((Y),
                             ((Q @ (W,s)) @ Y)
                            )
                    )
                   )
               )].

semLexBB(pn,M):-
   M = [symbol:Sym,
        sem:(lam((P),(((P @ (_,s)) @ (((Sym,e)))))))].

semLexBB(noun,M):-
   M = [symbol:Sym,
        sem:(Sym, s > (e>t))].

semLexBB(iv,M):-
   M = [symbol:Sym,
        sem:lam(W,lam(X,((Sym @ W)  @ (X ))))].

semLexBB(tv,M):-
   M = [symbol:Sym,
        sem:lam(K,lam(W,lam((Y),(K @ lam(W,lam((X),((Sym @ (W,s)) @ (Y,e)) @ ((X,e ))))))))].

% think
semLexBB(sv,M):- %(mhahn)
   M = [symbol:Sym,
        sem:(lam((P,(s>t)),lam(W,
                 lam((X,e),
                     ((((Sym , s> ((s>t)> (e>t))) @ (W,s)) @ P) @ X)))))].

semLexBB(ecmv,M):- %(mhahn)
   M = [symbol:Sym,
        sem:(lam(P,lam(W,
                 lam(X,
                     (((Sym  )
                       @ (W,s)
                      ) @ 
                      (
                       P
                      )
                     )
                    ) 
                 @ (X))))].

% want, seek
semLexBB(tiv, M) :- %(mhahn)
   M = [symbol:Sym,
      sem:lam(P,lam(W,lam(X,((Sym @ W) @ P) @ X)))].

semLexBB(qnp,M):-
   M = [type:wh,
        symbol:Sym,
        sem:(que @ Sym)].

semLexBB(cop,M):-
   M = [pol:pos,
        sem:lam(K,lam(W,lam((Y),(K @ lam(W,lam(X,(eq(e) @ Y) @ X ))))))];
   M = [pol:neg,
        sem:lam(K,lam(W,lam((Y),(K @ lam(W,lam((X),(not @ (((eq(e)) @ (Y)) @ (X , e )))))))))].

semLexBB(relpro,M):-
   M = [sem:lam(P,lam(Q,lam((X),(and @ (P @ X)) @ (Q @ X))))].

semLexBB(prep,M):-
   M = [symbol:Sym,
        sem:Sym]. 

%mhahn
semLexBB(adj, M) :-
   M = [symbol:Sym,type:_,
        sem:lam((P,s>(e>t)),lam((W,s),lam((X,e),(((Sym @ W) @ P) @ X))))].


semLexBB(av,M):-
   M = [pol:neg,
        sem:lam(P,lam(W,lam(X,(not @ ((P @ W) @ X)))))]; 
   M = [pol:pos,
        sem:lam(P,(P))].

semLexBB(coord,M):-
    (M = [type:conj|_],Sym = and;
   M = [type:disj|_], Sym = or),
   M = [_,sem:lam(P,lam(Q,lam(W,lam(X, (Sym @ ((P @ W) @ X )) @ ((Q @ W )@ X)))))].


semLexBB(adv,[symbol:Sym,sem:Sem]) :-
     Sem = lam(P,lam(W,lam((X,e),((Sym, s > ((s > t) > t)) @ W) @ lam(W2,(P @ W2) @ X)))).

:- 
   \+ ((semLexBB(A,Features), \+ (append(Syn, [sem:C], Features),
   betaConversion:completeTyping(C,B),
   betaConversion:unifyTypes(B),
   append(Syn, [sem:B], Result), asserta(hoi:semLex(A,Result))))).
