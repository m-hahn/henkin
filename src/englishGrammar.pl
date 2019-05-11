/*************************************************************************

    File: englishGrammar.pl
    Copyright (C) 2004,2005,2006 Patrick Blackburn & Johan Bos
    Modified by Michael Hahn (2015).

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de

    It is adapted from the file englishGrammar.pl of BB1, version 1.3
    by Patrick Blackburn & Johan Bos. Changes are marked with 'mhahn'.

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


/*========================================================================
   Texts
========================================================================*/


t([sem:T])--> 
   s([coord:no,sem:S]),
   {combine(t:T,[s:S])}.

t([sem:T])--> 
   s([coord:yes,sem:S]),
   {combine(t:T,[s:S])}.

t([sem:T])--> 
   q([sem:Q]),
   {combine(t:T,[q:Q])}.


/*========================================================================
   Sentences
========================================================================*/

s([coord:no,sem:Sem])--> 
   np([coord:_,num:Num,gap:[],sem:NP]), 
   vp([coord:_,inf:fin,num:Num,gap:[],sem:VP]), 
   {combine(s:Sem,[np:NP,vp:VP])}.

s([coord:no,sem:Sem]) --> %(mhahn)
    [it,is,not,the,case,that],
    s([coord:_,sem:S]),
    {combine(negS:Sem,[s:S])}.

s([coord:no,sem:Sem]) --> %(mhahn)
    [it,is,false,that],
    s([coord:_,sem:S]),
    {combine(negS:Sem,[s:S])}.

s([coord:no,sem:Sem]) --> %(mhahn)
    [it,is,true,that],
    s([coord:_,sem:Sem]).

s([coord:yes,sem:Sem])--> 
   s([coord:ant,sem:S1]), 
   s([coord:con,sem:S2]), 
   {combine(s:Sem,[s:S1,s:S2])}.

s([coord:yes,sem:Sem])--> 
   s([coord:either,sem:S1]), 
   s([coord:or,sem:S2]), 
   {combine(s:Sem,[s:S1,s:S2])}.

s([coord:ant,sem:Sem])--> 
   [if], 
   s([coord:_,sem:S]), % (no -> _) by mhahn)
   {combine(s:Sem,[if:S])}.

s([coord:either,sem:Sem])--> 
   [either], 
   s([coord:no,sem:S]),
   {combine(s:Sem,[either:S])}.

s([coord:con,sem:Sem])--> 
   [then], 
   s([coord:_,sem:S]), % (no -> _) by mhahn)
   {combine(s:Sem,[then:S])}.

s([coord:con,sem:Sem])-->
   s([coord:no,sem:S]),
   {combine(s:Sem,[then:S])}.

s([coord:yes,sem:Sem])-->  %(mhahn)
   s([coord:no,sem:S1]),
   [and], 
   s([coord:_,sem:S2]),
   {combine(s:Sem,[and:(S1,S2)])}.

s([coord:or,sem:Sem])-->
   [or], 
   s([coord:no,sem:S]),
   {combine(s:Sem,[or:S])}.

sinv([gap:G,sem:S])-->
   av([inf:fin,num:Num,sem:Sem]),
   np([coord:_,num:Num,gap:[],sem:NP]),
   vp([coord:_,inf:inf,num:Num,gap:G,sem:VP]), 
   {combine(sinv:S,[av:Sem,np:NP,vp:VP])}.


/*========================================================================
   Questions
========================================================================*/

q([sem:Sem])--> 
   whnp([num:Num,sem:NP]), 
   vp([coord:_,inf:fin,num:Num,gap:[],sem:VP]), 
   {combine(q:Sem,[whnp:NP,vp:VP])}.

q([sem:Sem])--> 
   whnp([num:_,sem:NP]), 
   sinv([gap:[np:NP],sem:S]),
   {combine(q:Sem,[sinv:S])}.


/*========================================================================
   Noun Phrases
========================================================================*/

%mhahn: removed num:sg to cover plural NPs

np([coord:no,num:_,gap:[np:NP],sem:NP])--> [].

np([coord:yes,num:_,gap:[],sem:NP])--> 
   np([coord:no,num:sg,gap:[],sem:NP1]), 
   coord([type:conj,sem:C]), 
   np([coord:_,num:_,gap:[],sem:NP2]), 
   {combine(np:NP,[np:NP1,coord:C,np:NP2])}.

np([coord:yes,num:_,gap:[],sem:NP])--> 
   np([coord:no,num:sg,gap:[],sem:NP1]), 
   coord([type:disj,sem:C]), 
   np([coord:_,num:sg,gap:[],sem:NP2]), 
   {combine(np:NP,[np:NP1,coord:C,np:NP2])}.

np([coord:no,num:_,gap:[],sem:NP])--> 
   det([mood:decl,type:_,sem:Det]),
   n([coord:_,sem:N]), 
   {combine(np:NP,[det:Det,n:N])}.

np([coord:no,num:_,gap:[],sem:NP])-->
   n([coord:_,sem:N]), 
   {combine(np:NP,[det:Det,n:N]),det([mood:decl,type:indef,sem:Det],_,[])}.

np([coord:no,num:_,gap:[],sem:NP])--> 
   pn([sem:PN]), 
   {combine(np:NP,[pn:PN])}.

np([coord:no,num:_,gap:[],sem:NP])--> 
   qnp([mood:decl,sem:QNP]), 
   {combine(np:NP,[qnp:QNP])}.


/*========================================================================
   WH Noun Phrases
========================================================================*/

whnp([num:sg,sem:NP])--> 
   qnp([mood:int,sem:QNP]), 
   {combine(whnp:NP,[qnp:QNP])}.

whnp([num:sg,sem:NP])--> 
   det([mood:int,type:_,sem:Det]), 
   n([coord:_,sem:N]), 
   {combine(whnp:NP,[det:Det,n:N])}.


/*========================================================================
   Nouns
========================================================================*/

n([coord:yes,sem:N])--> 
   n([coord:no,sem:N1]), 
   coord([type:_,sem:C]),  
   n([coord:_,sem:N2]),
   {combine(n:N,[n:N1,coord:C,n:N2])}.

n([coord:C,sem:Sem])--> 
   adj([sem:A]), 
   n([coord:C,sem:N]), 
   {combine(n:Sem,[adj:A,n:N])}.

n([coord:no,sem:N])--> 
   noun([sem:Noun]),
   {combine(n:N,[noun:Noun])}.

n([coord:no,sem:Sem])--> 
   noun([sem:N]), 
   nmod([sem:PP]),
   {combine(n:Sem,[noun:N,nmod:PP])}. 

nmod([sem:N])--> 
   pp([sem:PP]),
   {combine(nmod:N,[pp:PP])}.

nmod([sem:N])--> 
   rc([sem:RC]),
   {combine(nmod:N,[rc:RC])}.

nmod([sem:Sem])--> 
   pp([sem:PP]), 
   nmod([sem:NMod]),
   {combine(nmod:Sem,[pp:PP,nmod:NMod])}.


/*========================================================================
   Verb Phrases
========================================================================*/

vp([coord:yes,inf:Inf,num:Num,gap:[],sem:VP])--> 
   vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP1]), 
   coord([type:_,sem:C]), 
   vp([coord:_,inf:Inf,num:Num,gap:[],sem:VP2]),
   {combine(vp:VP,[vp:VP1,coord:C,vp:VP2])}.

vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP])--> 
   av([inf:Inf,num:Num,sem:Mod]), 
   vp([coord:_,inf:inf,num:Num,gap:[],sem:V2]), 
   {combine(vp:VP,[av:Mod,vp:V2])}.

vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP])--> 
   cop([inf:Inf,num:Num,sem:Cop]), 
   np([coord:_,num:_,gap:[],sem:NP]), 
   {combine(vp:VP,[cop:Cop,np:NP])}.

vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP])--> %(mhahn)
   cop([inf:Inf,num:Num,sem:Cop]),
   adj([sem:Adj]),
   {combine(vp:VP,[cop:Cop,adj:Adj])}.

vp([coord:no,inf:Inf,num:Num,gap:[],sem:VP])--> 
   iv([inf:Inf,num:Num,sem:IV]), 
   {combine(vp:VP,[iv:IV])}.

vp([coord:no,inf:I,num:Num,gap:G,sem:VP])-->   
   tv([inf:I,num:Num,sem:TV]), 
   np([coord:_,num:_,gap:G,sem:NP]), 
   {combine(vp:VP,[tv:TV,np:NP])}.

% simplifying assumption: gap:[]
vp([coord:no, inf:I, num:Num, gap:[], sem:VP])--> %(mhahn)
   sv([inf:I, num:Num,sem:SV]),
   s([coord:no, sem:S]),
   {combine(vp:VP,[sv:SV,s:S])}.

vp([coord:no, inf:I, num:Num, gap:[], sem:VP])--> %(mhahn)
   sv([inf:I, num:Num,sem:SV]),[that],
   s([coord:no, sem:S]),
   {combine(vp:VP,[sv:SV,s:S])}.

vp([coord:no, inf:I, num:Num, gap:G, sem:VP])--> %(mhahn)
   ecmv([inf:I,num:Num,sem:SV]),
   np([coord:_,num:_,gap:[],sem:NP]),
   vp([coord:_, inf:inf, num:_, gap:G,sem:VPI]),
   {combine(vp:VP,[ecmv:SV,np:NP,vp:VPI])}.

vp([coord:no, inf:I, num:Num, gap:[], sem:VP])--> %(mhahn)
   tiv([inf:I, num:Num,sem:TIV]),
   np([_,_,_,sem:NP]),
{combine(vp:VP,[tiv:TIV,np:NP])}.

vp([coord:Coord, inf:I, num:Num, gap:Gap, sem:SemResu])--> %(mhahn)
   adv([sem:ADV]),
   vp([coord:Coord, inf:I, num:Num, gap:Gap, sem:VP]),
   {combine(vp:SemResu,[adv:ADV,vp:VP])}.

vp([coord:yes, inf:I, num:Num, gap:Gap, sem:SemResu])--> %(mhahn) % use Coord to avoid left recursion
   vp([coord:no, inf:I, num:Num, gap:Gap, sem:VP]),
   adv([sem:ADV]),
   {combine(vp:SemResu,[adv:ADV,vp:VP])}.



/*========================================================================
   Prepositional Phrases
========================================================================*/

pp([sem:PP])--> 
   prep([sem:Prep]), 
   np([coord:_,num:_,gap:[],sem:NP]), 
   {combine(pp:PP,[prep:Prep,np:NP])}.


/*========================================================================
   Relative Clauses
========================================================================*/

rc([sem:RC])--> 
   relpro([sem:RP]), 
   vp([coord:_,inf:fin,num:sg,gap:[],sem:VP]), 
   {combine(rc:RC,[relpro:RP,vp:VP])}.


/*========================================================================
   Lexical Rules
========================================================================*/

iv([inf:Inf,num:Num,sem:Sem])--> 
   {lexEntry(iv,[symbol:Sym,syntax:Word,inf:Inf,num:Num])},
   Word,
   {semLex(iv,[symbol:Sym,sem:Sem])}.

tv([inf:Inf,num:Num,sem:Sem])--> 
   {lexEntry(tv,[symbol:Sym,syntax:Word,inf:Inf,num:Num])},
   Word,
   {semLex(tv,[symbol:Sym,sem:Sem])}.

sv([inf:Inf, num:Num, sem:Sem])--> %(mhahn)
   {lexEntry(sv,[symbol:Sym,syntax:Word,inf:Inf,num:Num])},
   Word,
   {semLex(sv,[symbol:Sym,sem:Sem])}.

ecmv([inf:Inf, num:Num, sem:Sem])--> %(mhahn)
   {lexEntry(ecmv,[symbol:Sym,syntax:Word,inf:Inf,num:Num])},
   Word,
   {semLex(ecmv,[symbol:Sym,sem:Sem])}.

tiv([inf:Inf, num:Num, sem:Sem]) --> %(mhahn)
{lexEntry(tiv,[symbol:Sym,syntax:Word,inf:Inf,num:Num])},
   Word,
{semLex(tiv,[symbol:Sym,sem:Sem])}.

cop([inf:Inf,num:Num,sem:Sem])--> 
   {lexEntry(cop,[pol:Pol,syntax:Word,inf:Inf,num:Num])},
   Word,
   {semLex(cop,[pol:Pol,sem:Sem])}.

det([mood:M,type:Type,sem:Det])--> 
   {lexEntry(det,[syntax:Word,mood:M,type:Type])},
   Word,
   {semLex(det,[type:Type,sem:Det])}. 

pn([sem:Sem])--> 
   {lexEntry(pn,[symbol:Sym,syntax:Word])},
   Word,  
   {semLex(pn,[symbol:Sym,sem:Sem])}.

relpro([sem:Sem])--> 
   {lexEntry(relpro,[syntax:Word])},
   Word,
   {semLex(relpro,[sem:Sem])}.

prep([sem:Sem])--> 
   {lexEntry(prep,[symbol:Sym,syntax:Word])},
   Word,
   {semLex(prep,[symbol:Sym,sem:Sem])}.

adj([sem:Sem])--> %(mhahn)
   adv([sem:Adv]),
   adj([sem:Adj]),
   {combine(ap:Sem,[adv:Adv,adj:Adj])}.

adj([sem:Sem])--> 
   {lexEntry(adj,[symbol:Sym,type:Type,syntax:Word])},
   Word,
   {semLex(adj,[symbol:Sym,type:Type,sem:Sem])}.

av([inf:Inf,num:Num,sem:Sem])--> 
   {lexEntry(av,[syntax:Word,inf:Inf,num:Num,pol:Pol])},
   Word,
   {semLex(av,[pol:Pol,sem:Sem])}.

coord([type:Type,sem:Sem])--> 
   {lexEntry(coord,[syntax:Word,type:Type])},
   Word, 
   {semLex(coord,[type:Type,sem:Sem])}.

qnp([mood:M,sem:NP])--> 
   {lexEntry(qnp,[symbol:Symbol,syntax:Word,mood:M,type:Type])},
   Word,
   {semLex(qnp,[type:Type,symbol:Symbol,sem:NP])}.

noun([sem:Sem])--> 
   {lexEntry(noun,[symbol:Sym,syntax:Word])},
   Word,
   {semLex(noun,[symbol:Sym,sem:Sem])}.

adv([sem:Sem]) -->
{lexEntry(adv,[symbol:Sym,syntax:Word])},
   Word,
{semLex(adv,[symbol:Sym,sem:Sem])}.
