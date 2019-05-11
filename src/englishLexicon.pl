/*************************************************************************

    File: englishLexicon.pl
    Copyright (C) 2004,2005,2006 Patrick Blackburn & Johan Bos
    Modified by Michael Hahn (2015).

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de

    It is adapted from the file englishLexicon.pl of BB1, version 1.3
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

:- dynamic(lexEntry/2).

/*========================================================================
   Determiners
========================================================================*/

lexEntry(det,[syntax:[every],mood:decl,type:uni]).
lexEntry(det,[syntax:[a],mood:decl,type:indef]).
lexEntry(det,[syntax:[an],mood:decl,type:indef]).
lexEntry(det,[syntax:[the],mood:decl,type:def]).
lexEntry(det,[syntax:[which],mood:int,type:wh]).
lexEntry(det,[syntax:[most],mood:decl,type:most]).
lexEntry(det,[syntax:[only],mood:decl,type:only]).
lexEntry(det,[syntax:[no],mood:decl,type:no]).
lexEntry(det,[syntax:[two],mood:decl,type:two]).
lexEntry(det,[syntax:[all],mood:decl,type:uni]).
lexEntry(det,[syntax:[some],mood:decl,type:indef]).
lexEntry(det,[syntax:[many],mood:decl,type:many]).
lexEntry(det,[syntax:[few],mood:decl,type:few]).
lexEntry(det,[syntax:[at,least,three],mood:decl,type:at_least_three]).
lexEntry(det,[syntax:[at,most,two],mood:decl,type:at_most_two]).
lexEntry(det,[syntax:[a,few],mood:decl,type:a_few]).
lexEntry(det,[syntax:[several],mood:decl,type:several]).


/*========================================================================
   Nouns
========================================================================*/

lexEntry(noun,[symbol:animal,syntax:[animal]]).
lexEntry(noun,[symbol:animal,syntax:[animals]]).
lexEntry(noun,[symbol:beverage,syntax:[beverage]]).
lexEntry(noun,[symbol:building,syntax:[building]]).
lexEntry(noun,[symbol:cup,syntax:[cup]]).
lexEntry(noun,[symbol:burger,syntax:[burger]]).
lexEntry(noun,[symbol:boxer,syntax:[boxer]]).
lexEntry(noun,[symbol:boss,syntax:[boss]]).
lexEntry(noun,[symbol:car,syntax:[car]]).
lexEntry(noun,[symbol:chainsaw,syntax:[chainsaw]]).
lexEntry(noun,[symbol:chairmanitel,syntax:[chairman,of,itel]]).
lexEntry(noun,[symbol:chairmandep,syntax:[chaiman,of,the,department]]).
lexEntry(noun,[symbol:criminal,syntax:[criminal]]).
lexEntry(noun,[symbol:customer,syntax:[customer]]).
lexEntry(noun,[symbol:drug,syntax:[drug]]).
lexEntry(noun,[symbol:episode,syntax:[episode]]).
lexEntry(noun,[symbol:fdshake,syntax:[five,dollar,shake]]).
lexEntry(noun,[symbol:footmassage,syntax:[foot,massage]]).
lexEntry(noun,[symbol:gimp,syntax:[gimp]]).
lexEntry(noun,[symbol:glass,syntax:[glass]]).
lexEntry(noun,[symbol:gun,syntax:[gun]]).
lexEntry(noun,[symbol:hammer,syntax:[hammer]]).
lexEntry(noun,[symbol:hashbar,syntax:[hash,bar]]).
lexEntry(noun,[symbol:person,syntax:[person]]).
lexEntry(noun,[symbol:husband,syntax:[husband]]).
lexEntry(noun,[symbol:joke,syntax:[joke]]).
lexEntry(noun,[symbol:man,syntax:[man]]).
lexEntry(noun,[symbol:needle,syntax:[needle]]).
lexEntry(noun,[symbol:owner,syntax:[owner]]).
lexEntry(noun,[symbol:phone,syntax:[phone]]).
lexEntry(noun,[symbol:piercing,syntax:[piercing]]).
lexEntry(noun,[symbol:plant,syntax:[plant]]).
lexEntry(noun,[symbol:politician,syntax:[politician]]).
lexEntry(noun,[symbol:qpwc,syntax:[quarter,pounder,with,cheese]]).
lexEntry(noun,[symbol:radio,syntax:[radio]]).
lexEntry(noun,[symbol:restaurant,syntax:[restaurant]]).
lexEntry(noun,[symbol:robber,syntax:[robber]]).
lexEntry(noun,[symbol:suitcase,syntax:[suitcase]]).
lexEntry(noun,[symbol:shotgun,syntax:[shotgun]]).
lexEntry(noun,[symbol:sword,syntax:[sword]]).
lexEntry(noun,[symbol:unicorn,syntax:[unicorn]]).
lexEntry(noun,[symbol:vehicle,syntax:[vehicle]]).
lexEntry(noun,[symbol:weapon,syntax:[weapon]]).
lexEntry(noun,[symbol:wife,syntax:[wife]]).
lexEntry(noun,[symbol:woman,syntax:[Syn]]) :- Syn = woman; Syn = women.
lexEntry(noun,[symbol:mammal,syntax:[mammal]]).
lexEntry(noun,[symbol:mouse,syntax:[Syn]]) :- Syn = mouse; Syn = mice.
lexEntry(noun,[symbol:elephant,syntax:[Syn]]) :- Syn = elephant; Syn = elephants.
lexEntry(noun,[symbol:legalauthority,syntax:[legal,authorities]]).
lexEntry(noun,[symbol:lawlecturer,syntax:[law,lecturers]]).
lexEntry(noun,[symbol:contract,syntax:[contract]]).
lexEntry(noun,[symbol:universitystudent,syntax:[university,student]]).

/*========================================================================
   Proper Names
========================================================================*/

lexEntry(pn,[symbol:butch,syntax:[butch]]).
lexEntry(pn,[symbol:esmarelda,syntax:[esmarelda]]).
lexEntry(pn,[symbol:honey_bunny,syntax:[honey,bunny]]).
lexEntry(pn,[symbol:jimmy,syntax:[jimmy]]).
lexEntry(pn,[symbol:jody,syntax:[jody]]).
lexEntry(pn,[symbol:jones,syntax:[jones]]).
lexEntry(pn,[symbol:jules,syntax:[jules]]).
lexEntry(pn,[symbol:lance,syntax:[lance]]).
lexEntry(pn,[symbol:marsellus,syntax:[marsellus]]).
lexEntry(pn,[symbol:marsellus,syntax:[marsellus,wallace]]).
lexEntry(pn,[symbol:marvin,syntax:[marvin]]).
lexEntry(pn,[symbol:mia,syntax:[mia]]).
lexEntry(pn,[symbol:mia,syntax:[mia,wallace]]).
lexEntry(pn,[symbol:pumpkin,syntax:[pumpkin]]).
lexEntry(pn,[symbol:smith,syntax:[smith]]).
lexEntry(pn,[symbol:thewolf,syntax:[the,wolf]]).
lexEntry(pn,[symbol:vincent,syntax:[vincent]]).
lexEntry(pn,[symbol:vincent,syntax:[vincent,vega]]).
lexEntry(pn,[symbol:yolanda,syntax:[yolanda]]).
lexEntry(pn,[symbol:excalibur,syntax:[excalibur]]).

lexEntry(pn,[symbol:kim,syntax:[kim]]).
lexEntry(pn,[symbol:john,syntax:[john]]).
lexEntry(pn,[symbol:dumbo,syntax:[dumbo]]).
lexEntry(pn,[symbol:mickey,syntax:[mickey]]).
lexEntry(pn,[symbol:1992,syntax:[1992]]).
lexEntry(pn,[symbol:itel,syntax:[itel]]).

/*========================================================================
   Quantified Noun Phrases
========================================================================*/

lexEntry(qnp,[symbol:person,syntax:[who],mood:int,type:wh]).
lexEntry(qnp,[symbol:thing,syntax:[what],mood:int,type:wh]).


/*========================================================================
   Intransitive Verbs
========================================================================*/

lexEntry(iv,[symbol:collapse,syntax:[collapse],inf:inf,num:sg]).
lexEntry(iv,[symbol:collapse,syntax:[collapses],inf:fin,num:sg]).
lexEntry(iv,[symbol:collapse,syntax:[collapse],inf:fin,num:pl]).

lexEntry(iv,[symbol:dance,syntax:[dance],inf:inf,num:sg]).
lexEntry(iv,[symbol:dance,syntax:[dances],inf:fin,num:sg]).
lexEntry(iv,[symbol:dance,syntax:[dance],inf:fin,num:pl]).

lexEntry(iv,[symbol:die,syntax:[die],inf:inf,num:sg]).
lexEntry(iv,[symbol:die,syntax:[dies],inf:fin,num:sg]).
lexEntry(iv,[symbol:die,syntax:[die],inf:fin,num:pl]).

lexEntry(iv,[symbol:growl,syntax:[growl],inf:inf,num:sg]).
lexEntry(iv,[symbol:growl,syntax:[growls],inf:fin,num:sg]).
lexEntry(iv,[symbol:growl,syntax:[growl],inf:fin,num:pl]).

lexEntry(iv,[symbol:playairguitar,syntax:[play,air,guitar],inf:inf,num:sg]).
lexEntry(iv,[symbol:playairguitar,syntax:[plays,air,guitar],inf:fin,num:sg]).
lexEntry(iv,[symbol:playairguitar,syntax:[play,air,guitar],inf:fin,num:pl]).

lexEntry(iv,[symbol:smoke,syntax:[smoke],inf:inf,num:sg]).
lexEntry(iv,[symbol:smoke,syntax:[smokes],inf:fin,num:sg]).
lexEntry(iv,[symbol:smoke,syntax:[smoke],inf:fin,num:pl]).

lexEntry(iv,[symbol:snort,syntax:[snort],inf:inf,num:sg]).
lexEntry(iv,[symbol:snort,syntax:[snorts],inf:fin,num:sg]).
lexEntry(iv,[symbol:snort,syntax:[snort],inf:fin,num:pl]).

lexEntry(iv,[symbol:shriek,syntax:[shriek],inf:inf,num:sg]).
lexEntry(iv,[symbol:shriek,syntax:[shrieks],inf:fin,num:sg]).
lexEntry(iv,[symbol:shriek,syntax:[shriek],inf:fin,num:pl]).

lexEntry(iv,[symbol:sing,syntax:[sing],inf:_,num:_]).
lexEntry(iv,[symbol:sing,syntax:[sings],inf:fin,num:_]).

lexEntry(iv,[symbol:walk,syntax:[walk],inf:inf,num:sg]).
lexEntry(iv,[symbol:walk,syntax:[walks],inf:fin,num:sg]).
lexEntry(iv,[symbol:walk,syntax:[walk],inf:fin,num:pl]).


/*========================================================================
   Transitive Verbs
========================================================================*/

lexEntry(tv,[symbol:clean,syntax:[clean],inf:inf,num:sg]).
lexEntry(tv,[symbol:clean,syntax:[cleans],inf:fin,num:sg]).
lexEntry(tv,[symbol:clean,syntax:[clean],inf:fin,num:pl]).

lexEntry(tv,[symbol:drink,syntax:[drink],inf:inf,num:sg]).
lexEntry(tv,[symbol:drink,syntax:[drinks],inf:fin,num:sg]).
lexEntry(tv,[symbol:drink,syntax:[drink],inf:fin,num:pl]).

lexEntry(tv,[symbol:date,syntax:[date],inf:inf,num:sg]).
lexEntry(tv,[symbol:date,syntax:[dates],inf:fin,num:sg]).
lexEntry(tv,[symbol:date,syntax:[date],inf:fin,num:pl]).

lexEntry(tv,[symbol:discard,syntax:[discard],inf:inf,num:sg]).
lexEntry(tv,[symbol:discard,syntax:[discards],inf:fin,num:sg]).
lexEntry(tv,[symbol:discard,syntax:[discard],inf:fin,num:pl]).

lexEntry(tv,[symbol:eat,syntax:[eat],inf:inf,num:sg]).
lexEntry(tv,[symbol:eat,syntax:[eats],inf:fin,num:sg]).
lexEntry(tv,[symbol:eat,syntax:[eat],inf:fin,num:pl]).

lexEntry(tv,[symbol:enjoy,syntax:[enjoy],inf:inf,num:sg]).
lexEntry(tv,[symbol:enjoy,syntax:[enjoys],inf:fin,num:sg]).
lexEntry(tv,[symbol:enjoy,syntax:[enjoy],inf:fin,num:pl]).

lexEntry(tv,[symbol:hate,syntax:[hate],inf:inf,num:sg]).
lexEntry(tv,[symbol:hate,syntax:[hates],inf:fin,num:sg]).
lexEntry(tv,[symbol:hate,syntax:[hate],inf:fin,num:pl]).

lexEntry(tv,[symbol:have,syntax:[have],inf:inf,num:sg]).
lexEntry(tv,[symbol:have,syntax:[has],inf:fin,num:sg]).
lexEntry(tv,[symbol:have,syntax:[have],inf:fin,num:pl]).

lexEntry(tv,[symbol:kill,syntax:[kill],inf:inf,num:sg]).
lexEntry(tv,[symbol:kill,syntax:[kills],inf:fin,num:sg]).
lexEntry(tv,[symbol:kill,syntax:[kill],inf:fin,num:pl]).

lexEntry(tv,[symbol:know,syntax:[know],inf:inf,num:sg]).
lexEntry(tv,[symbol:know,syntax:[knows],inf:fin,num:sg]).
lexEntry(tv,[symbol:know,syntax:[know],inf:fin,num:pl]).
lexEntry(tv,[symbol:know,syntax:[knew],inf:fin,num:_]).

lexEntry(tv,[symbol:like,syntax:[like],inf:inf,num:sg]).
lexEntry(tv,[symbol:like,syntax:[likes],inf:fin,num:sg]).
lexEntry(tv,[symbol:like,syntax:[like],inf:fin,num:pl]).

lexEntry(tv,[symbol:love,syntax:[love],inf:inf,num:sg]).
lexEntry(tv,[symbol:love,syntax:[loves],inf:fin,num:sg]).
lexEntry(tv,[symbol:love,syntax:[love],inf:fin,num:pl]).

lexEntry(tv,[symbol:pickup,syntax:[pick,up],inf:inf,num:sg]).
lexEntry(tv,[symbol:pickup,syntax:[picks,up],inf:fin,num:sg]).
lexEntry(tv,[symbol:pickup,syntax:[pick,up],inf:fin,num:pl]).

lexEntry(tv,[symbol:see,syntax:[sees],inf:fin,num:sg]).
lexEntry(tv,[symbol:see,syntax:[see],inf:_,num:_]).
lexEntry(tv,[symbol:see,syntax:[saw],inf:fin,num:_]).

lexEntry(tv,[symbol:sign,syntax:[sign],inf:inf,num:sg]).
lexEntry(tv,[symbol:sign,syntax:[signed],inf:fin,num:_]).

lexEntry(tv,[symbol:shoot,syntax:[shot],inf:inf,num:sg]).
lexEntry(tv,[symbol:shoot,syntax:[shot],inf:fin,num:sg]).
lexEntry(tv,[symbol:shoot,syntax:[shoots],inf:fin,num:sg]).
lexEntry(tv,[symbol:shoot,syntax:[shoot],inf:fin,num:pl]).

lexEntry(tv,[symbol:win,syntax:Syn,inf:fin,num:_]) :- Syn = [won]; Syn = [had,won].

/*========================================================================
   Intensional Verbs (mhahn)
=======================================================================*/

lexEntry(sv,[symbol:think, syntax:[think], inf:inf, num:_]).
lexEntry(sv,[symbol:think, syntax:[thinks], inf:fin, num:sg]).
lexEntry(sv,[symbol:think, syntax:[think], inf:fin, num:pl]).

lexEntry(sv,[symbol:know, syntax:[know], inf:inf, num:_]).
lexEntry(sv,[symbol:know, syntax:[knows], inf:fin, num:sg]).
lexEntry(sv,[symbol:know, syntax:[know], inf:fin, num:pl]).
lexEntry(sv,[symbol:know, syntax:[knew], inf:fin, num:_]).

lexEntry(tiv,[symbol:want, syntax:[want], inf:inf, num:_]).
lexEntry(tiv,[symbol:want, syntax:[wants], inf:fin, num:sg]).
lexEntry(tiv,[symbol:want, syntax:[want], inf:fin, num:pl]).

lexEntry(tiv,[symbol:seek, syntax:[seek], inf:inf, num:_]).
lexEntry(tiv,[symbol:seek, syntax:[seeks], inf:fin, num:sg]).
lexEntry(tiv,[symbol:seek, syntax:[seek], inf:fin, num:pl]).

%lexEntry(ecmv,[symbol:seeECM, syntax:[see], inf:inf, num:_]).
%lexEntry(ecmv,[symbol:seeECM, syntax:[sees], inf:fin, num:sg]).
%lexEntry(ecmv,[symbol:seeECM, syntax:[see], inf:fin, num:pl]).
%lexEntry(ecmv,[symbol:seeECM, syntax:[saw], inf:fin, num:_]).

lexEntry(vpv,[symbol:manageto,syntax:[managed,to],inf:fin,num:_]).

/*========================================================================
   Copula
========================================================================*/

lexEntry(cop,[pol:pos,syntax:[is],inf:fin,num:sg]).
lexEntry(cop,[pol:neg,syntax:[is,not],inf:fin,num:sg]).
lexEntry(cop,[pol:pos,syntax:[are],inf:fin,num:pl]).
lexEntry(cop,[pol:neg,syntax:[are,not],inf:fin,num:pl]).


/*========================================================================
   Prepositions
========================================================================*/

lexEntry(prep,[symbol:about,syntax:[about]]).
lexEntry(prep,[symbol:in,syntax:[in]]).
lexEntry(prep,[symbol:of,syntax:[of]]).
lexEntry(prep,[symbol:with,syntax:[with]]).


/*========================================================================
   Adjectives
========================================================================*/

lexEntry(adj,[symbol:big,type:intersective,syntax:[big]]).
lexEntry(adj,[symbol:blue,type:intersective,syntax:[blue]]).
lexEntry(adj,[symbol:female,type:intersective,syntax:[female]]).
lexEntry(adj,[symbol:happy,type:intersective,syntax:[happy]]).
lexEntry(adj,[symbol:kahuna,type:intersective,syntax:[kahuna]]).
lexEntry(adj,[symbol:male,type:intersective,syntax:[male]]).
lexEntry(adj,[symbol:married,type:intersective,syntax:[married]]).
lexEntry(adj,[symbol:red,type:intersective,syntax:[red]]).
lexEntry(adj,[symbol:sad,type:intersective,syntax:[sad]]).
lexEntry(adj,[symbol:small,type:subsective,syntax:[small]]).
lexEntry(adj,[symbol:tall,type:intersective,syntax:[tall]]).
lexEntry(adj,[symbol:large,type:subsective,syntax:[large]]).
lexEntry(adj,[symbol:fat,type:intersective,syntax:[fat]]).
lexEntry(adj,[symbol:fourlegged,type:intersective,syntax:[four-legged]]).

lexEntry(adj,[symbol:successful,type:subsective,syntax:[successful]]).
lexEntry(adj,[symbol:skillful,type:subsective,syntax:[skillful]]).
lexEntry(adj,[symbol:clever,type:subsective,syntax:[clever]]).
lexEntry(adj,[symbol:competent,type:subsective,syntax:[competent]]).

lexEntry(adj,[symbol:fake,type:intensional,syntax:[fake]]). %mhahn
lexEntry(adj,[symbol:alleged,type:intensional,syntax:[alleged]]).
lexEntry(adj,[symbol:genuine,type:intensional,syntax:[genuine]]).
lexEntry(adj,[symbol:former,type:intensional,syntax:[former]]).

/*========================================================================
   Relative Pronouns
========================================================================*/

lexEntry(relpro,[syntax:[who]]).
lexEntry(relpro,[syntax:[that]]).


/*========================================================================
   Coordinations
========================================================================*/

lexEntry(coord,[syntax:[and],type:conj]).
lexEntry(coord,[syntax:[or],type:disj]).


/*========================================================================
   Auxiliary Verbs
========================================================================*/

lexEntry(av,[syntax:[does],inf:fin,num:sg,pol:pos]).
lexEntry(av,[syntax:[does,not],inf:fin,num:sg,pol:neg]).
lexEntry(av,[syntax:[did],inf:fin,num:sg,pol:pos]).
lexEntry(av,[syntax:[did,not],inf:fin,num:sg,pol:neg]).



/*========================================================================
    Adverbs (mhahn)
========================================================================*/

lexEntry(adv,[symbol:necessarily,syntax:[necessarily]]).
lexEntry(adv,[symbol:possibly,syntax:[possibly]]).
lexEntry(adv,[symbol:allegedly,syntax:[allegedly]]).
lexEntry(adv,[symbol:really,syntax:[really]]).


hoi:lexEntry(adj,[symbol:greatest,type:subsective,syntax:[greatest]]).
hoi:lexEntry(noun,[symbol:tenor,syntax:[tenor]]).
hoi:lexEntry(prep,[symbol:to,syntax:[to]]).
hoi:lexEntry(adj,[symbol:great,type:subsective,syntax:[great]]).
hoi:lexEntry(noun,[symbol:man,syntax:[men]]).
hoi:lexEntry(noun,[symbol:tenor,syntax:[tenors]]).
hoi:lexEntry(adj,[symbol:ambitious,type:subsective,syntax:[ambitious]]).
hoi:lexEntry(adj,[symbol:swedish,type:intersective,syntax:[swedish]]).
hoi:lexEntry(adj,[symbol:italian,type:intersective,syntax:[italian]]).
hoi:lexEntry(adj,[symbol:german,type:intersective,syntax:[german]]).
hoi:lexEntry(adj,[symbol:british,type:intersective,syntax:[british]]).
hoi:lexEntry(iv,[symbol:sing,syntax:[sing],inf:_G520,num:_G526]).
hoi:lexEntry(adj,[symbol:popular,type:subsective,syntax:[popular]]).
hoi:lexEntry(noun,[symbol:music,syntax:[music]]).
hoi:lexEntry(adj,[symbol:leading,type:subsective,syntax:[leading]]).
hoi:lexEntry(adj,[symbol:excellent,type:subsective,syntax:[excellent]]).
hoi:lexEntry(adj,[symbol:indispensable,type:subsective,syntax:[indispensable]]).
hoi:lexEntry(prep,[symbol:at,syntax:[at]]).
hoi:lexEntry(tv,[symbol:take,syntax:[take],inf:_G490,num:_G496]).
hoi:lexEntry(noun,[symbol:concert,syntax:[concert]]).
hoi:lexEntry(noun,[symbol:irishman,syntax:[irishman]]).
hoi:lexEntry(prep,[symbol:for,syntax:[for]]).
hoi:lexEntry(adj,[symbol:european,type:subsective,syntax:[european]]).
hoi:lexEntry(adj,[symbol:right,type:subsective,syntax:[right]]).
hoi:lexEntry(iv,[symbol:live,syntax:[live],inf:_G655,num:_G661]).
hoi:lexEntry(pn,[symbol:europe,syntax:[europe]]).
hoi:lexEntry(iv,[symbol:travel,syntax:[travel],inf:_G1083,num:_G1089]).
hoi:lexEntry(noun,[symbol:european,syntax:[europeans]]).
hoi:lexEntry(noun,[symbol:resident,syntax:[residents]]).
hoi:lexEntry(noun,[symbol:member,syntax:[member]]).
hoi:lexEntry(noun,[symbol:individual,syntax:[individuals]]).
hoi:lexEntry(noun,[symbol:individual,syntax:[individual]]).
hoi:lexEntry(noun,[symbol:resident,syntax:[resident]]).
hoi:lexEntry(noun,[symbol:people,syntax:[people]]).
hoi:lexEntry(noun,[symbol:comittee,syntax:[committee]]).
hoi:lexEntry(prep,[symbol:from,syntax:[from]]).
hoi:lexEntry(pn,[symbol:sweden,syntax:[sweden]]).
hoi:lexEntry(pn,[symbol:scandinavia,syntax:[scandinavia]]).
hoi:lexEntry(noun,[symbol:commissioner,syntax:[commissioners]]).
hoi:lexEntry(noun,[symbol:businessman,syntax:[businessmen]]).
hoi:lexEntry(pn,[symbol:portugal,syntax:[portugal]]).
hoi:lexEntry(tv,[symbol:spend,syntax:[spend],inf:_G504,num:_G510]).
hoi:lexEntry(noun,[symbol:time,syntax:[time]]).
hoi:lexEntry(noun,[symbol:home,syntax:[home]]).
hoi:lexEntry(noun,[symbol:swede,syntax:[swede]]).
hoi:lexEntry(adj,[symbol:scandinavian,type:subsective,syntax:[scandinavian]]).
hoi:lexEntry(adj,[symbol:irish,type:subsective,syntax:[irish]]).
hoi:lexEntry(noun,[symbol:delegate,syntax:[delegates]]).
hoi:lexEntry(tv,[symbol:finish,syntax:[finished],inf:_G478,num:_G484]).
hoi:lexEntry(noun,[symbol:survey,syntax:[survey]]).
hoi:lexEntry(prep,[symbol:on,syntax:[on]]).
hoi:lexEntry(adj,[symbol:portuguese,type:subsective,syntax:[portuguese]]).
hoi:lexEntry(tv,[symbol:get,syntax:[got],inf:_G493,num:_G499]).
hoi:lexEntry(noun,[symbol:result,syntax:[results]]).
hoi:lexEntry(tv,[symbol:publish,syntax:[published],inf:_G571,num:_G577]).
hoi:lexEntry(adj,[symbol:major,type:subsective,syntax:[major]]).
hoi:lexEntry(adj,[symbol:national,type:subsective,syntax:[national]]).
hoi:lexEntry(noun,[symbol:newspaper,syntax:[newspapers]]).
hoi:lexEntry(adj,[symbol:north,type:subsective,syntax:[north]]).
hoi:lexEntry(adj,[symbol:american,type:subsective,syntax:[american]]).
hoi:lexEntry(noun,[symbol:continent,syntax:[continent]]).
hoi:lexEntry(adj,[symbol:canadian,type:subsective,syntax:[canadian]]).
hoi:lexEntry(noun,[symbol:country,syntax:[countries]]).
hoi:lexEntry(adj,[symbol:modest,type:subsective,syntax:[modest]]).
hoi:lexEntry(adj,[symbol:poor,type:subsective,syntax:[poor]]).
hoi:lexEntry(iv,[symbol:come,syntax:[comes],inf:_G498,num:_G504]).
hoi:lexEntry(adj,[symbol:cheap,type:subsective,syntax:[cheap]]).
hoi:lexEntry(pn,[symbol:pavarotti,syntax:[pavarotti]]).
hoi:lexEntry(iv,[symbol:contribute,syntax:[contribute],inf:_G532,num:_G538]).
hoi:lexEntry(noun,[symbol:fee,syntax:[fees]]).
hoi:lexEntry(noun,[symbol:charity,syntax:[charity]]).
hoi:lexEntry(tv,[symbol:obtain,syntax:[obtained],inf:_G451,num:_G457]).
hoi:lexEntry(adj,[symbol:interesting,type:subsective,syntax:[interesting]]).
hoi:lexEntry(adv,[symbol:anywhere,syntax:[anywhere]]).
hoi:lexEntry(noun,[symbol:delegate,syntax:[delegate]]).
hoi:lexEntry(noun,[symbol:report,syntax:[report]]).
hoi:lexEntry(noun,[symbol:commissioner,syntax:[commissioner]]).
hoi:lexEntry(tv,[symbol:spend,syntax:[spends],inf:_G460,num:_G466]).
hoi:lexEntry(noun,[symbol:business,syntax:[business]]).
hoi:lexEntry(prep,[symbol:outside,syntax:[outside]]).
hoi:lexEntry(noun,[symbol:diamond,syntax:[diamond]]).
hoi:lexEntry(noun,[symbol:university,syntax:[university]]).
hoi:lexEntry(noun,[symbol:student,syntax:[student]]).
hoi:lexEntry(adj,[symbol:fourLegged,type:subsective,syntax:[four-legged]]).
hoi:lexEntry(pn,[symbol:mickey,syntax:[mickey]]).
hoi:lexEntry(pn,[symbol:bill,syntax:[bill]]).
hoi:lexEntry(pn,[symbol:fido,syntax:[fido]]).
hoi:lexEntry(pn,[symbol:1992,syntax:[1992]]).
hoi:lexEntry(tv,[symbol:win,syntax:[win],inf:_G465,num:_G471]).
hoi:lexEntry(noun,[symbol:chairman,syntax:[chairman]]).
hoi:lexEntry(pn,[symbol:helen,syntax:[helen]]).
hoi:lexEntry(noun,[symbol:department,syntax:[department]]).
hoi:lexEntry(tv,[symbol:answer,syntax:[answer],inf:_G628,num:_G634]).
hoi:lexEntry(noun,[symbol:secretary,syntax:[secretary]]).
hoi:lexEntry(tv,[symbol:make,syntax:[make],inf:_G618,num:_G624]).
hoi:lexEntry(adj,[symbol:crucial,type:subsective,syntax:[crucial]]).
hoi:lexEntry(noun,[symbol:clause,syntax:[clause]]).
hoi:lexEntry(noun,[symbol:heart,syntax:[heart]]).
hoi:lexEntry(iv,[symbol:beat,syntax:[beat],inf:_G759,num:_G765]).
