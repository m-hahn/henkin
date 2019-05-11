/*************************************************************************

    File: fracas.pl
    Copyright (C) 2015 Michael Hahn

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de
    
    This file contains a Prolog representation of the FraCaS testsuite as
    adapted by Bill MacCartney, downloaded September 17, 2015 from
       http://nlp.stanford.edu/~wcmac/downloads/

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


:- dynamic(skipWord/1).


/*========================================================================
   Interactively complete the lexicon to cover the FraCaS items.
========================================================================*/


completeLexicon(Section) :-
      open('lexfracas.pl', write, Stream),
      forall(fracasSentence(Section,_,_,Premises,Hyp),(completeLexicon(Premises,Stream),completeLexicon([Hyp],Stream))),
      close(Stream).

completeLexicon([],_).
completeLexicon([A|T],S) :-
      completeLexiconSent(A,S),
      completeLexicon(T,S).

completeLexiconSent([],_).
completeLexiconSent([A|T],S) :-
      hoi:lexEntry(_,Feats),
      comsemPredicates:getFeatureValue(Feats,syntax,[A]),!,
      completeLexiconSent(T,S).
completeLexiconSent([A|T],S) :-
      skipWord(A),
      completeLexiconSent(T,S).
completeLexiconSent([A|T],S) :-
      write(A),nl,
      read(B),
      process(A,B,S,T).

process(_,quit,S,_) :- close(S).
process(A,noun,S,T) :-
      write('symbol ' ),nl,read(Sym),
      add(S,hoi:lexEntry(noun,[symbol:Sym,syntax:[A]])),
      completeLexiconSent(T,S).
process(A,pn,S,T) :-
      add(S,hoi:lexEntry(pn,[symbol:A,syntax:[A]])),
      completeLexiconSent(T,S).
process(A,iv,S,T) :-
      write('symbol ' ),nl,read(Sym),
      add(S,hoi:lexEntry(iv,[symbol:Sym,syntax:[A],inf:_,num:_])),
      completeLexiconSent(T,S).
process(A,tv,S,T) :-
      write('symbol ' ),nl,read(Sym),
      add(S,hoi:lexEntry(tv,[symbol:Sym,syntax:[A],inf:_,num:_])),
      completeLexiconSent(T,S).
process(A,prep,S,T) :-
      add(S,hoi:lexEntry(prep,[symbol:A,syntax:[A]])),
      completeLexiconSent(T,S).
process(A,adv,S,T) :-
      add(S,hoi:lexEntry(adv,[symbol:A,syntax:[A]])),
      completeLexiconSent(T,S).
process(A,adj,S,T) :-
      write('type '),nl,read(Type),
      add(S,hoi:lexEntry(adj,[symbol:A,type:Type,syntax:[A]])),
      completeLexiconSent(T,S).
process(A,_,S,T) :-
      write('Skip!'),nl,
      asserta(skipWord(A)),
      completeLexiconSent(T,S).


add(S,A) :-
     write(S,A),write(S,'.\n'),asserta(A).



/*========================================================================
   Process a test item and generate its FO translation
========================================================================*/



fracasTestItemFO(A,B,C,D-E,HO,FO-FONeg) :-
      fracasTestItem(A,B,C,D-E,HO-HONeg),
      betaConversion:instantiateTypes(HO),
      hoi:translateWithAxioms(HO,FO),
      hoi:translateWithAxioms(HONeg,FONeg).

fracasTestItem(A,B,C,D-E,Result-ResultNeg) :-
      fracasSentence(A,B,C2,D,E),
      hoi:lambdaHOI(E,[Hyp|_]),
      hoi:lambdaHOIList(D,Prem),
      hoi:buildImplicationTerm(Prem,Hyp,Result),
      hoi:buildImplicationTerm(Prem,(@((not,t>t),Hyp),t),ResultNeg),
      member((C2,C),[(unknown,contingent),(yes,valid),(no,contradictory)]).



fracasSentence(Section,Id,Status,Premises,Hyp) :-
      fracasSentence2(Section,Id,Status,Premises2,Hyp2),
      tokenizeList(Premises2,Premises),
      tokenizeList([Hyp2],[Hyp]).

tokenizeList([],[]).
tokenizeList([A|T],[A2|T2]) :-
      downcase_atom(A,A1),
      atomic_list_concat(A2,' ', A1),
      tokenizeList(T,T2).

fracasSentence2(Section,Id,Status,Premise,Hyp) :-
     fracasProblem(id=Id,answer=Status,p=Premise,h=Hyp),
     section(Section,_,From-To), From =< Id, Id =< To.

/*========================================================================
   The FraCaS testsuite as adapted by MacCartney
========================================================================*/



section(1,'GENERALIZED QUANTIFIERS',1-80).
section(2,'PLURALS ',81-113).
section(3,'(NOMINAL) ANAPHORA ',114-141).
section(4,'ELLIPSIS ',142-196).
section(5,'ADJECTIVES ',197-219).
section(6,'COMPARATIVES ',220-250).
section(7,'TEMPORAL REFERENCE',251-325).
section(8,'VERBS ',326-333).
section(9,'ATTITUDES ',334-346).


fracasProblem(id=ID, answer=ANSWER, p=Premises, h=Hypothesis) :-
    fracasProblem(id=ID,fracas_answer=ANSWER, p=Premises, q=_, h=Hypothesis);
    fracasProblem(id=ID,fracas_answer=ANSWER, p=Premises, q=_, h=Hypothesis,_);
    fracasProblem(id=ID,fracas_answer=ANSWER, p=Premises, q=_, h=Hypothesis,_,_);
    fracasProblem(id=ID,fracas_answer=ANSWER, p=Premises, q=_, h=Hypothesis,_,_,_);
    fracasProblem(id=ID,fracas_answer=_, my_answer = ANSWER, p=Premises, q=_, h=Hypothesis);
    fracasProblem(id=ID,fracas_answer=_, my_answer = ANSWER, p=Premises, q=_, h=Hypothesis,_);
    fracasProblem(id=ID,fracas_answer=_, my_answer = ANSWER, p=Premises, q=_, h=Hypothesis,_,_);
    fracasProblem(id=ID,fracas_answer=_, my_answer = ANSWER, p=Premises, q=_, h=Hypothesis,_,_,_).




/*<comment class=section> 1 GENERALIZED QUANTIFIERS </comment>*/
 

/*<comment class=subsection> 11 Conservativity </comment>*/
 

/*<comment> Q As are Bs == Q As are As who are Bs </comment>*/
 

fracasProblem(id=001, fracas_answer=yes, p=['An Italian became the world \'s greatest tenor'], q='Was there an Italian who became the world \'s greatest tenor?', h='There was an Italian who became the world \'s greatest tenor').
fracasProblem(id=002, fracas_answer=yes, p=['Every Italian man wants to be a great tenor',  'Some Italian men are great tenors'], q='Are there Italian men who want to be a great tenor?', h='There are Italian men who want to be a great tenor' ).
fracasProblem(id=003, fracas_answer=yes, p=['All Italian men want to be a great tenor',  'Some Italian men are great tenors'], q='Are there Italian men who want to be a great tenor?', h='There are Italian men who want to be a great tenor' ).
fracasProblem(id=004, fracas_answer=yes, p=['Each Italian tenor wants to be great',  'Some Italian tenors are great'], q='Are there Italian tenors who want to be great?', h='There are Italian tenors who want to be great' ).
fracasProblem(id=005, fracas_answer=yes, p=['The really ambitious tenors are Italian'], q='Are there really ambitious tenors who are Italian?', h='There are really ambitious tenors who are Italian').
fracasProblem(id=006, fracas_answer=no, p=['No really great tenors are modest'], q='Are there really great tenors who are modest?', h='There are really great tenors who are modest', a='No').
fracasProblem(id=007, fracas_answer=yes, p=['Some great tenors are Swedish'], q='Are there great tenors who are Swedish?', h='There are great tenors who are Swedish').
fracasProblem(id=008, fracas_answer=yes, p=['Many great tenors are German'], q='Are there great tenors who are German?', h='There are great tenors who are German').
fracasProblem(id=009, fracas_answer=yes, p=['Several great tenors are British'], q='Are there great tenors who are British?', h='There are great tenors who are British').
fracasProblem(id=010, fracas_answer=yes, p=['Most great tenors are Italian'], q='Are there great tenors who are Italian?', h='There are great tenors who are Italian').
fracasProblem(id=011, fracas_answer=yes, p=['A few great tenors sing popular music',  'Some great tenors like popular music'], q='Are there great tenors who sing popular music?', h='There are great tenors who sing popular music' ).

fracasProblem(id=012, fracas_answer=undef, p=['Few great tenors are poor'], q='Are there great tenors who are poor?', h='There are great tenors who are poor', a='Not many').
fracasProblem(id=013, fracas_answer=yes, p=['Both leading tenors are excellent',  'Leading tenors who are excellent are indispensable'], q='Are both leading tenors indispensable?', h='Both leading tenors are indispensable').
fracasProblem(id=014, fracas_answer=no, p=['Neither leading tenor comes cheap',  'One of the leading tenors is Pavarotti'], q='Is Pavarotti a leading tenor who comes cheap?', h='Pavarotti is a leading tenor who comes cheap', a='No').
fracasProblem(id=015, fracas_answer=yes, p=['At least three tenors will take part in the concert'], q='Are there tenors who will take part in the concert?', h='There are tenors who will take part in the concert').
fracasProblem(id=016, fracas_answer=undef, p=['At most two tenors will contribute their fees to charity'], q='Are there tenors who will contribute their fees to charity?', h='There are tenors who will contribute their fees to charity', a='At most two').






/*fracasProblem(id=0001, fracas_answer=yes, p=['An Italian became the world \'s greatest tenor'], q='Was there an Italian became the world \'s greatest tenor?', h='An Italian became the world \'s greatest tenor').
fracasProblem(id=0002, fracas_answer=yes, p=['Every Italian man wants to be a great tenor',  'Some Italian men are great tenors'], q='Are there Italian men want to be a great tenor?', h='Some Italian men want to be a great tenor' ).
fracasProblem(id=0003, fracas_answer=yes, p=['All Italian men want to be a great tenor',  'Some Italian men are great tenors'], q='Are there Italian men want to be a great tenor?', h='Some Italian men want to be a great tenor' ).
fracasProblem(id=0004, fracas_answer=yes, p=['Each Italian tenor wants to be great',  'Some Italian tenors are great'], q='Are there Italian tenors want to be great?', h='Some Italian tenors want to be great' ).
fracasProblem(id=0005, fracas_answer=yes, p=['The really ambitious tenors are Italian'], q='Are there really ambitious tenors are Italian?', h='Some really ambitious tenors are Italian').
fracasProblem(id=0006, fracas_answer=no, p=['No really great tenors are modest'], q='Are there really great tenors are modest?', h='Some really great tenors are modest', a='No').
fracasProblem(id=0007, fracas_answer=yes, p=['Some great tenors are Swedish'], q='Are there great tenors are Swedish?', h='Some great tenors are Swedish').
fracasProblem(id=0008, fracas_answer=yes, p=['Many great tenors are German'], q='Are there great tenors are German?', h='Some great tenors are German').
fracasProblem(id=0009, fracas_answer=yes, p=['Several great tenors are British'], q='Are there great tenors are British?', h='Some great tenors are British').
fracasProblem(id=0010, fracas_answer=yes, p=['Most great tenors are Italian'], q='Are there great tenors are Italian?', h='Some great tenors are Italian').
fracasProblem(id=0011, fracas_answer=yes, p=['A few great tenors sing popular music',  'Some great tenors like popular music'], q='Are there great tenors sing popular music?', h='Some great tenors sing popular music' ).

fracasProblem(id=0012, fracas_answer=undef, p=['Few great tenors are poor'], q='Are there great tenors are poor?', h='Some great tenors are poor', a='Not many').
fracasProblem(id=0013, fracas_answer=yes, p=['Both leading tenors are excellent',  'Leading tenors are excellent are indispensable'], q='Are both leading tenors indispensable?', h='Both leading tenors are indispensable').
fracasProblem(id=0014, fracas_answer=no, p=['Neither leading tenor comes cheap',  'One of the leading tenors is Pavarotti'], q='Is Pavarotti a leading tenor comes cheap?', h='Pavarotti is a leading tenor comes cheap', a='No').
fracasProblem(id=0015, fracas_answer=yes, p=['At least three tenors will take part in the concert'], q='Are there tenors will take part in the concert?', h='Some tenors will take part in the concert').
fracasProblem(id=0016, fracas_answer=undef, p=['At most two tenors will contribute their fees to charity'], q='Are there tenors will contribute their fees to charity?', h='Some tenors will contribute their fees to charity', a='At most two').*/



/*<comment class=subsection> 12 Monotonicity (upwards on second argument) </comment>*/
 

/*<comment> Q As are Bs and all Bs are Cs &lt; Q As are Cs </comment>*/
 
fracasProblem(id=017, fracas_answer=yes, p=['An Irishman won the Nobel prize for literature'], q='Did an Irishman win a Nobel prize?', h='An Irishman won a Nobel prize').
fracasProblem(id=018, fracas_answer=yes, p=['Every European has the right to live in Europe',  'Every European is a person',  'Every person who has the right to live in Europe can travel freely within Europe'], q='Can every European travel freely within Europe?', h='Every European can travel freely within Europe').
fracasProblem(id=019, fracas_answer=yes, p=['All Europeans have the right to live in Europe',  'Every European is a person',  'Every person who has the right to live in Europe can travel freely within Europe'], q='Can all Europeans travel freely within Europe?', h='All Europeans can travel freely within Europe').
fracasProblem(id=020, fracas_answer=yes, p=['Each European has the right to live in Europe',  'Every European is a person',  'Every person who has the right to live in Europe can travel freely within Europe'], q='Can each European travel freely within Europe?', h='Each European can travel freely within Europe').
fracasProblem(id=021, fracas_answer=yes, p=['The residents of member states have the right to live in Europe',  'All residents of member states are individuals',  'Every individual who has the right to live in Europe can travel freely within Europe'], q='Can the residents of member states travel freely within Europe?', h='The residents of member states can travel freely within Europe').
fracasProblem(id=022, fracas_answer=unknown, p=['No delegate finished the report on time'], q='Did no delegate finish the report?', h='No delegate finished the report', a='don\'t know', why='can\'t drop adjunct in negative context').
fracasProblem(id=023, fracas_answer=yes, my_answer=unknown, p=['Some delegates finished the survey on time'], q='Did some delegates finish the survey?', h='Some delegates finished the survey', why='OK to drop adjunct in positive context').
fracasProblem(id=024, fracas_answer=yes, p=['Many delegates obtained interesting results from the survey'], q='Did many delegates obtain results from the survey?', h='Many delegates obtained results from the survey', why='OK to drop adjunct in positive context').
fracasProblem(id=025, fracas_answer=yes, p=['Several delegates got the results published in major national newspapers'], q='Did several delegates get the results published?', h='Several delegates got the results published', why='OK to drop adjunct in positive context').
fracasProblem(id=026, fracas_answer=yes, p=['Most Europeans are resident in Europe',  'All Europeans are people',  'All people who are resident in Europe can travel freely within Europe'], q='Can most Europeans travel freely within Europe?', h='Most Europeans can travel freely within Europe').
fracasProblem(id=027, fracas_answer=yes, p=['A few committee members are from Sweden',  'All committee members are people',  'All people who are from Sweden are from Scandinavia'], q='Are at least a few committee members from Scandinavia?', h='At least a few committee members are from Scandinavia').
fracasProblem(id=028, fracas_answer=unknown, p=['Few committee members are from Portugal',  'All committee members are people',  'All people who are from Portugal are from southern Europe'], q='Are there few committee members from southern Europe?', h='There are few committee members from southern Europe', a='don\'t know').
fracasProblem(id=029, fracas_answer=yes, p=['Both commissioners used to be leading businessmen'], q='Did both commissioners used to be businessmen?', h='Both commissioners used to be businessmen').
fracasProblem(id=030, fracas_answer=unknown, p=['Neither commissioner spends a lot of time at home'], q='Does neither commissioner spend time at home?', h='Neither commissioner spends time at home', a='don\'t know', why='Not OK to drop [qualifier] in negative context').
fracasProblem(id=031, fracas_answer=yes, p=['At least three commissioners spend a lot of time at home'], q='Do at least three commissioners spend time at home?', h='At least three commissioners spend time at home', note='Typo in original problem: premise was A least three').
fracasProblem(id=032, fracas_answer=unknown, p=['At most ten commissioners spend a lot of time at home'], q='Do at most ten commissioners spend time at home?', h='At most ten commissioners spend time at home', a='don\'t know').


/*<comment class=subsection> 13 Monotonicity (downwards on second argument) </comment>*/
 

/*<comment> Q As are Bs and all Cs are Bs &lt; Q As are Cs </comment>*/
 
fracasProblem(id=033, fracas_answer=unknown, p=['An Irishman won a Nobel prize'], q='Did an Irishman win the Nobel prize for literature?', h='An Irishman won the Nobel prize for literature', a='don\'t know').
fracasProblem(id=034, fracas_answer=unknown, p=['Every European can travel freely within Europe',  'Every European is a person',  'Every person who has the right to live in Europe can travel freely within Europe'], q='Does every European have the right to live in Europe?', h='Every European has the right to live in Europe', a='don\'t know').
fracasProblem(id=035, fracas_answer=unknown, p=['All Europeans can travel freely within Europe',  'Every European is a person',  'Every person who has the right to live in Europe can travel freely within Europe'], q='Do all Europeans have the right to live in Europe?', h='All Europeans have the right to live in Europe', a='don\'t know').
fracasProblem(id=036, fracas_answer=unknown, p=['Each European can travel freely within Europe',  'Every European is a person',  'Every person who has the right to live in Europe can travel freely within Europe'], q='Does each European have the right to live in Europe?', h='Each European has the right to live in Europe', a='don\'t know').
fracasProblem(id=037, fracas_answer=unknown, p=['The residents of member states can travel freely within Europe',  'All residents of member states are individuals',  'Every individual who has the right to live anywhere in Europe can travel freely within Europe'], q='Do the residents of member states have the right to live anywhere in Europe?', h='The residents of member states have the right to live anywhere in Europe', a='don\'t know').
fracasProblem(id=038, fracas_answer=no, my_answer=unknown, p=['No delegate finished the report'], q='Did any delegate finish the report on time?', h='Some delegate finished the report on time', a='No').
fracasProblem(id=039, fracas_answer=unknown, p=['Some delegates finished the survey'], q='Did some delegates finish the survey on time?', h='Some delegates finished the survey on time', a='don\'t know').
fracasProblem(id=040, fracas_answer=unknown, p=['Many delegates obtained results from the survey'], q='Did many delegates obtain interesting results from the survey?', h='Many delegates obtained interesting results from the survey', a='don\'t know').
fracasProblem(id=041, fracas_answer=unknown, p=['Several delegates got the results published'], q='Did several delegates get the results published in major national newspapers?', h='Several delegates got the results published in major national newspapers', a='don\'t know').
fracasProblem(id=042, fracas_answer=unknown, p=['Most Europeans can travel freely within Europe',  'All Europeans are people',  'All people who are resident in Europe can travel freely within Europe'], q='Are most Europeans resident in Europe?', h='Most Europeans are resident in Europe', a='don\'t know').
fracasProblem(id=043, fracas_answer=unknown, p=['A few committee members are from Scandinavia',  'All committee members are people',  'All people who are from Sweden are from Scandinavia'], q='Are at least a few committee members from Sweden?', h='At least a few committee members are from Sweden', a='don\'t know').
fracasProblem(id=044, fracas_answer=yes, p=['Few committee members are from southern Europe',  'All committee members are people',  'All people who are from Portugal are from southern Europe'], q='Are there few committee members from Portugal?', h='There are few committee members from Portugal').
fracasProblem(id=045, fracas_answer=unknown, p=['Both commissioners used to be businessmen'], q='Did both commissioners used to be leading businessmen?', h='Both commissioners used to be leading businessmen', a='don\'t know').
fracasProblem(id=046, fracas_answer=no, p=['Neither commissioner spends time at home'], q='Does either commissioner spend a lot of time at home?', h='One of the commissioners spends a lot of time at home', a='No').
fracasProblem(id=047, fracas_answer=unknown, p=['At least three commissioners spend time at home'], q='Do at least three commissioners spend a lot of time at home?', h='At least three commissioners spend a lot of time at home', a='don\'t know', note='Typo in original problem: premise was A least three').
fracasProblem(id=048, fracas_answer=yes, p=['At most ten commissioners spend time at home'], q='Do at most ten commissioners spend a lot of time at home?', h='At most ten commissioners spend a lot of time at home').

/*<comment class=subsection> 14 Monotonicity (upwards on first argument) </comment>*/
 

/*<comment> Q As are Bs and all As are Cs &lt; Q Cs are Bs </comment>*/
 
fracasProblem(id=049, fracas_answer=yes, p=['A Swede won a Nobel prize',  'Every Swede is a Scandinavian'], q='Did a Scandinavian win a Nobel prize?', h='A Scandinavian won a Nobel prize').
fracasProblem(id=050, fracas_answer=unknown, p=['Every Canadian resident can travel freely within Europe',  'Every Canadian resident is a resident of the North American continent'], q='Can every resident of the North American continent travel freely within Europe?', h='Every resident of the North American continent can travel freely within Europe', a='don\'t know').
fracasProblem(id=051, fracas_answer=unknown, p=['All Canadian residents can travel freely within Europe',  'Every Canadian resident is a resident of the North American continent'], q='Can all residents of the North American continent travel freely within Europe?', h='All residents of the North American continent can travel freely within Europe', a='don\'t know').
fracasProblem(id=052, fracas_answer=unknown, p=['Each Canadian resident can travel freely within Europe',  'Every Canadian resident is a resident of the North American continent'], q='Can each resident of the North American continent travel freely within Europe?', h='Each resident of the North American continent can travel freely within Europe', a='don\'t know').
fracasProblem(id=053, fracas_answer=unknown, p=['The residents of major western countries can travel freely within Europe',  'All residents of major western countries are residents of western countries'], q='Do the residents of western countries have the right to live in Europe?', h='The residents of western countries have the right to live in Europe', a='don\'t know').
fracasProblem(id=054, fracas_answer=unknown, p=['No Scandinavian delegate finished the report on time'], q='Did any delegate finish the report on time?', h='Some delegate finished the report on time', a='don\'t know').
fracasProblem(id=055, fracas_answer=yes, p=['Some Irish delegates finished the survey on time'], q='Did any delegates finish the survey on time?', h='Some delegates finished the survey on time').
fracasProblem(id=056, fracas_answer=unknown, p=['Many British delegates obtained interesting results from the survey'], q='Did many delegates obtain interesting results from the survey?', h='Many delegates obtained interesting results from the survey', a='don\'t know').
fracasProblem(id=057, fracas_answer=yes, p=['Several Portuguese delegates got the results published in major national newspapers'], q='Did several delegates get the results published in major national newspapers?', h='Several delegates got the results published in major national newspapers').
fracasProblem(id=058, fracas_answer=unknown, p=['Most Europeans who are resident in Europe can travel freely within Europe'], q='Can most Europeans travel freely within Europe?', h='Most Europeans can travel freely within Europe', a='don\'t know').
fracasProblem(id=059, fracas_answer=yes, p=['A few female committee members are from Scandinavia'], q='Are at least a few committee members from Scandinavia?', h='At least a few committee members are from Scandinavia').
fracasProblem(id=060, fracas_answer=unknown, p=['Few female committee members are from southern Europe'], q='Are few committee members from southern Europe?', h='Few committee members are from southern Europe', a='don\'t know', note='Note that this problem is exactly the inverse of problem fracas-76').
fracasProblem(id=061, fracas_answer=undef, p=['Both female commissioners used to be in business'], q='Did both commissioners used to be in business?', h='Both commissioners used to be in business', a='Yes, if both commissioners are female; otherwise there are more than two commissioners').
fracasProblem(id=062, fracas_answer=undef, p=['Neither female commissioner spends a lot of time at home'], q='Does either commissioner spend a lot of time at home?', h='One of the commissioners spends a lot of time at home', a='No, if both commissioners are female; otherwise there are more than two commissioners').
fracasProblem(id=063, fracas_answer=yes, p=['At least three female commissioners spend time at home'], q='Do at least three commissioners spend time at home?', h='At least three commissioners spend time at home', note='Typo in original problem: premise was A least three').
fracasProblem(id=064, fracas_answer=unknown, p=['At most ten female commissioners spend time at home'], q='Do at most ten commissioners spend time at home?', h='At most ten commissioners spend time at home', a='don\'t know').

/*<comment class=subsection> 15 Monotonicity (downwards on first argument) </comment>*/
 

/*<comment> Q As are Bs and all Cs are As &lt; Q Cs are Bs </comment>*/
 
fracasProblem(id=065, fracas_answer=unknown, p=['A Scandinavian won a Nobel prize',  'Every Swede is a Scandinavian'], q='Did a Swede win a Nobel prize?', h='A Swede won a Nobel prize', a='don\'t know').
fracasProblem(id=066, fracas_answer=yes, p=['Every resident of the North American continent can travel freely within Europe',  'Every Canadian resident is a resident of the North American continent'], q='Can every Canadian resident travel freely within Europe?', h='Every Canadian resident can travel freely within Europe', note='NB: in the original, travel was missing from the question').
fracasProblem(id=067, fracas_answer=yes, p=['All residents of the North American continent can travel freely within Europe',  'Every Canadian resident is a resident of the North American continent'], q='Can all Canadian residents travel freely within Europe?', h='All Canadian residents can travel freely within Europe').
fracasProblem(id=068, fracas_answer=yes, p=['Each resident of the North American continent can travel freely within Europe',  'Every Canadian resident is a resident of the North American continent'], q='Can each Canadian resident travel freely within Europe?', h='Each Canadian resident can travel freely within Europe').
fracasProblem(id=069, fracas_answer=yes, p=['The residents of western countries can travel freely within Europe',  'All residents of major western countries are residents of western countries'], q='Do the residents of major western countries have the right to live in Europe?', h='The residents of major western countries have the right to live in Europe').
fracasProblem(id=070, fracas_answer=no, p=['No delegate finished the report on time'], q='Did any Scandinavian delegate finish the report on time?', h='Some Scandinavian delegate finished the report on time', a='No').
fracasProblem(id=071, fracas_answer=unknown, p=['Some delegates finished the survey on time'], q='Did any Irish delegates finish the survey on time?', h='Some Irish delegates finished the survey on time', a='don\'t know').
fracasProblem(id=072, fracas_answer=unknown, p=['Many delegates obtained interesting results from the survey'], q='Did many British delegates obtain interesting results from the survey?', h='Many British delegates obtained interesting results from the survey', a='don\'t know', note='Note that this problem is exactly the inverse of problem fracas-56').
fracasProblem(id=073, fracas_answer=unknown, p=['Several delegates got the results published in major national newspapers'], q='Did several Portuguese delegates get the results published in major national newspapers?', h='Several Portuguese delegates got the results published in major national newspapers', a='don\'t know').
fracasProblem(id=074, fracas_answer=unknown, p=['Most Europeans can travel freely within Europe'], q='Can most Europeans who are resident outside Europe travel freely within Europe?', h='Most Europeans who are resident outside Europe can travel freely within Europe', a='don\'t know').
fracasProblem(id=075, fracas_answer=unknown, p=['A few committee members are from Scandinavia'], q='Are at least a few female committee members from Scandinavia?', h='At least a few female committee members are from Scandinavia', a='don\'t know').
fracasProblem(id=076, fracas_answer=yes, p=['Few committee members are from southern Europe'], q='Are few female committee members from southern Europe?', h='Few female committee members are from southern Europe').
fracasProblem(id=077, fracas_answer=undef, p=['Both commissioners used to be in business'], q='Did both female commissioners used to be in business?', h='Both female commissioners used to be in business', a='Yes, if both commissioners are female; otherwise there are more than two commissioners').
fracasProblem(id=078, fracas_answer=undef, p=['Neither commissioner spends a lot of time at home'], q='Does either female commissioner spend a lot of time at home?', h='One of the female commissioners spends a lot of time at home', a='No, if both commissioners are female; otherwise there are more than two commissioners').
fracasProblem(id=079, fracas_answer=unknown, p=['At least three commissioners spend time at home'], q='Do at least three male commissioners spend time at home?', h='At least three male commissioners spend time at home', a='don\'t know', note='Typo in original problem: premise was A least three').
fracasProblem(id=080, fracas_answer=yes, p=['At most ten commissioners spend time at home'], q='Do at most ten female commissioners spend time at home?', h='At most ten female commissioners spend time at home').

/*<comment class=section> 2 PLURALS </comment>*/
 

/*<comment>A number of inferences pertaining to plurals are covered under the headings ofgeneralized quantifiers and elsewhere Here we concentrate on conjoined NPs;bare, existential and definite plurals; dependent plurals; and collective anddistributive readings and scope ambiguity </comment>*/
 

/*<comment class=subsection> 21 Conjoined Noun Phrases </comment>*/
 
fracasProblem(id=081, fracas_answer=yes, p=['Smith, Jones and Anderson signed the contract'], q='Did Jones sign the contract?', h='Jones signed the contract').
fracasProblem(id=082, fracas_answer=yes, p=['Smith, Jones and several lawyers signed the contract'], q='Did Jones sign the contract?', h='Jones signed the contract').
fracasProblem(id=083, fracas_answer=unknown, p=['Either Smith, Jones or Anderson signed the contract'], q='Did Jones sign the contract?', h='Jones signed the contract', a='don\'t know').
fracasProblem(id=084, fracas_answer=yes, p=['Either Smith, Jones or Anderson signed the contract'], q='If Smith and Anderson did not sign the contract, did Jones sign the contract?', h='If Smith and Anderson did not sign the contract, Jones signed the contract').
fracasProblem(id=085, fracas_answer=no, p=['Exactly two lawyers and three accountants signed the contract'], q='Did six lawyers sign the contract?', h='Six lawyers signed the contract', a='No', why='No scope relations between the two conjoined NPs').
fracasProblem(id=086, fracas_answer=no, p=['Exactly two lawyers and three accountants signed the contract'], q='Did six accountants sign the contract?', h='Six accountants signed the contract', a='No', why='No scope relations between the two conjoined NPs').

/*<comment> Conjoined Nbars </comment>*/
 

/*<comment>Nbar conjunction tends to be quite ambiguous This may be the result of asyntactic ambiguity between (i) genuine Nbar conjunction, and (ii) NPconjunction where the determiner of one of the NPs is ellided </comment>*/
 
fracasProblem(id=087, fracas_answer=yes, p=['Every representative and client was at the meeting'], q='Was every representative at the meeting?', h='Every representative was at the meeting', a='Yes, on one reading', why='Arguably NP conjunction: every representative and every client').
fracasProblem(id=088, fracas_answer=unknown, p=['Every representative and client was at the meeting'], q='Was every representative at the meeting?', h='Every representative was at the meeting', a='don\'t know, on one reading', why='NBar conjunction: everyone who is both a representative and a client', note='Note that this is formally identical with preceding').
fracasProblem(id=089, fracas_answer=yes, p=['Every representative or client was at the meeting'], q='Was every representative and every client at the meeting?', h='Every representative and every client was at the meeting', why='With disjunction, NP conjunction seems unavailable').

/*<comment class=subsection> 22 Definite Plurals </comment>*/
 

/*<comment>Definite plurals can often be non-anaphoric and behave like universallyquantified noun phrases (90) However, as with (generic) bare plurals, theforce of the quantification can also be less than universal (91) Whether thislessening of quantificational force is due to the noun phrase or to thepredicate of which the NP is an argument is unclear (92, 93) </comment>*/
 
fracasProblem(id=090, fracas_answer=yes, p=['The chairman read out the items on the agenda'], q='Did the chairman read out every item on the agenda?', h='The chairman read out every item on the agenda').

/*<comment> Non-anaphoric, universal plural definite </comment>*/
 
fracasProblem(id=091, fracas_answer=unknown, p=['The people who were at the meeting voted for a new chairman'], q='Did everyone at the meeting vote for a new chairman?', h='Everyone at the meeting voted for a new chairman', a='don\'t know', why='Some people may have abstained from the vote').
fracasProblem(id=092, fracas_answer=yes, p=['All the people who were at the meeting voted for a new chairman'], q='Did everyone at the meeting vote for a new chairman?', h='Everyone at the meeting voted for a new chairman').
fracasProblem(id=093, fracas_answer=yes, p=['The people who were at the meeting all voted for a new chairman'], q='Did everyone at the meeting vote for a new chairman?', h='Everyone at the meeting voted for a new chairman').

/*<comment> Closely related to this, plural definites can have a collective/institutional or even generic interpretation: </comment>*/
 
fracasProblem(id=094, fracas_answer=unknown, p=['The inhabitants of Cambridge voted for a Labour MP'], q='Did every inhabitant of Cambridge vote for a Labour MP?', h='Every inhabitant of Cambridge voted for a Labour MP', a='don\'t know').
fracasProblem(id=095, fracas_answer=unknown, p=['The Ancient Greeks were noted philosophers'], q='Was every Ancient Greek a noted philosopher?', h='Every Ancient Greek was a noted philosopher', a='don\'t know').
fracasProblem(id=096, fracas_answer=yes, p=['The Ancient Greeks were all noted philosophers'], q='Was every Ancient Greek a noted philosopher?', h='Every Ancient Greek was a noted philosopher').

/*<comment class=subsection> 23 Bare Plurals </comment>*/
 

/*<comment> Bare plurals can exhibit existential, (quasi) universal, generic or dependent plural behaviour </comment>*/
 

/*<comment> The circumstances giving rise to these different behaviours a poorly understood, so we only give a few illustrative examples </comment>*/
 
fracasProblem(id=097, fracas_answer=yes, p=['Software faults were blamed for the system failure'], q='Was the system failure blamed on one or more software faults?', h='The system failure was blamed on one or more software faults', why='Existential bare plural').
fracasProblem(id=098, fracas_answer=unknown, p=['Software faults were blamed for the system failure',  'Bug # 32-985 is a known software fault'], q='Was Bug # 32-985 blamed for the system failure?', h='Bug # 32-985 was blamed for the system failure', a='don\'t know', why='Existential interpretation: not every software fault contributed to the failure').
fracasProblem(id=099, fracas_answer=yes, p=['Clients at the demonstration were all impressed by the system  \'s performance',  'Smith was a client at the demonstration'], q='Was Smith impressed by the system  \'s performance?', h='Smith was impressed by the system \'s performance', why='(Quasi) universal bare plural').
fracasProblem(id=100, fracas_answer=yes, p=['Clients at the demonstration were impressed by the system \'s performance'], q='Were most clients at the demonstration impressed by the system \'s performance?', h='Most clients at the demonstration were impressed by the system \'s performance', why='(Quasi) universal bare plural').
fracasProblem(id=101, fracas_answer=yes, p=['University graduates make poor stock-market traders',  'Smith is a university graduate'], q='Is Smith likely to make a poor stock market trader?', h='Smith is likely to make a poor stock market trader', why='Generic interpretation').
fracasProblem(id=102, fracas_answer=unknown, p=['University graduates make poor stock-market traders',  'Smith is a university graduate'], q='Will Smith make a poor stock market trader?', h='Smith will make a poor stock market trader', a='don\'t know', why='Generic interpretation').

/*<comment class=subsection> 24 Dependent Plurals </comment>*/
 
fracasProblem(id=103, fracas_answer=yes, p=['All APCOM managers have company cars',  'Jones is an APCOM manager'], q='Does Jones have a company car?', h='Jones has a company car').
fracasProblem(id=104, fracas_answer=unknown, p=['All APCOM managers have company cars',  'Jones is an APCOM manager'], q='Does Jones have more than one company car?', h='Jones has more than one company car', a='don\'t know').

/*<comment class=subsection> 25 Negated Plurals </comment>*/
 
fracasProblem(id=105, fracas_answer=no, p=['Just one accountant attended the meeting'], q='Did no accountants attend the meeting?', h='No accountants attended the meeting', a='No').
fracasProblem(id=106, fracas_answer=no, p=['Just one accountant attended the meeting'], q='Did no accountant attend the meeting?', h='No accountant attended the meeting', a='No').
fracasProblem(id=107, fracas_answer=yes, p=['Just one accountant attended the meeting'], q='Did any accountants attend the meeting?', h='Some accountants attended the meeting').
fracasProblem(id=108, fracas_answer=yes, p=['Just one accountant attended the meeting'], q='Did any accountant attend the meeting?', h='Some accountant attended the meeting').
fracasProblem(id=109, fracas_answer=no, p=['Just one accountant attended the meeting'], q='Did some accountants attend the meeting?', h='Some accountants attended the meeting', a='No, just one').
fracasProblem(id=110, fracas_answer=yes, p=['Just one accountant attended the meeting'], q='Did some accountant attend the meeting?', h='Some accountant attended the meeting').

/*<comment class=subsection> 26 Collective and Distributive Plurals </comment>*/
 
fracasProblem(id=111, fracas_answer=yes, p=['Smith signed one contract',  'Jones signed another contract'], q='Did Smith and Jones sign two contracts?', h='Smith and Jones signed two contracts', a='Yes, on a collective/cumulative reading of the conclusion').
fracasProblem(id=112, fracas_answer=yes, p=['Smith signed two contracts',  'Jones signed two contracts'], q='Did Smith and Jones sign two contracts?', h='Smith and Jones signed two contracts', a='Yes, on a distributive reading of Smith and Jones').
fracasProblem(id=113, fracas_answer=yes, p=['Smith signed two contracts',  'Jones also signed them'], q='Did Smith and Jones sign two contracts?', h='Smith and Jones signed two contracts').

/*<comment class=section> 3 (NOMINAL) ANAPHORA </comment>*/
 

/*<comment> In the examples below we make the assumption (unless otherwise indicated) that there is no context beyond that provided by the mini-discourse This is so that we can do away with explicit co-indexing of pronouns with their antecedents, on the grounds that context will provide only (or sometimes a strictly limited number) of possible antecedents </comment>*/
 

/*<comment class=subsection> 31 Intra-Sentential </comment>*/
 
fracasProblem(id=114, fracas_answer=yes, p=['Mary used her workstation'], q='Was Mary \'s workstation used?', h='Mary \'s workstation was used').
fracasProblem(id=115, fracas_answer=yes, p=['Mary used her workstation'], q='Does Mary have a workstation?', h='Mary has a workstation').
fracasProblem(id=116, fracas_answer=yes, p=['Mary used her workstation'], q='Is Mary female?', h='Mary is female').
fracasProblem(id=117, fracas_answer=yes, p=['Every student used her workstation',  'Mary is a student'], q='Did Mary use her workstation?', h='Mary used her workstation').
fracasProblem(id=118, fracas_answer=yes, p=['Every student used her workstation',  'Mary is a student'], q='Does Mary have a workstation?', h='Mary has a workstation').
fracasProblem(id=119, fracas_answer=no, p=['No student used her workstation',  'Mary is a student'], q='Did Mary use a workstation?', h='Mary used a workstation', a='No').

/*<comment class=subsection> 32 Inter-Sentential </comment>*/
 
fracasProblem(id=120, fracas_answer=yes, p=['Smith attended a meeting',  'She chaired it'], q='Did Smith chair a meeting?', h='Smith chaired a meeting').
fracasProblem(id=121, fracas_answer=yes, p=['Smith delivered a report to ITEL',  'She also delivered them an invoice',  'And she delivered them a project proposal'], q='Did Smith deliver a report, an invoice and a project proposal to ITEL?', h='Smith delivered a report, an invoice and a project proposal to ITEL', why='Keeping track of same entities across more than two sentences').
fracasProblem(id=122, fracas_answer=yes, p=['Every committee has a chairman',  'He is appointed its members'], q='Does every committee have a chairman appointed by members of the committee?', h='Every committee has a chairman appointed by members of the committee', why='Modal subordination').

/*<comment class=subsection> 33 Plural Anaphora </comment>*/
 
fracasProblem(id=123, fracas_answer=yes, p=['ITEL has sent most of the reports Smith needs',  'They are on her desk'], q='Are there some reports from ITEL on Smith \'s desk?', h='There are some reports from ITEL on Smith \'s desk').
fracasProblem(id=124, fracas_answer=yes, p=['Two out of ten machines are missing',  'They have been removed'], q='Have two machines been removed?', h='Two machines have been removed').
fracasProblem(id=125, fracas_answer=unknown, p=['Two out of ten machines are missing',  'They have been removed'], q='Have eight machines been removed?', h='Eight machines have been removed', a='don\'t know', why='Set difference can\'t be used to construct plural antecedents').
fracasProblem(id=126, fracas_answer=yes, p=['Two out of ten machines are missing',  'They were all here yesterday'], q='Were ten machines here yesterday?', h='Ten machines were here yesterday').
fracasProblem(id=127, fracas_answer=yes, p=['Smith took a machine on Tuesday, and Jones took a machine on Wednesday',  'They put them in the lobby'], q='Did Smith and Jones put two machines in the lobby?', h='Smith and Jones put two machines in the lobby', a='Yes, on a distributive reading of the question', why='Construction of plural antecedents from separate constituents').
fracasProblem(id=128, fracas_answer=yes, p=['John and his colleagues went to a meeting',  'They hated it'], q='Did John \'s colleagues hate the meeting?', h='John \'s colleagues hated the meeting').
fracasProblem(id=129, fracas_answer=yes, p=['John and his colleagues went to a meeting',  'They hated it'], q='Did John hate the meeting?', h='John hated the meeting', a='Yes, on one possible reading', why='They can be resolved to John and his colleagues').
fracasProblem(id=130, fracas_answer=unknown, p=['John and his colleagues went to a meeting',  'They hated it'], q='Did John hate the meeting?', h='John hated the meeting', a='don\'t know, on one possible reading', why='They can also be resolved to John \'s colleagues but not John', note='Note that this is formally identical with preceding').
fracasProblem(id=131, fracas_answer=yes, p=['Each department has a dedicated line',  'They rent them from BT'], q='Does every department rent a line from BT?', h='Every department rents a line from BT', why='Dependent plural anaphora').
fracasProblem(id=132, fracas_answer=yes, p=['Each department has a dedicated line',  'The sales department rents it from BT'], q='Does the sales department rent a line from BT?', h='The sales department rents a line from BT', why='Paycheque pronoun').

/*<comment class=subsection> 34 E-type and Donkey Pronouns </comment>*/
 
fracasProblem(id=133, fracas_answer=yes, p=['GFI owns several computers',  'ITEL maintains them'], q='Does ITEL maintain all the computers that GFI owns?', h='ITEL maintains all the computers that GFI owns', why='E-type anaphora').
fracasProblem(id=134, fracas_answer=yes, p=['Every customer who owns a computer has a service contract for it',  'MFI is a customer that owns exactly one computer'], q='Does MFI have a service contract for all its computers?', h='MFI has a service contract for all its computers', why='Donkey sentence').
fracasProblem(id=135, fracas_answer=yes, p=['Every customer who owns a computer has a service contract for it',  'MFI is a customer that owns several computers'], q='Does MFI have a service contract for all its computers?', h='MFI has a service contract for all its computers', why='This pattern of inference, unlike (134), tends to some theory dependence Although the inference seems correct in this example, compare with (136)').
fracasProblem(id=136, fracas_answer=unknown, p=['Every executive who had a laptop computer brought it to take notes at the meeting',  'Smith is a executive who owns five different laptop computers'], q='Did Smith take five laptop computers to the meeting?', h='Smith took five laptop computers to the meeting', a='don\'t know', why='Similar to (135), except for tense and pragmatic plausibility').
fracasProblem(id=137, fracas_answer=yes, p=['There are 100 companies',  'ICM is one of the companies and owns 150 computers',  'It does not have service contracts for any of its computers',  ' Each of the other 99 companies owns one computer',  ' They have service contracts for them'], q='Do most companies that own a computer have a service contract for it?', h='Most companies that own a computer have a service contract for it', why='Proportion problem').

/*<comment class=subsection> 35 Functional and Subsectional </comment>*/
 

/*<comment> Due to the heavy domain dependence of functional (or better perhaps, relational) anaphora, it is hard to state general inferences that don\'t assume considerable background knowledge unless this is given explicitly </comment>*/
 
fracasProblem(id=138, fracas_answer=yes, p=['Every report has a cover page',  'R-95-103 is a report',  'Smith signed the cover page'], q='Did Smith sign the cover page of R-95-103?', h='Smith signed the cover page of R-95-103').

/*<comment class=subsection> 36 Simple Reflexives </comment>*/
 
fracasProblem(id=139, fracas_answer=yes, p=['A company director awarded himself a large payrise'], q='Has a company director awarded and been awarded a payrise?', h='A company director has awarded and been awarded a payrise').
fracasProblem(id=140, fracas_answer=yes, p=['John said Bill had hurt himself'], q='Did John say Bill had been hurt?', h='John said Bill had been hurt').
fracasProblem(id=141, fracas_answer=unknown, p=['John said Bill had hurt himself'], q='Did anyone say John had been hurt?', h='Someone said John had been hurt', a='don\'t know').

/*<comment class=section> 4 ELLIPSIS </comment>*/
 

/*<comment>In nearly all cases the inferences presented here have conclusions that aresimply reconstructions of the ellided constituent Unfortunately, an inferencetest suite is not well suited to illustrating prohibitions on ellipsisresolution For example, an ill-formed discourse like John was in Paris yesterday *So did Bill doesn\'t even get as far as supporting any inferences </comment>*/
 

/*<comment class=subsection> 41 VP Ellipsis </comment>*/
 
fracasProblem(id=142, fracas_answer=yes, p=['John spoke to Mary',  'So did Bill'], q='Did Bill speak to Mary?', h='Bill spoke to Mary', why='Basic example').
fracasProblem(id=143, fracas_answer=unknown, p=['John spoke to Mary',  'So did Bill',  'John spoke to Mary at four o\'clock'], q='Did Bill speak to Mary at four o\'clock?', h='Bill spoke to Mary at four o\'clock', a='don\'t know', why='Temporal resolution of tense in antecedent is not carried across to ellipsis').
fracasProblem(id=144, fracas_answer=yes, p=['John spoke to Mary at four o\'clock',  'So did Bill'], q='Did Bill speak to Mary at four o\'clock?', h='Bill spoke to Mary at four o\'clock', why='Explicit temporal adverbials are carried across to ellipsis').
fracasProblem(id=145, fracas_answer=yes, p=['John spoke to Mary at four o\'clock',  'And Bill did at five o\'clock'], q='Did Bill speak to Mary at five o\'clock?', h='Bill spoke to Mary at five o\'clock', why='Explicit temporal adverbials are not carried across if overridden').
fracasProblem(id=146, fracas_answer=yes, p=['John has spoken to Mary',  'Bill is going to'], q='Will Bill speak to Mary?', h='Bill will speak to Mary', why='Tense agreement not necessary between ellipsis and antecedent').
fracasProblem(id=147, fracas_answer=no, p=['John spoke to Mary on Monday',  'Bill didn\'t'], q='Did Bill speak to Mary on Monday?', h='Bill spoke to Mary on Monday', a='No', why='Polarity agreement not necessary between ellipsis and antecedent').
fracasProblem(id=148, fracas_answer=yes, p=['Has John spoken to Mary?',  'Bill has'], q='Has Bill spoken to Mary?', h='Bill has spoken to Mary', why='Mood agreement not necessary between ellipsis and antecedent', note='Note unusual use of question as premise').
fracasProblem(id=149, fracas_answer=yes, p=['John has spoken to Mary',  'The students have too'], q='Have the students spoken to Mary?', h='The students have spoken to Mary', why='Number agreement not necessary').

/*<comment class=subsection> 42 Gapping </comment>*/
 
fracasProblem(id=150, fracas_answer=yes, p=['John went to Paris by car, and Bill by train'], q='Did Bill go to Paris by train?', h='Bill went to Paris by train', why='Basic example').
fracasProblem(id=151, fracas_answer=yes, p=['John went to Paris by car, and Bill by train to Berlin'], q='Did Bill go to Berlin by train?', h='Bill went to Berlin by train', why='Another basic example').
fracasProblem(id=152, fracas_answer=yes, p=['John went to Paris by car, and Bill to Berlin'], q='Did Bill go to Berlin by car?', h='Bill went to Berlin by car', why='Another basic example').
fracasProblem(id=153, fracas_answer=yes, p=['John is going to Paris by car, and the students by train'], q='Are the students going to Paris by train?', h='The students are going to Paris by train', why='Subject-verb agreement not necessary').
fracasProblem(id=154, fracas_answer=yes, p=['John went to Paris by car',  'Bill by train'], q='Did Bill go to Paris by train?', h='Bill went to Paris by train', why='Cross-sentential gapping').

/*<comment class=subsection> 43 One Anaphora </comment>*/
 
fracasProblem(id=155, fracas_answer=yes, p=['John owns a car',  'Bill owns one too'], q='Does Bill own a car?', h='Bill owns a car', why='Basic example').
fracasProblem(id=156, fracas_answer=unknown, p=['John owns a car',  'Bill owns one too'], q='Is there a car that John and Bill own?', h='There is a car that John and Bill own', a='don\'t know', why='It needn\'t be the same car that John and Bill own').
fracasProblem(id=157, fracas_answer=yes, p=['John owns a red car',  'Bill owns a blue one'], q='Does Bill own a blue car?', h='Bill owns a blue car').
fracasProblem(id=158, fracas_answer=unknown, p=['John owns a red car',  'Bill owns a blue one'], q='Does Bill own a red car?', h='Bill owns a red car', a='don\'t know').
fracasProblem(id=159, fracas_answer=yes, p=['John owns a red car',  'Bill owns a fast one'], q='Does Bill own a fast car?', h='Bill owns a fast car').
fracasProblem(id=160, fracas_answer=yes, p=['John owns a red car',  'Bill owns a fast one'], q='Does Bill own a fast red car?', h='Bill owns a fast red car', a='Yes, on one possible reading', why='The one anaphor may be resolved via the property of being a red car').
fracasProblem(id=161, fracas_answer=unknown, p=['John owns a red car',  'Bill owns a fast one'], q='Does Bill own a fast red car?', h='Bill owns a fast red car', a='don\'t know, on one possible reading', why='Or the one anaphor may just be resolved via the property of being a car', note='Note that this is formally identical with preceding').
fracasProblem(id=162, fracas_answer=yes, p=['John owns a fast red car',  'Bill owns a slow one'], q='Does Bill own a slow red car?', h='Bill owns a slow red car', why='When semantically parallel (eg fast/slow) modifiers appear on the antecedent and one-anaphor, it appears that all non-parallel modifiers must form part of the resolution').

/*<comment class=subsection> 44 Sluicing </comment>*/
 
fracasProblem(id=163, fracas_answer=no, p=['John had his paper accepted',  'Bill doesn\'t know why'], q='Does Bill know why John had his paper accepted?', h='Bill knows why John had his paper accepted', a='No').

/*<comment class=subsection> 45 Phrasal Ellipsis </comment>*/
 
fracasProblem(id=164, fracas_answer=yes, p=['John spoke to Mary',  'And to Sue'], q='Did John speak to Sue?', h='John spoke to Sue', why='PP ellipsis (subcategorized)').
fracasProblem(id=165, fracas_answer=yes, p=['John spoke to Mary',  'On Friday'], q='Did John speak to Mary on Friday?', h='John spoke to Mary on Friday', why='PP ellipsis: adds PP to antecedent').
fracasProblem(id=166, fracas_answer=yes, p=['John spoke to Mary on Thursday',  'And on Friday'], q='Did John speak to Mary on Friday?', h='John spoke to Mary on Friday', why='PP ellipsis: replaces PP in antecedent').
fracasProblem(id=167, fracas_answer=no, p=['Twenty men work in the Sales Department',  'But only one woman'], q='Do two women work in the Sales Department?', h='Two women work in the Sales Department', a='No', why='NP ellipsis').
fracasProblem(id=168, fracas_answer=yes, p=['Five men work part time',  'And forty five women'], q='Do forty five women work part time?', h='Forty five women work part time', why='NP ellipsis').
fracasProblem(id=169, fracas_answer=yes, p=['John found Mary before Bill'], q='Did John find Mary before Bill found Mary?', h='John found Mary before Bill found Mary', a='Yes, on one possible reading', why='NP ellipsis').
fracasProblem(id=170, fracas_answer=yes, p=['John found Mary before Bill'], q='Did John find Mary before John found Bill?', h='John found Mary before John found Bill', a='Yes, on one possible reading', why='NP ellipsis').
fracasProblem(id=171, fracas_answer=yes, p=['John wants to know how many men work part time',  'And women'], q='Does John want to know how many women work part time?', h='John wants to know how many women work part time', why='Nbar ellipsis').
fracasProblem(id=172, fracas_answer=yes, p=['John wants to know how many men work part time, and which'], q='Does John want to know which men work part time?', h='John wants to know which men work part time', why='Determiner ellipsis').

/*<comment class=subsection> 46 Antecedent Contained Deletion </comment>*/
 

/*<comment> Antecedent contained deletion is a notorious problem for copying approaches to ellipsis, since the antecedent clause contains the ellipsis and some way must be found of removing it from the copy </comment>*/
 
fracasProblem(id=173, fracas_answer=yes, p=['Bill spoke to everyone that John did',  'John spoke to Mary'], q='Did Bill speak to Mary?', h='Bill spoke to Mary').
fracasProblem(id=174, fracas_answer=unknown, p=['Bill spoke to everyone that John did',  'Bill spoke to Mary'], q='Did John speak to Mary?', h='John spoke to Mary', a='don\'t know').

/*<comment class=subsection> 47 Configurational Effects </comment>*/
 

/*<comment>There are a number of syntactic and other configurational constraints on whatcan constitute the antecedent to an ellipsis These constraints varyingdepending on the type of ellipsis (VP, phrasal, gapping, etc) </comment>*/
 
fracasProblem(id=175, fracas_answer=yes, p=['John said Mary wrote a report, and Bill did too'], q='Did Bill say Mary wrote a report?', h='Bill said Mary wrote a report', a='Yes, on one possible reading/parse').
fracasProblem(id=176, fracas_answer=yes, p=['John said Mary wrote a report, and Bill did too'], q='Did John say Bill wrote a report?', h='John said Bill wrote a report', a='Yes, on one possible reading/parse').
fracasProblem(id=177, fracas_answer=unknown, p=['John said that Mary wrote a report, and that Bill did too'], q='Did Bill say Mary wrote a report?', h='Bill said Mary wrote a report', a='don\'t know').

/*<comment> Note that the first sentence in (175) and (176) is syntactically ambiguous, depending on whether the conjunctive clause conjoins with the main or subordinate clause of John said Mary wrote a report In (177) the conjunctive clause unambiguously conjoins with the subordinate clause, and only one interpretation of the ellipsis is possible This appears to indicate that the antecedent clause to a VP ellipsis must be adjacent to the elliptical clause However, as the examples below show, this is not correct </comment>*/
 
fracasProblem(id=178, fracas_answer=yes, p=['John wrote a report, and Bill said Peter did too'], q='Did Bill say Peter wrote a report?', h='Bill said Peter wrote a report', why='Embedded elliptical clause').
fracasProblem(id=179, fracas_answer=yes, p=['If John wrote a report, then Bill did too',  'John wrote a report'], q='Did Bill write a report?', h='Bill wrote a report', why='Elliptical and antecedent clause embedded (in parallel)').
fracasProblem(id=180, fracas_answer=yes, p=['John wanted to buy a car, and he did'], q='Did John buy a car?', h='John bought a car', why='Embedded antecedent clause').
fracasProblem(id=181, fracas_answer=unknown, p=['John needed to buy a car, and Bill did'], q='Did Bill buy a car?', h='Bill bought a car', a='don\'t know').

/*<comment>Other configurational effects of the kinds illustrated in Deliverable 7 arehard to exemplify using inference suites </comment>*/
 

/*<comment class=subsection> 48 Ellipsis and Anaphora </comment>*/
 

/*<comment>The following inferences illustrate differences between strict and sloppyinterpretations of anaphors in elliptical clauses </comment>*/
 
fracasProblem(id=182, fracas_answer=yes, p=['Smith represents his company and so does Jones'], q='Does Jones represent Jones\' company?', h='Jones represents Jones\' company', a='Yes, on one reading', why='Sloppy identity').
fracasProblem(id=183, fracas_answer=yes, p=['Smith represents his company and so does Jones'], q='Does Jones represent Smith \'s company?', h='Jones represents Smith \'s company', a='Yes, on one reading', why='Strict identity').
fracasProblem(id=184, fracas_answer=unknown, p=['Smith represents his company and so does Jones'], q='Does Smith represent Jones\' company?', h='Smith represents Jones\' company', a='don\'t know').
fracasProblem(id=185, fracas_answer=yes, p=['Smith claimed he had costed his proposal and so did Jones'], q='Did Jones claim he had costed his own proposal?', h='Jones claimed he had costed his own proposal', a='Yes, on one reading', why='Sloppy identity on both pronouns').
fracasProblem(id=186, fracas_answer=yes, p=['Smith claimed he had costed his proposal and so did Jones'], q='Did Jones claim he had costed Smith \'s proposal?', h='Jones claimed he had costed Smith \'s proposal', a='Yes, on one reading', why='Sloppy identity he, strict on his').
fracasProblem(id=187, fracas_answer=yes, p=['Smith claimed he had costed his proposal and so did Jones'], q='Did Jones claim Smith had costed Smith \'s proposal?', h='Jones claimed Smith had costed Smith \'s proposal', a='Yes, on one reading', why='Strict identity on both pronouns').
fracasProblem(id=188, fracas_answer=unknown, p=['Smith claimed he had costed his proposal and so did Jones'], q='Did Jones claim Smith had costed Jones\' proposal?', h='Jones claimed Smith had costed Jones\' proposal', a='don\'t know', why='Can\'t have strict identity on he and sloppy identity on his').
fracasProblem(id=189, fracas_answer=yes, p=['John is a man and Mary is a woman',  'John represents his company and so does Mary'], q='Does Mary represent her own company?', h='Mary represents her own company', a='Yes, on one reading', why='Sloppy identity, gender agreement not necessary').
fracasProblem(id=190, fracas_answer=yes, p=['John is a man and Mary is a woman',  'John represents his company and so does Mary'], q='Does Mary represent John \'s company?', h='Mary represents John \'s company', a='Yes, on one reading', why='Strict identity, gender agreement not necessary').
fracasProblem(id=191, fracas_answer=yes, p=['Bill suggested to Frank \'s boss that they should go to the meeting together, and Carl to Alan \'s wife'], q='If it was suggested that Bill and Frank should go together, was it suggested that Carl and Alan should go together?', h='If it was suggested that Bill and Frank should go together, it was suggested that Carl and Alan should go together', why='Plural pronouns resolved in parallel').
fracasProblem(id=192, fracas_answer=unknown, p=['Bill suggested to Frank \'s boss that they should go to the meeting together, and Carl to Alan \'s wife'], q='If it was suggested that Bill and Frank should go together, was it suggested that Carl and Alan \'s wife should go together?', h='If it was suggested that Bill and Frank should go together, it was suggested that Carl and Alan \'s wife should go together', a='don\'t know', why='Plural pronouns resolved in parallel').
fracasProblem(id=193, fracas_answer=yes, p=['Bill suggested to Frank \'s boss that they should go to the meeting together, and Carl to Alan \'s wife'], q='If it was suggested that Bill and Frank \'s boss should go together, was it suggested that Carl and Alan \'s wife should go together?', h='If it was suggested that Bill and Frank \'s boss should go together, it was suggested that Carl and Alan \'s wife should go together', why='Plural pronouns resolved in parallel').
fracasProblem(id=194, fracas_answer=unknown, p=['Bill suggested to Frank \'s boss that they should go to the meeting together, and Carl to Alan \'s wife'], q='If it was suggested that Bill and Frank \'s boss should go together, was it suggested that Carl and Alan should go together?', h='If it was suggested that Bill and Frank \'s boss should go together, it was suggested that Carl and Alan should go together', a='don\'t know', why='Plural pronouns resolved in parallel').
fracasProblem(id=195, fracas_answer=yes, p=['Bill suggested to Frank \'s boss that they should go to the meeting together, and Carl to Alan \'s wife'], q='If it was suggested that Bill, Frank and Frank \'s boss should go together, was it suggested that Carl, Alan and Alan \'s wife should go together?', h='If it was suggested that Bill, Frank and Frank \'s boss should go together, it was suggested that Carl, Alan and Alan \'s wife should go together', why='Plural pronouns resolved in parallel').

/*<comment class=subsection> 49 Ellipsis and Quantification </comment>*/
 

/*<comment> Scope parallelism turns out to be rather tricky to illustrate through inference suites This is because of the entailment relation: 98 j= 89 </comment>*/
 
fracasProblem(id=196, fracas_answer=yes, p=['A lawyer signed every report, and so did an auditor',  'That is, there was one lawyer who signed all the reports'], q='Was there one auditor who signed all the reports?', h='There was one auditor who signed all the reports').

/*<comment class=section> 5 ADJECTIVES </comment>*/
 

/*<comment>The inferences below carve up adjectives into (a by no means exhaustive)cross-cutting set of dimensions Typical inferences are given for exampleadjectives </comment>*/
 

/*<comment class=subsection> 51 Affirmative and Non-Affirmative </comment>*/
 

/*<comment>Affirmative adjectives map the denotation of the predicate they modify onto asubset of the denotation So for example, an old man is a man Most adjectivesare affirmative, but a few like former and fake are not Given that someone isa former student, one cannot conclude that they are now a student But it isnot entirely clear whether one can conclude that they are not now a student they may have become one again </comment>*/
 
fracasProblem(id=197, fracas_answer=yes, p=['John has a genuine diamond'], q='Does John have a diamond?', h='John has a diamond', why='Affirmative adjectives: Adj N entails N').
fracasProblem(id=198, fracas_answer=no, p=['John is a former university student'], q='Is John a university student?', h='John is a university student', a='No / don\'t know', why='Non-affirmative: Adj N =/=> N (Opinions differ about whether Adj N entails !N)').
fracasProblem(id=199, fracas_answer=yes, p=['John is a successful former university student'], q='Is John successful?', h='John is successful', a='Yes (for a former university student)', why='Ordering between affirmative and non-affirmative adjectives affects which adjectival predications are and aren\'t affirmed').
fracasProblem(id=200, fracas_answer=unknown, p=['John is a former successful university student'], q='Is John successful?', h='John is successful', a='don\'t know').
fracasProblem(id=201, fracas_answer=unknown, p=['John is a former successful university student'], q='Is John a university student?', h='John is a university student', a='don\'t know', why='John may currently be an unsuccessful university student').

/*<comment class=subsection> 52 No Comparison Class </comment>*/
 

/*<comment>Gradable adjectives (eg big, small) usually assume some form of comparisonclass (ie big for an N) But some others do not eg four-legged, or theadjectival phrase ten foot long Adjectives not requiring a comparison classpermit straightforward predication without reference to a nominal propertyproviding a comparison class: a ten foot long alligator is ten foot long </comment>*/
 
fracasProblem(id=202, fracas_answer=yes, p=['Every mammal is an animal'], q='Is every four-legged mammal a four-legged animal?', h='Every four-legged mammal is a four-legged animal', why='[N1 entails N2] entails [Adj(N1) entails Adj(N2)]').
fracasProblem(id=203, fracas_answer=yes, p=['Dumbo is a four-legged animal'], q='Is Dumbo four-legged?', h='Dumbo is four-legged', why='Adj(N)(x) entails Adj(x)').

/*<comment class=subsection> 53 Opposites </comment>*/
 

/*<comment> Large and small (applied to the same comparison class) are opposites If something is a small N it cannot be a large N, and vice versa Some things can be neither large nor small Ns </comment>*/
 
fracasProblem(id=204, fracas_answer=no, p=['Mickey is a small animal'], q='Is Mickey a large animal?', h='Mickey is a large animal', a='No', why='Small(N) entails !Large(N)').
fracasProblem(id=205, fracas_answer=no, p=['Dumbo is a large animal'], q='Is Dumbo a small animal?', h='Dumbo is a small animal', a='No', why='Large(N) entails !Small(N)').
fracasProblem(id=206, fracas_answer=unknown, p=['Fido is not a small animal'], q='Is Fido a large animal?', h='Fido is a large animal', a='don\'t know', why='!Small(N) =/=> Large(N)').
fracasProblem(id=207, fracas_answer=unknown, p=['Fido is not a large animal'], q='Is Fido a small animal?', h='Fido is a small animal', a='don\'t know', why='!Large(N) =/=> Small(N)').
fracasProblem(id=208, fracas_answer=yes, p=['Mickey is a small animal',  'Dumbo is a large animal'], q='Is Mickey smaller than Dumbo?', h='Mickey is smaller than Dumbo', why='Small and large are related via the comparative smaller').
fracasProblem(id=209, fracas_answer=no, p=['Mickey is a small animal',  'Dumbo is a large animal'], q='Is Mickey larger than Dumbo?', h='Mickey is larger than Dumbo', a='No', why='Small and large are related via the comparative larger').

/*<comment class=subsection> 54 Extensional Comparison Classes </comment>*/
 

/*<comment> Adjectives like large and small depend only on the extension of the comparison class they depend on </comment>*/
 
fracasProblem(id=210, fracas_answer=no, p=['All mice are small animals',  'Mickey is a large mouse'], q='Is Mickey a large animal?', h='Mickey is a large animal', a='No').
fracasProblem(id=211, fracas_answer=no, p=['All elephants are large animals',  'Dumbo is a small elephant'], q='Is Dumbo a small animal?', h='Dumbo is a small animal', a='No').
fracasProblem(id=212, fracas_answer=yes, p=['All mice are small animals',  'All elephants are large animals',  'Mickey is a large mouse',  ' Dumbo is a small elephant'], q='Is Dumbo larger than Mickey?', h='Dumbo is larger than Mickey', why='Assume comparative relations exemplified in (208) and (209)').
fracasProblem(id=213, fracas_answer=undef, p=['All mice are small animals',  'Mickey is a large mouse'], q='Is Mickey small?', h='Mickey is small', a='??: Yes for a mouse; ?? No for an animal', why='Adjectives requiring a comparison class cannot usually be predicated in the absence of a common noun, unless some comparison class is clear from the wider context').

/*<comment class=subsection> 55 Extensional and Intensional Comparison Classes </comment>*/
 

/*<comment>Some adjectives require an intensional comparison class: differentinferences may follow when two distinct but co-extensive predicates providethe comparison class </comment>*/
 
fracasProblem(id=214, fracas_answer=yes, p=['All legal authorities are law lecturers',  'All law lecturers are legal authorities'], q='Are all fat legal authorities fat law lecturers?', h='All fat legal authorities are fat law lecturers', why='Extensional comparison class').
fracasProblem(id=215, fracas_answer=unknown, p=['All legal authorities are law lecturers',  'All law lecturers are legal authorities'], q='Are all competent legal authorities competent law lecturers?', h='All competent legal authorities are competent law lecturers', a='don\'t know', why='Intensional comparison class').
fracasProblem(id=216, fracas_answer=yes, p=['John is a fatter politician than Bill'], q='Is John fatter than Bill?', h='John is fatter than Bill', why='Extensional').
fracasProblem(id=217, fracas_answer=unknown, p=['John is a cleverer politician than Bill'], q='Is John cleverer than Bill?', h='John is cleverer than Bill', a='don\'t know', why='Intensional').

/*<comment>Note that both intensional and extensional comparison class adjectives supportcomparatives </comment>*/
 

/*<comment class=subsection> 56 Default Comparison Classes </comment>*/
 

/*<comment> Comparison class adjectives can sometimes pick up a default comparison class from the subject NP For example, knowing that Kim is a person provides a default scale for assessing cleverness in people If Kim were known to be a dog, the assessment scale would be different </comment>*/
 
fracasProblem(id=218, fracas_answer=yes, p=['Kim is a clever person'], q='Is Kim clever?', h='Kim is clever').
fracasProblem(id=219, fracas_answer=unknown, my_answer=yes, p=['Kim is a clever politician'], q='Is Kim clever?', h='Kim is clever', a='don\'t know').

/*<comment class=section> 6 COMPARATIVES </comment>*/
 

/*<comment class=subsection> 61 Phrasal Comparatives </comment>*/
 
fracasProblem(id=220, fracas_answer=yes, p=['The PC-6082 is faster than the ITEL-XZ',  'The ITEL-XZ is fast'], q='Is the PC-6082 fast?', h='The PC-6082 is fast').
fracasProblem(id=221, fracas_answer=unknown, p=['The PC-6082 is faster than the ITEL-XZ'], q='Is the PC-6082 fast?', h='The PC-6082 is fast', a='don\'t know').
fracasProblem(id=222, fracas_answer=unknown, p=['The PC-6082 is faster than the ITEL-XZ',  'The PC-6082 is fast'], q='Is the ITEL-XZ fast?', h='The ITEL-XZ is fast', a='don\'t know').
fracasProblem(id=223, fracas_answer=no, p=['The PC-6082 is faster than the ITEL-XZ',  'The PC-6082 is slow'], q='Is the ITEL-XZ fast?', h='The ITEL-XZ is fast', a='No').
fracasProblem(id=224, fracas_answer=yes, p=['The PC-6082 is as fast as the ITEL-XZ',  'The ITEL-XZ is fast'], q='Is the PC-6082 fast?', h='The PC-6082 is fast').
fracasProblem(id=225, fracas_answer=unknown, p=['The PC-6082 is as fast as the ITEL-XZ'], q='Is the PC-6082 fast?', h='The PC-6082 is fast', a='don\'t know').
fracasProblem(id=226, fracas_answer=unknown, p=['The PC-6082 is as fast as the ITEL-XZ',  'The PC-6082 is fast'], q='Is the ITEL-XZ fast?', h='The ITEL-XZ is fast', a='don\'t know').
fracasProblem(id=227, fracas_answer=no, p=['The PC-6082 is as fast as the ITEL-XZ',  'The PC-6082 is slow'], q='Is the ITEL-XZ fast?', h='The ITEL-XZ is fast', a='No').
fracasProblem(id=228, fracas_answer=unknown, p=['The PC-6082 is as fast as the ITEL-XZ'], q='Is the PC-6082 faster than the ITEL-XZ?', h='The PC-6082 is faster than the ITEL-XZ', a='don\'t know').
fracasProblem(id=229, fracas_answer=no, p=['The PC-6082 is as fast as the ITEL-XZ'], q='Is the PC-6082 slower than the ITEL-XZ?', h='The PC-6082 is slower than the ITEL-XZ', a='No').
fracasProblem(id=230, fracas_answer=yes, p=['ITEL won more orders than APCOM did'], q='Did ITEL win some orders?', h='ITEL won some orders').
fracasProblem(id=231, fracas_answer=unknown, p=['ITEL won more orders than APCOM did'], q='Did APCOM win some orders?', h='APCOM won some orders', a='don\'t know').
fracasProblem(id=232, fracas_answer=yes, p=['ITEL won more orders than APCOM did',  'APCOM won ten orders'], q='Did ITEL win at least eleven orders?', h='ITEL won at least eleven orders').

/*<comment>Inferences (233)-(235) are similar to (230)-(232) Note however, that ifAPCOM can be interpreted as referring to a particular order (eg the APCOMcontract), as it can in (233), the sentence ITEL won more orders than APCOMis ambiguous between a reading like that in (230)-(232), and one where ITELwon more than just the APCOM order  see (236) </comment>*/
 
fracasProblem(id=233, fracas_answer=yes, p=['ITEL won more orders than APCOM'], q='Did ITEL win some orders?', h='ITEL won some orders').
fracasProblem(id=234, fracas_answer=unknown, p=['ITEL won more orders than APCOM'], q='Did APCOM win some orders?', h='APCOM won some orders', a='don\'t know').
fracasProblem(id=235, fracas_answer=yes, p=['ITEL won more orders than APCOM',  'APCOM won ten orders'], q='Did ITEL win at least eleven orders?', h='ITEL won at least eleven orders').
fracasProblem(id=236, fracas_answer=yes, p=['ITEL won more orders than the APCOM contract'], q='Did ITEL win the APCOM contract?', h='ITEL won the APCOM contract').
fracasProblem(id=237, fracas_answer=yes, p=['ITEL won more orders than the APCOM contract'], q='Did ITEL win more than one order?', h='ITEL won more than one order').
fracasProblem(id=238, fracas_answer=yes, p=['ITEL won twice as many orders than APCOM',  'APCOM won ten orders'], q='Did ITEL win twenty orders?', h='ITEL won twenty orders').

/*<comment class=subsection> 62 Clausal Complement </comment>*/
 
fracasProblem(id=239, fracas_answer=yes, p=['ITEL won more orders than APCOM lost'], q='Did ITEL win some orders?', h='ITEL won some orders').
fracasProblem(id=240, fracas_answer=unknown, p=['ITEL won more orders than APCOM lost'], q='Did APCOM lose some orders?', h='APCOM lost some orders', a='don\'t know').
fracasProblem(id=241, fracas_answer=yes, p=['ITEL won more orders than APCOM lost',  'APCOM lost ten orders'], q='Did ITEL win at least eleven orders?', h='ITEL won at least eleven orders').

/*<comment class=subsection> 63 Measure Phrases </comment>*/
 
fracasProblem(id=242, fracas_answer=yes, p=['The PC-6082 is faster than 500 MIPS',  'The ITEL-ZX is slower than 500 MIPS'], q='Is the PC-6082 faster than the ITEL-ZX?', h='The PC-6082 is faster than the ITEL-ZX').

/*<comment class=subsection> 64 Differential Comparatives </comment>*/
 
fracasProblem(id=243, fracas_answer=yes, p=['ITEL sold 3000 more computers than APCOM',  'APCOM sold exactly 2500 computers'], q='Did ITEL sell 5500 computers?', h='ITEL sold 5500 computers').

/*<comment class=subsection> 65 Attributive Comparatives </comment>*/
 
fracasProblem(id=244, fracas_answer=yes, p=['APCOM has a more important customer than ITEL'], q='Does APCOM have a more important customer than ITEL is?', h='APCOM has a more important customer than ITEL is', a='Yes, on one reading of the premise').
fracasProblem(id=245, fracas_answer=yes, p=['APCOM has a more important customer than ITEL'], q='Does APCOM has a more important customer than ITEL has?', h='APCOM has a more important customer than ITEL has', a='Yes, on one reading of the premise', note='Note ungrammaticality of question in original source: subject/verb agreement').

/*<comment class=subsection> 66 Comparatives and Quantifiers </comment>*/
 
fracasProblem(id=246, fracas_answer=yes, p=['The PC-6082 is faster than every ITEL computer',  'The ITEL-ZX is an ITEL computer'], q='Is the PC-6082 faster than the ITEL-ZX?', h='The PC-6082 is faster than the ITEL-ZX').
fracasProblem(id=247, fracas_answer=unknown, p=['The PC-6082 is faster than some ITEL computer',  'The ITEL-ZX is an ITEL computer'], q='Is the PC-6082 faster than the ITEL-ZX?', h='The PC-6082 is faster than the ITEL-ZX', a='don\'t know').
fracasProblem(id=248, fracas_answer=yes, p=['The PC-6082 is faster than any ITEL computer',  'The ITEL-ZX is an ITEL computer'], q='Is the PC-6082 faster than the ITEL-ZX?', h='The PC-6082 is faster than the ITEL-ZX').
fracasProblem(id=249, fracas_answer=yes, p=['The PC-6082 is faster than the ITEL-ZX and the ITEL-ZY'], q='Is the PC-6082 faster than the ITEL-ZX?', h='The PC-6082 is faster than the ITEL-ZX').
fracasProblem(id=250, fracas_answer=yes, p=['The PC-6082 is faster than the ITEL-ZX or the ITEL-ZY'], q='Is the PC-6082 faster than the ITEL-ZX?', h='The PC-6082 is faster than the ITEL-ZX', a='Yes, on one reading of the premise').

/*<comment class=section> 7 TEMPORAL REFERENCE </comment>*/
 

/*<comment>Inference patterns involving temporal reference are complicated by theinterplay between tense, aspectual information, lexical semantics, defeasibleinterpretation principles such as narrative progression, rhetorical relations, a theory of action and causation, world knowledge, interaction betweenplurality, genericity and temporal/aspectual phenomena etc Some of theinferences are very basic, some are more involved The more complex examplesgive ample illustration of the fact that temporal phenomena are usuallydiscourse phenomena </comment>*/
 

/*<comment class=subsection> 71 Standard Use of Tenses </comment>*/
 
fracasProblem(id=251, fracas_answer=yes, p=['ITEL has a factory in Birmingham'], q='Does ITEL currently have a factory in Birmingham?', h='ITEL currently has a factory in Birmingham').
fracasProblem(id=252, fracas_answer=yes, p=['Since 1992 ITEL has been in Birmingham',  'It is now 1996'], q='Was ITEL in Birmingham in 1993?', h='Itel was in Birmingham in 1993').

/*<comment> (251) and (252) are instances of the subinterval property This works only with stative verbs Cf the following example involving an accomplishment verb in the simple past: </comment>*/
 
fracasProblem(id=253, fracas_answer=unknown, p=['ITEL has developed a new editor since 1992',  'It is now 1996'], q='Did ITEL develop a new editor in 1993?', h='ITEL developed a new editor in 1993', a='don\'t know').

/*<comment> Similarly with activity verbs and adverbial modification: </comment>*/
 
fracasProblem(id=254, fracas_answer=unknown, p=['ITEL has expanded since 1992',  'It is now 1996'], q='Did ITEL expand in 1993?', h='ITEL expanded in 1993', a='don\'t know').

/*<comment> Also, the position of the since adverbial affects the range of readings available: </comment>*/
 
fracasProblem(id=255, fracas_answer=yes, p=['Since 1992 ITEL has made a loss',  'It is now 1996'], q='Did ITEL make a loss in 1993?', h='ITEL made a loss in 1993').
fracasProblem(id=256, fracas_answer=unknown, p=['ITEL has made a loss since 1992',  'It is now 1996'], q='Did ITEL make a loss in 1993?', h='ITEL made a loss in 1993', a='don\'t know, on one reading of the premise').
fracasProblem(id=257, fracas_answer=yes, p=['ITEL has made a loss since 1992',  'It is now 1996'], q='Did ITEL make a loss in 1993?', h='ITEL made a loss in 1993', a='Yes, on one reading of the premise', note='Note that this is formally identical with preceding').
fracasProblem(id=258, fracas_answer=no, p=['In March 1993 APCOM founded ITEL'], q='Did ITEL exist in 1992?', h='ITEL existed in 1992', a='No').

/*<comment> (258) involves the lexical semantics of found </comment>*/
 

/*<comment class=subsection> 72 Temporal Adverbials </comment>*/
 

/*<comment class=subsubsection> 721 Indexicals </comment>*/
 

/*<comment> Non-context dependent indexicals are reasonably straightforward: </comment>*/
 
fracasProblem(id=259, fracas_answer=yes, p=['The conference started on July 4th, 1994',  'It lasted 2 days'], q='Was the conference over on July 8th, 1994?', h='The conference was over on July 8th, 1994').

/*<comment> Context dependent indexicals (eg today, yesterday) are evaluated with respect to some temporal reference point (eg now): </comment>*/
 
fracasProblem(id=260, fracas_answer=yes, p=['Yesterday APCOM signed the contract',  'Today is Saturday, July 14th'], q='Did APCOM sign the contract Friday, 13th?', h='APCOM signed the contract Friday, 13th', note='The odd punctuation in the question was in the original').

/*<comment class=subsubsection> 722 Before, After (Temporal Subordinate Clauses) </comment>*/
 

/*<comment>Ignoring counterfactual readings, 'before'and'after'have the followingtransitivity properties: if X, Y and Z are either all state or accomplishmentor achievement or activity denoting sentences we have X &lt; Y Y &lt; Z X &lt; Z where &lt; \in {before; after} </comment>*/
 
fracasProblem(id=261, fracas_answer=yes, p=['Smith left before Jones left',  'Jones left before Anderson left'], q='Did Smith leave before Anderson left?', h='Smith left before Anderson left', note='Original is degenerate problem; this is my fabrication').
fracasProblem(id=262, fracas_answer=yes, p=['Smith left after Jones left',  'Jones left after Anderson left'], q='Did Smith leave after Anderson left?', h='Smith left after Anderson left').

/*<comment> In general transitivity does not hold when we mix aspectual classes in the premises: </comment>*/
 
fracasProblem(id=263, fracas_answer=unknown, p=['Smith was present after Jones left',  'Jones left after Anderson was present'], q='Was Smith present after Anderson was present?', h='Smith was present after Anderson was present', a='don\'t know').

/*<comment> If X and Y are either all accomplishment or achievement denoting sentences with simple tenses'before'and'after'are inverses of each other: </comment>*/
 

/*<comment> X before Y iff Y after X </comment>*/
 
fracasProblem(id=264, fracas_answer=yes, p=['Smith left',  'Jones left',  'Smith left before Jones left'], q='Did Jones leave after Smith left?', h='Jones left after Smith left', note='Original is degenerate problem; this is my fabrication').
fracasProblem(id=265, fracas_answer=yes, p=['Smith left',  'Jones left',  'Smith left after Jones left'], q='Did Jones leave before Smith left?', h='Jones left before Smith left').
fracasProblem(id=266, fracas_answer=yes, p=['Smith left',  'Jones left',  'Jones left before Smith left'], q='Did Smith leave after Jones left?', h='Smith left after Jones left').
fracasProblem(id=267, fracas_answer=yes, p=['Jones revised the contract',  'Smith revised the contract',  'Jones revised the contract before Smith did'], q='Did Smith revise the contract after Jones did?', h='Smith revised the contract after Jones did').
fracasProblem(id=268, fracas_answer=yes, p=['Jones revised the contract',  'Smith revised the contract',  'Jones revised the contract after Smith did'], q='Did Smith revise the contract before Jones did?', h='Smith revised the contract before Jones did').

/*<comment> In general this is not so with activity verbs: </comment>*/
 
fracasProblem(id=269, fracas_answer=unknown, p=['Smith swam',  'Jones swam',  'Smith swam before Jones swam'], q='Did Jones swim after Smith swam?', h='Jones swam after Smith swam', a='don\'t know').

/*<comment> However we do get </comment>*/
 
fracasProblem(id=270, fracas_answer=yes, p=['Smith swam to the shore',  'Jones swam to the shore',  'Smith swam to the shore before Jones swam to the shore'], q='Did Jones swim to the shore after Smith swam to the shore?', h='Jones swam to the shore after Smith swam to the shore').

/*<comment>Here the PP to the shore provides an end point or conclusion for the activity </comment>*/
 

/*<comment> Before and after are not inverses for state-denoting sentences: </comment>*/
 
fracasProblem(id=271, fracas_answer=unknown, p=['Smith was present',  'Jones was present',  'Smith was present after Jones was present'], q='Was Jones present before Smith was present?', h='Jones was present before Smith was present', a='don\'t know').
fracasProblem(id=272, fracas_answer=unknown, p=['Smith was present',  'Jones was present',  'Smith was present before Jones was present'], q='Was Jones present after Smith was present?', h='Jones was present after Smith was present', a='don\'t know').
fracasProblem(id=273, fracas_answer=unknown, p=['Smith was writing a report',  'Jones was writing a report',  'Smith was writing a report before Jones was writing a report'], q='Was Jones writing a report after Smith was writing a report?', h='Jones was writing a report after Smith was writing a report', a='don\'t know').
fracasProblem(id=274, fracas_answer=unknown, p=['Smith was writing a report',  'Jones was writing a report',  'Smith was writing a report after Jones was writing a report'], q='Was Jones writing a report before Smith was writing a report?', h='Jones was writing a report before Smith was writing a report', a='don\'t know').

/*<comment> Also before, but not after, can have a counterfactual meaning Whether this is a distinct sense of before is open to debate: </comment>*/
 
fracasProblem(id=275, fracas_answer=unknown, p=['Smith left the meeting before he lost his temper'], q='Did Smith lose his temper?', h='Smith lost his temper', a='don\'t know').

/*<comment>With when things are even more complicated The problem is that itis often very difficult to tease apart the temporal from the causaldimension of when, cf </comment>*/
 
fracasProblem(id=276, fracas_answer=undef, p=['When they opened the M25, traffic increased'], q=' ', h=' ', a='', note='Original is degenerate problem; no question or answer given').

/*<comment class=subsubsection> 723 In, For and On Temporal Adverbials </comment>*/
 

/*<comment> In and for adverbials can be used as tests for the aspectual class of verb phrases (or sentences) </comment>*/
 
fracasProblem(id=277, fracas_answer=unknown, p=['Smith lived in Birmingham in 1991'], q='Did Smith live in Birmingham in 1992?', h='Smith lived in Birmingham in 1992', a='don\'t know', why='Stative').
fracasProblem(id=278, fracas_answer=no, p=['Smith wrote his first novel in 1991'], q='Did Smith write his first novel in 1992?', h='Smith wrote his first novel in 1992', a='No', why='(Unrepeatable) accomplishment').
fracasProblem(id=279, fracas_answer=no, p=['Smith wrote a novel in 1991'], q='Did Smith write it in 1992?', h='Smith wrote it in 1992', a='No', why='(Unrepeatable) accomplishment').
fracasProblem(id=280, fracas_answer=unknown, p=['Smith wrote a novel in 1991'], q='Did Smith write a novel in 1992?', h='Smith wrote a novel in 1992', a='don\'t know', why='(Repeatable) accomplishment').
fracasProblem(id=281, fracas_answer=unknown, p=['Smith was running a business in 1991'], q='Was Smith running it in 1992?', h='Smith was running it in 1992', a='don\'t know', why='Activity').
fracasProblem(id=282, fracas_answer=no, p=['Smith discovered a new species in 1991'], q='Did Smith discover it in 1992?', h='Smith discovered it in 1992', a='No', why='(Unrepeatable) achievement').
fracasProblem(id=283, fracas_answer=unknown, p=['Smith discovered a new species in 1991'], q='Did Smith discover a new species in 1992?', h='Smith discovered a new species in 1992', a='don\'t know', why='(Repeatable) achievement').
fracasProblem(id=284, fracas_answer=yes, p=['Smith wrote a report in two hours',  'Smith started writing the report at 8 am'], q='Had Smith finished writing the report by 11 am?', h='Smith had finished writing the report by 11 am', why='Accomplishment').
fracasProblem(id=285, fracas_answer=unknown, p=['Smith wrote a report in two hours'], q='Did Smith spend two hours writing the report?', h='Smith spent two hours writing the report', a='don\'t know', why='Smith may have written the report in less than two hours It is unclear whether there are two different readings for the premise: one where Smith takes exactly two hours, and one where he does it within two hours').
fracasProblem(id=286, fracas_answer=no, p=['Smith wrote a report in two hours'], q='Did Smith spend more than two hours writing the report?', h='Smith spent more than two hours writing the report', a='No').
fracasProblem(id=287, fracas_answer=unknown, p=['Smith wrote a report in two hours'], q='Did Smith write a report in one hour?', h='Smith wrote a report in one hour', a='don\'t know').
fracasProblem(id=288, fracas_answer=yes, p=['Smith wrote a report in two hours'], q='Did Smith write a report?', h='Smith wrote a report').
fracasProblem(id=289, fracas_answer=no, p=['Smith discovered a new species in two hours'], q='Did Smith spend two hours discovering the new species?', h='Smith spent two hours discovering the new species', a='No', why='Achievements are typically (more or less) instantaneous').
fracasProblem(id=290, fracas_answer=yes, p=['Smith discovered a new species in two hours'], q='Did Smith discover a new species?', h='Smith discovered a new species').
fracasProblem(id=291, fracas_answer=yes, p=['Smith discovered many new species in two hours'], q='Did Smith spend two hours discovering new species?', h='Smith spent two hours discovering new species', a='?Yes', why='Repeated achievement can last two hours').
fracasProblem(id=292, fracas_answer=unknown, p=['Smith was running his own business in two years'], q='Did Smith spend two years running his own business?', h='Smith spent two years running his own business', a='don\'t know', why='Premise refers to time taken to inception of activity, not duration of activity').
fracasProblem(id=293, fracas_answer=unknown, p=['Smith was running his own business in two years'], q='Did Smith spend more than two years running his own business?', h='Smith spent more than two years running his own business', a='don\'t know', why='Cf similar inference for accomplishment, (286)').
fracasProblem(id=294, fracas_answer=yes, p=['Smith was running his own business in two years'], q='Did Smith run his own business?', h='Smith ran his own business').
fracasProblem(id=295, fracas_answer=unknown, p=['In two years Smith owned a chain of businesses'], q='Did Smith own a chain of business for two years?', h='Smith owned a chain of business for two years', a='don\'t know', why='States behave like activities', note='Sic: the original did have chain of business in the question').
fracasProblem(id=296, fracas_answer=unknown, p=['In two years Smith owned a chain of businesses'], q='Did Smith own a chain of business for more than two years?', h='Smith owned a chain of business for more than two years', a='don\'t know', note='Sic: the original did have chain of business in the question').
fracasProblem(id=297, fracas_answer=yes, p=['In two years Smith owned a chain of businesses'], q='Did Smith own a chain of business?', h='Smith owned a chain of business', note='Sic: the original did have chain of business in the question').
fracasProblem(id=298, fracas_answer=yes, p=['Smith lived in Birmingham for two years'], q='Did Smith live in Birmingham for a year?', h='Smith lived in Birmingham for a year', why='State').
fracasProblem(id=299, fracas_answer=no, p=['Smith lived in Birmingham for two years'], q='Did Smith live in Birmingham for exactly a year?', h='Smith lived in Birmingham for exactly a year', a='No').
fracasProblem(id=300, fracas_answer=yes, p=['Smith lived in Birmingham for two years'], q='Did Smith live in Birmingham?', h='Smith lived in Birmingham').
fracasProblem(id=301, fracas_answer=yes, p=['Smith ran his own business for two years'], q='Did Smith run his own business for a year?', h='Smith ran his own business for a year', why='Activity').
fracasProblem(id=302, fracas_answer=yes, p=['Smith ran his own business for two years'], q='Did Smith run his own business?', h='Smith ran his own business').
fracasProblem(id=303, fracas_answer=yes, p=['Smith wrote a report for two hours'], q='Did Smith write a report for an hour?', h='Smith wrote a report for an hour', why='Accomplishment').
fracasProblem(id=304, fracas_answer=unknown, p=['Smith wrote a report for two hours'], q='Did Smith write a report?', h='Smith wrote a report', a='don\'t know', why='He may not have finished it').
fracasProblem(id=305, fracas_answer=undef, p=['Smith discovered a new species for an hour'], q=' ', h=' ', a='', note='Original is degenerate problem; no question or answer given').
fracasProblem(id=306, fracas_answer=yes, p=['Smith discovered new species for two years'], q='Did Smith discover new species?', h='Smith discovered new species', why='Repeated achievement').

/*<comment class=subsubsection> 724 Quantificational Adverbials </comment>*/
 
fracasProblem(id=307, fracas_answer=yes, p=['In 1994 ITEL sent a progress report every month'], q='Did ITEL send a progress report in July 1994?', h='ITEL sent a progress report in July 1994').

/*<comment> Quantificational adverbials also introduce scope ambiguities with respect to other quantified NPs </comment>*/
 
fracasProblem(id=308, fracas_answer=undef, p=['Smith wrote to a representative every week'], q='Is there a representative that Smith wrote to every week?', h='There is a representative that Smith wrote to every week', a='Yes on one scoping; unknown on another scoping').

/*<comment class=subsection> 73 Anaphoric Dimension </comment>*/
 

/*<comment>Rhetorical relations like narrative progression are defeasibleinterpretation principles They depend on a theory of action andcausation and general world knowledge (cf (309) and (310)) </comment>*/
 
fracasProblem(id=309, fracas_answer=undef, p=['Smith left the house at a quarter past five',  'She took a taxi to the station and caught the first train to Luxembourg'], q=' ', h=' ', a='', note='Original is degenerate problem; no question or answer given').
fracasProblem(id=310, fracas_answer=undef, p=['Smith lost some files',  'They were destroyed when her hard disk crashed'], q=' ', h=' ', a='', note='Original is degenerate problem; no question or answer given').
fracasProblem(id=311, fracas_answer=yes, p=['Smith had left the house at a quarter past five',  'Then she took a taxi to the station'], q='Did Smith leave the house before she took a taxi to the station?', h='Smith left the house before she took a taxi to the station').

/*<comment class=subsection> 74 Adverbs of Quantification </comment>*/
 
fracasProblem(id=312, fracas_answer=yes, p=['ITEL always delivers reports late',  'In 1993 ITEL delivered reports'], q='Did ITEL delivered reports late in 1993?', h='ITEL delivered reports late in 1993', note='Sic: the original did have delivered in the question').
fracasProblem(id=313, fracas_answer=no, p=['ITEL never delivers reports late',  'In 1993 ITEL delivered reports'], q='Did ITEL delivered reports late in 1993?', h='ITEL delivered reports late in 1993', a='No', note='Sic: the original did have delivered in the question').

/*<comment class=subsection> 75 Some more Complex Examples </comment>*/
 
fracasProblem(id=314, fracas_answer=yes, p=['Smith arrived in Paris on the 5th of May, 1995',  'Today is the 15th of May, 1995',  'She is still in Paris'], q='Was Smith in Paris on the 7th of May, 1995?', h='Smith was in Paris on the 7th of May, 1995').
fracasProblem(id=315, fracas_answer=yes, p=['When Smith arrived in Katmandu she had been travelling for three days'], q='Had Smith been travelling the day before she arrived in Katmandu?', h='Smith had been travelling the day before she arrived in Katmandu').
fracasProblem(id=316, fracas_answer=yes, p=['Jones graduated in March and has been employed ever since',  'Jones has been unemployed in the past'], q='Was Jones unemployed at some time before he graduated?', h='Jones was unemployed at some time before he graduated').
fracasProblem(id=317, fracas_answer=yes, p=['Every representative has read this report',  'No two representatives have read it at the same time',  'No representative took less than half a day to read the report',  ' There are sixteen representatives'], q='Did it take the representatives more than a week to read the report?', h='It took the representatives more than a week to read the report').
fracasProblem(id=318, fracas_answer=no, p=['While Jones was updating the program, Mary came in and told him about the board meeting',  'She finished before he did'], q='Did Mary \'s story last as long as Jones \'s updating the program?', h='Mary \'s story lasted as long as Jones \'s updating the program', a='No').
fracasProblem(id=319, fracas_answer=yes, p=['Before APCOM bought its present office building, it had been paying mortgage interest on the previous one for 8 years',  'Since APCOM bought its present office building it has been paying mortgage interest on it for more than 10 years'], q='Has APCOM been paying mortgage interest for a total of 15 years or more?', h='APCOM has been paying mortgage interest for a total of 15 years or more').
fracasProblem(id=320, fracas_answer=yes, p=['When Jones got his job at the CIA, he knew that he would never be allowed to write his memoirs'], q='Is it the case that Jones is not and will never be allowed to write his memoirs?', h='It is the case that Jones is not and will never be allowed to write his memoirs').
fracasProblem(id=321, fracas_answer=yes, p=['Smith has been to Florence twice in the past',  'Smith will go to Florence twice in the coming year'], q='Two years from now will Smith have been to Florence at least four times?', h='Two years from now Smith will have been to Florence at least four times').
fracasProblem(id=322, fracas_answer=yes, p=['Last week I already knew that when, in a month \'s time, Smith would discover that she had been duped she would be furious'], q='Will it be the case that in a few weeks Smith will discover that she has been duped; and will she be furious?', h='It will be the case that in a few weeks Smith will discover that she has been duped; and she will be furious').
fracasProblem(id=323, fracas_answer=yes, p=['No one gambling seriously stops until he is broke',  'No one can gamble when he is broke'], q='Does everyone who starts gambling seriously stop the moment he is broke?', h='Everyone who starts gambling seriously stops the moment he is broke').
fracasProblem(id=324, fracas_answer=yes, p=['No one who starts gambling seriously stops until he is broke'], q='Does everyone who starts gambling seriously continue until he is broke?', h='Everyone who starts gambling seriously continues until he is broke').
fracasProblem(id=325, fracas_answer=yes, p=['Nobody who is asleep ever knows that he is asleep',  'But some people know that they have been asleep after they have been asleep'], q='Do some people discover that they have been asleep?', h='Some people discover that they have been asleep').

/*<comment class=section> 8 VERBS </comment>*/
 

/*<comment class=subsection> 81 Aspectual Classes </comment>*/
 
fracasProblem(id=326, fracas_answer=yes, p=['ITEL built MTALK in 1993'], q='Did ITEL finish MTALK in 1993?', h='ITEL finished MTALK in 1993').
fracasProblem(id=327, fracas_answer=unknown, p=['ITEL was building MTALK in 1993'], q='Did ITEL finish MTALK in 1993?', h='ITEL finished MTALK in 1993', a='don\'t know').
fracasProblem(id=328, fracas_answer=yes, p=['ITEL won the contract from APCOM in 1993'], q='Did ITEL win a contract in 1993?', h='ITEL won a contract in 1993').
fracasProblem(id=329, fracas_answer=unknown, p=['ITEL was winning the contract from APCOM in 1993'], q='Did ITEL win a contract in 1993?', h='ITEL won a contract in 1993', a='don\'t know').
fracasProblem(id=330, fracas_answer=yes, p=['ITEL owned APCOM from 1988 to 1992'], q='Did ITEL own APCOM in 1990?', h='ITEL owned APCOM in 1990').

/*<comment class=subsection> 82 Distributive and Collective Predication </comment>*/
 
fracasProblem(id=331, fracas_answer=yes, p=['Smith and Jones left the meeting'], q='Did Smith leave the meeting?', h='Smith left the meeting').
fracasProblem(id=332, fracas_answer=yes, p=['Smith and Jones left the meeting'], q='Did Jones leave the meeting?', h='Jones left the meeting').
fracasProblem(id=333, fracas_answer=yes, p=['Smith, Anderson and Jones met'], q='Was there a group of people that met?', h='There was a group of people that met').

/*<comment class=section> 9 ATTITUDES </comment>*/
 

/*<comment class=subsection> 91 Epistemic, Intentional and Reportive Attitudes </comment>*/
 
fracasProblem(id=334, fracas_answer=yes, p=['Smith knew that ITEL had won the contract in 1992'], q='Did ITEL win the contract in 1992?', h='ITEL won the contract in 1992').
fracasProblem(id=335, fracas_answer=unknown, p=['Smith believed that ITEL had won the contract in 1992'], q='Did ITEL win the contract in 1992?', h='ITEL won the contract in 1992', a='don\'t know', note='Sic: the original had believed / said / denied / feared / hoped in the premise I changed this to just tried').
fracasProblem(id=336, fracas_answer=yes, p=['ITEL managed to win the contract in 1992'], q='Did ITEL win the contract in 1992?', h='ITEL won the contract in 1992').
fracasProblem(id=337, fracas_answer=unknown, p=['ITEL tried to win the contract in 1992'], q='Did ITEL win the contract in 1992?', h='ITEL won the contract in 1992', a='don\'t know', note='Sic: the original had tried / wanted in the premise I changed this to just tried').
fracasProblem(id=338, fracas_answer=yes, p=['It is true that ITEL won the contract in 1992'], q='Did ITEL win the contract in 1992?', h='ITEL won the contract in 1992').
fracasProblem(id=339, fracas_answer=no, p=['It is false that ITEL won the contract in 1992'], q='Did ITEL win the contract in 1992?', h='ITEL won the contract in 1992', a='No').

/*<comment class=subsection> 92 Preceptive Attitudes: See with Bare Infinitive Complements </comment>*/
 

/*<comment class=subsubsection> 921 Inferences we do not get </comment>*/
 
fracasProblem(id=340, fracas_answer=unknown, p=['Smith saw Jones sign the contract',  'If Jones signed the contract his heart was beating'], q='Did Smith see Jones\' heart beat?', h='Smith saw Jones\' heart beat', a='don\'t know').
fracasProblem(id=341, fracas_answer=unknown, p=['Smith saw Jones sign the contract',  'When Jones signed the contract his heart was beating'], q='Did Smith see Jones\' heart beat?', h='Smith saw Jones\' heart beat', a='don\'t know').

/*<comment class=subsubsection> 922 Veridicality </comment>*/
 

/*<comment> a saw \phi &lt; \phi </comment>*/
 
fracasProblem(id=342, fracas_answer=yes, p=['Smith saw Jones sign the contract'], q='Did Jones sign the contract?', h='Jones signed the contract').

/*<comment class=subsubsection> 923 Substitution </comment>*/
 

/*<comment> a saw \phi(b), b = c &lt; a saw \phi(c) </comment>*/
 
fracasProblem(id=343, fracas_answer=yes, p=['Smith saw Jones sign the contract',  'Jones is the chairman of ITEL'], q='Did Smith see the chairman of ITEL sign the contract?', h='Smith saw the chairman of ITEL sign the contract').

/*<comment class=subsubsection> 924 Existential instantiation </comment>*/
 

/*<comment> a saw \phi(b) &lt; 9x a saw \phi(x) </comment>*/
 
fracasProblem(id=344, fracas_answer=yes, p=['Helen saw the chairman of the department answer the phone',  'The chairman of the department is a person'], q='Is there anyone whom Helen saw answer the phone?', h='There is someone whom Helen saw answer the phone').

/*<comment class=subsubsection> 925 Conjunction distribution </comment>*/
 

/*<comment> a saw \phi and / &lt; a saw \phi and a saw / </comment>*/
 
fracasProblem(id=345, fracas_answer=yes, p=['Smith saw Jones sign the contract and his secretary make a copy'], q='Did Smith see Jones sign the contract?', h='Smith saw Jones sign the contract').

/*<comment class=subsubsection> 926 Disjunction distribution </comment>*/
 

/*<comment> A saw \phi or / &lt; A saw \phi or A saw / </comment>*/
 
fracasProblem(id=346, fracas_answer=yes, p=['Smith saw Jones sign the contract or cross out the crucial clause'], q='Did Smith either see Jones sign the contract or see Jones cross out the crucial clause?', h='Smith either saw Jones sign the contract or saw Jones cross out the crucial clause').

fracasProblem(_,_,_,_) :- fail.
fracasProblem(_,_,_,_,_) :- fail.
fracasProblem(_,_,_,_,_,_) :- fail.
fracasProblem(_,_,_,_,_,_,_) :- fail.
fracasProblem(_,_,_,_,_,_,_,_) :- fail.
fracasProblem(_,_,_,_,_,_,_,_,_) :- fail.

