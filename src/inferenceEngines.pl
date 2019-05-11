/*************************************************************************

    File: inferenceEngines.pl
    Copyright (C) 2004,2005,2006 Patrick Blackburn & Johan Bos
    Modified by Michael Hahn (2015).

    This file is part of the source code for the paper

         Michael Hahn and Frank Richter (2015), Henkin Semantics for
         Reasoning with Natural Language, Journal of Language Modelling

    Contact: mhahn@sfs.uni-tuebingen.de

    It is adapted from the file inferenceEngines.pl of BB1, version 1.3
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
   Choose Inference Engines
========================================================================*/

inferenceEngines([prover9, spass,eprover]). %mhahn
modelBuilders([mace]). %mhahn


