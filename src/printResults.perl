#
#    File: printResults.perl
#    Copyright (C) 2015 Michael Hahn
#
#    This file is part of the source code for the paper
#
#         Michael Hahn and Frank Richter (2015), Henkin Semantics for
#         Reasoning with Natural Language, Journal of Language Modelling
#
#    Contact: mhahn@sfs.uni-tuebingen.de
#
#    This program is free software; you can redistribute it and/or
#    modify it under the terms of the GNU General Public License
#    as published by the Free Software Foundation; either version 2
#    of the License, or (at your option) any later version.
#
#    This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with this program; if not, write to the Free Software
#    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
#

#
# Prints the results of the inference engines on the testsuite in (mostly) Latex format.
# The section names of the test suite are encoded in the variables sectionsOwn and sections.
#
# Usage:
#    perl printResults.perl DIR
#   where DIR is the directory of the output of the inference engiens (e.g., tpinput)
#
#


use Time::HiRes qw/time/;
use File::Copy;
use Scalar::Util qw(looks_like_number);
use Data::Dumper;

$dir = $ARGV[0];


%sectionsOwn = ("FirstOrder" => [0,99], "Modality" => [100,199], "KnowledgeAndBelief" => [200,299], "GQ" => [300,399], "Modifiers" => [400,499], "deDicto" => [500,599]);
%sectionsFracas = ("KnowledgeAndBelief" => [334,346], "GQ" => [1,80], "Modifiers" => [197,219]);

@sections = ("FirstOrder", "Modality", "KnowledgeAndBelief", "GQ", "Modifiers", "deDicto");


%results = ();

@engines = ("Spass", "Prover9", "E", "Mace");


require "$dir/tp-prover9.resu";
require "$dir/tp-spass.resu";
require "$dir/tp-eprover.resu";
require "$dir/mb-prover9.resu";
# note that the file will not exist for the strong translation

%indivResultsNames = ("Spass",  => $tp_spass, "Prover9" => $tp_prover9, "Mace" => $mb_prover9, "E" => $tp_eprover);
# note that it is hard-wired that the fourth engine is a model builder and the others are provers





for($index=0;$index<@engines;$index++) {
    $engine = $engines[$index];
    $engineResults = $indivResultsNames{$engine};
    for $item (keys(%{$engineResults})) {
	@arr = split("-",$item);
        $category = getCategory($arr[0],$arr[1]);
        @result = @{${$engineResults}{$item}};
        $results{$category}{$result[0]}{$arr[1]}[$index] = [$result[1],$result[2]];
    }
}

#print(Dumper(\%results));

print(" \% DETAILED TABLE\n");

print("\n".'\begin{longtable}{|l||ll|ll|ll||ll|}'."\n".'\hline ID & \multicolumn{2}{|c|}{Spass}  & \multicolumn{2}{|c|}{Prover9}  & \multicolumn{2}{|c|}{E}  & \multicolumn{2}{||c|}{Mace} \\\\ \hline'."\n");
foreach $section (@sections) {
    $fracas = $results{"fracas-$section"};
    $own = $results{"own-$section"};
    if(defined($own)) {
        printSection("$section (Our Items)",$own);
    }
    if(defined($fracas)) {
        printSection("$section (Fracas)",$fracas);
    }
}
print("\\hline \n".'\end{longtable}'."\n");





sub printSection {
    print('\hline \hline \multicolumn{9}{|c|}{\textbf{');
    print(shift);
    print('}} \\\\');
    my $results = shift;
    my $valid = ${$results}{"valid"};
    my $contingent = ${$results}{"contingent"};
    my $contradictory = ${$results}{"contradictory"};
    
    printPart($valid,"Valid");
    printPart($contingent,"Contingent");
    printPart($contradictory,"Contradictory");
}

sub printPart {
    my $part = shift;
    my $classification = shift;
    if(keys(%{$part}) > 0) {
print('');

	print('\hline  \multicolumn{9}{|c|}{'.$classification.'} \\\\ \hline'."\n");
        printResults($part,$classification);
    }
}

sub printResults {
    my $results = shift;
    my $classification = shift;
    foreach $item (sort { $a <=> $b } keys(%{$results})) {
	print("$item ");
        my $i = 0;
        foreach $engineResult (@{${$results}{$item}}) {
            $i++;
            if($i == 4) {
		my $temp = ${$engineResult}[0];
                ${$engineResult}[0] = ${$engineResult}[1];
                ${$engineResult}[1] = $temp;
            }
            my $shouldHaveFoundPos = ($i ==4 && $classification ne "Contradictory") || ($classification eq "Valid");
            my $shouldHaveFoundNeg = ($i ==4 && $classification ne "Valid") || ($classification eq "Contradictory");
            unless(defined(${$engineResult}[0]) && (${$engineResult}[0])>0) {
                if($shouldHaveFoundPos) {
			${$engineResult}[0] = "--";
                } else {
			${$engineResult}[0] = "";
		}
            }
            unless(defined(${$engineResult}[1]) && (${$engineResult}[1])>0) {
                if($shouldHaveFoundNeg) {
			${$engineResult}[1] = "--";
                } else {
			${$engineResult}[1] = "";
		}
            }
            ${$engineResult}[0] = substr ${$engineResult}[0],0,5;
            ${$engineResult}[1] = substr ${$engineResult}[1],0,5;
            print(" & ".${$engineResult}[0]." & ".${$engineResult}[1]);
        }
        print(" \\\\\n");
    }
}


sub getCategory {
    my $set = shift;
    my $number = shift;
    if($set eq 'own') {
	$sets = \%sectionsOwn;
    } else {
        $sets = \%sectionsFracas;
    }
    for $section (keys(%{$sets})) {
        $bounds = ${$sets}{$section};
        if(${$bounds}[0] <= $number && ${$bounds}[1] >= $number) {
	    return $set."-".$section;
        }
    }
    return $set."-other";
}

print("\n\n \% RESULTS PER SECTION AND LABEL\n");

$totalForAll = 0;
@provedForAll = (0,0,0);
@modelsFoundForAll = ([0,0,0]);
$decidedForAll = 0;

# it is assumed below that the last entry will be the total number of proofs/models
@lessThanProvers = (0,0,0,0,0);
@lessThanModels = (0,0,0,0,0);
@lessThanMeasures = (0.1,1,2,5,10000);

$modelsWhereExpected = 0;

%totalPerLabel = ();

%sectionNames = ("Modality"=>"Modality", "KnowledgeAndBelief"=>"Know/bel.", "GQ"=>"Quant.", "Modifiers"=>"Adj.", "deDicto"=>"de dicto", "FirstOrder"=>"First-Order");
@labels = ("valid", "contradictory", "contingent");
foreach my $section (@sections) {
      print("\\hline ".$sectionNames{$section}."   ");
     foreach my $label (@labels) {
        
        my $total = 0;
        my @proved = (0,0,0);
        my @modelsFound = ([0,0,0]);
	my $decided = 0;
    for(my $q = 0; $q<2; $q++) {
	if($q == 0) {
	    $sectionKey = "own-$section";
        } else {
	    $sectionKey = "fracas-$section";
	}
    
	foreach my $item (keys(%{${$results{$sectionKey}}{$label}})) {
            $total ++;
            $resultsForItem = ${${$results{$sectionKey}}{$label}}{$item};
            my $someHasDecided = 0;
            # THEOREM PROVERS

            for(my $i=0;$i<3;$i++) {
                my $relevant;
		if($label eq "contingent") {
		    $relevant = -1;
		} elsif($label eq "valid") {
                    $relevant = ${${$resultsForItem}[$i]}[0];
		} else {
                    $relevant = ${${$resultsForItem}[$i]}[1];
		}
                if($relevant ne "--" && $relevant > 0) { 
@proved[$i]++; $someHasDecided = 1;

for(my $k = 0; $k<@lessThanMeasures; $k++) {
    if($relevant < $lessThanMeasures[$k]) {
	$lessThanProvers[$k]++;
    }
}
                }
	    }

            # MODEL BUILDER (hard-coded that there is just one, otherwise replace 0 by running index)
            if(looks_like_number(${${$resultsForItem}[3]}[0])) {
		if($label ne "contradictory") {
                    $modelsWhereExpected++;
                }
                 ${$modelsFound[0]}[0]++;
for(my $k = 0; $k<@lessThanMeasures; $k++) {
    if(${${$resultsForItem}[3]}[0] < $lessThanMeasures[$k]) {
	$lessThanModels[$k]++;
    }
}
	    }
            if(looks_like_number(${${$resultsForItem}[3]}[1])) {
                if($label ne "valid") {
                    $modelsWhereExpected++;
                }
                 ${$modelsFound[0]}[1]++;
for(my $k = 0; $k<@lessThanMeasures; $k++) {
    if(${${$resultsForItem}[3]}[1] < $lessThanMeasures[$k]) {
	$lessThanModels[$k]++;
    }
}
	    }
            if(looks_like_number(${${$resultsForItem}[3]}[0]) && looks_like_number(${${$resultsForItem}[3]}[1])) {
                 ${$modelsFound[0]}[2]++;
                 $someHasDecided=1;
	    }

            # GENERAL
	    if($someHasDecided) {
		$decided++;
	    }
	}
    }
	if($total > 0) {
	    $totalPerLabel{$label} += $total;
print(" &  $label &");
        $totalForAll += $total;
        print(" $total & ");
        for($i = 0; $i < @proved; $i++) {
            print($proved[$i]);print(" & ");
            $provedForAll[$i] += $proved[$i];
	}
        print(${$modelsFound[0]}[0]."/".${$modelsFound[0]}[1]."/".${$modelsFound[0]}[2]);
        ${$modelsFoundForAll[0]}[0] += ${$modelsFound[0]}[0];
        ${$modelsFoundForAll[0]}[1] += ${$modelsFound[0]}[1];
        ${$modelsFoundForAll[0]}[2] += ${$modelsFound[0]}[2];
        print(" & $decided \\\\ \n");
        $decidedForAll += $decided;
	    if($label ne "contingent") {
		$decidedByProofs += $decided;
	    }
	}
    }
}

       print("\\hline (total) & & $totalForAll & ");
        for($i = 0; $i < @provedForAll; $i++) {
            print($provedForAll[$i]);print(" & ");
	}
        print(${$modelsFoundForAll[0]}[0]."/".${$modelsFoundForAll[0]}[1]."/".${$modelsFoundForAll[0]}[2]);
        
        print(" & $decidedForAll\n");

print("\n\n   \% TOTAL PER LABEL \n");
print(Dumper(\%totalPerLabel));

print("\n\n   \% PERFORMANCE OF PROVERS \n");
my $expected = $totalPerLabel{"valid"} + $totalPerLabel{"contradictory"};
my $totalNumberOfProofs = 0;

for($i = 0; $i < 3; $i++) {
    my $proofs = $provedForAll[$i];
    $totalNumberOfProofs+=$proofs;
    print(percentage($proofs/$expected)." & ");
}
print(percentage($decidedByProofs/$expected));
print("\n");

sub percentage {
    return (int(1000*(shift)+0.5)/10)." \\%";
}



print("\n\n   \%   TIME (PROVER) \n");
for $i (@lessThanMeasures) {
    print("\& \$\\leq\$ ".$i." s  ");
}
print("\\\\ \n");
for $i (@lessThanProvers) {
    print(percentage($i/$totalNumberOfProofs)." \& ");
}
print("\n");


print("\n\n  \%  RESULTS OF BUILDER\n");
# here it is crucial that there is just one model builder...
$modelsCount = $lessThanModels[@lessThanModels-1];
$modelsExpected = $totalPerLabel{"valid"} + $totalPerLabel{"contradictory"} + 2*$totalPerLabel{"contingent"};
$recall = percentage($modelsWhereExpected/$modelsExpected);
$accuracy = percentage($modelsWhereExpected/$modelsCount);


print("Recall (Models found where expected)  & ".$recall."  \\\\\n");
print("Accuracy (Models expected where found) & ".$accuracy." \\\\\n");
print("\\% of models found within 0.1 seconds & ".percentage($lessThanModels[0]/$modelsCount)."  \\\\ \n");
print("\\% of models found within a second & ".percentage($lessThanModels[1]/$modelsCount)."  \\\\ \n");
print("\\% of models found within two seconds & ".percentage($lessThanModels[2]/$modelsCount)."  \\\\ \n");
print("\\% of models found within five seconds & ".percentage($lessThanModels[3]/$modelsCount)."  \n");




