#
#    File: testMB.perl
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

use Time::HiRes qw/time/;
use File::Copy;

use Data::Dumper;

# lists for every prover a string whose occurence in the prover's output indicates that the prover found a proof
my %builders = ("prover9" => "end of model");

# lists for every builder the command to be used to call it
my %commands = ("prover9" => "mace4 -c ");



$builder = $ARGV[0];
$dir = $ARGV[1];


$builderCommand = $commands{$builder};
my $provenSignal = $builders{$builder};

open LOG, "> $dir/mb-$builder.log";

# for every file:
opendir my $direc, "$dir" or die "Cannot open directory: $!";
my @files = readdir $direc;
closedir $direc;

%done = ();
%tried = ();
%result = ();

$count = 0;

for $file (@files) {

    

   
    unless($file =~ /$builder/) { next; }
    unless($file =~ /.in/) { next; }

    @array = split("-",$file);
    unless(@array == 5) {next;}

   

    if($tried{$file}) { 
                         next; }
    

    
    $posFile = $array[0]."-".$array[1]."-".$array[2]."-".$array[3]."-"."neg.in";
    $negFile = $array[0]."-".$array[1]."-".$array[2]."-".$array[3]."-"."pos.in";

    if($array[3] eq "contradictory") {
      if($file eq $posFile && ! $tried{$negFile}) {
	$file = $negFile;
        push(@files, $posFile);
      }
    } elsif( $file eq $negFile && ! $tried{$posFile}) {
        $file = $posFile;
        push(@files, $negFile);
    }

    $tried{$file} = 1;
    print(LOG "$file\t");

    print("$file\n");
copy("$dir/$file", "$dir/$builder.in") or die "";

    open $handle, "$builderCommand < $dir/$builder.in 2>/dev/null |" or die "Can't open $builder.in: $!";
 my $time = time;
     $count++;


my $TIMEOUT_IN_SECONDS = 30;
eval {
    local $SIG{ALRM} = sub { die "alarm\n" };
    alarm($TIMEOUT_IN_SECONDS);
    
while(1) {
    $_ = <$handle>;
    
    if(defined($_)) {
            if($_ =~ /error/) {
                print("$builder : $_\n");
                print(LOG "-3\n"); # error
                $result{$file} = -3;
                last;
	    }
	    if($_ =~ /$provenSignal/) {
                $time = time-$time;
                print("$builder $_");
                print("   After $time seconds\n");
                print(LOG "$time\n"); # terminated successfully
                $result{$file} = $time;
                last;
            }
	} else {
            print("failed\n");
            print(LOG "-1\n"); # terminated with failure
            $result{$file} = -1;
	    last;
	}
   
}




    alarm(0);
};
if ($@) {
    print("TIMEOUT\n");
    print(LOG "-2\n"); # timeout
    $result{$file} = -2;
    # handle timeout condition.
}



}

print(LOG "\n");

print(Dumper(\%result));

# EVALUATE

%sectionsOwn = ("FirstOrder" => [0,99], "Modality" => [100,199], "KnowledgeAndBelief" => [200,299], "GQ" => [300,399], "Modifiers" => [400,499], "deDicto" => [500,599]);
%sectionsFracas = ("KnowledgeAndBelief" => [334,346], "GQ" => [1,80], "Modifiers" => [197,219]);

print(Dumper(\%sectionsOwn));

%stat = ();
%final = ();


for $file (keys(%result)) {
    @data = split("-",$file);
    print(Dumper(\@data));
    # [., own/fracas, num, valid/..., pos/neg.in]
    $id = $data[1]."-".$data[2];
    if(defined($final{$id})) { next; }
    $posFile = $data[0]."-".$id."-".$data[3]."-pos.in";
    $negFile = $data[0]."-".$id."-".$data[3]."-neg.in";
    if($data[3] eq 'cotradictory') {
        my $temp = $posFile;
	$posFile = $negFile;
        $negFile = $temp;
    }

    unless(defined($result{$posFile})) {
	print(LOG "WARNING $file\n");
    }

    @resultForThisID = ($data[3],$result{$posFile}, $result{$negFile});
    $final{$id} = [$data[3],$result{$posFile}, $result{$negFile}];
    # get Category
    my $category = getCategory($data[1],$data[2]);
    print("$id $category\n");
    
    updateStat($category, @resultForThisID, $id);
}

print(Dumper(\%final));
print("STAT ".Dumper(\%stat));
print("TIMES ".Dumper(\%times));

print(LOG Dumper(\%final));
print(LOG "STAT ".Dumper(\%stat));
print(LOG "TIMES ".Dumper(\%times));

close(LOG);


open(LOG2,"> $dir/mb-$builder.resu");
print(LOG2 Dumper(\%final));
print(LOG2 '$mb_'.$builder.' = $VAR1;'."\n");
close(LOG2);

exit 1;

sub updateStat {
    my $cat = shift;
    my $status = shift;
    my $resultP = shift;
    my $resultN = shift;
    my $id = shift;

    $num = 1;
    if($resultP >= 0) {
	$num = $num*2;
        push(@{$times{$cat}}, $resultP);
    } elsif($resultN >= 0) {
        $num = $num*3;
        push(@{$times{$cat}}, $resultN);
    } else {
        $num = $resultP;
    }
    
    push(@{$stat{$cat}{$status}{$num}}, $id);

    
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
