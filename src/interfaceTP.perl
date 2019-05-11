:
eval 'exec perl -w -S $0 ${1+"$@"}'
 if 0;

#
#    File: interfaceTP.perl
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

#use Data::Dumper;

# lists for every prover a string whose occurence in the prover's output indicates that the prover found a proof
my %provers = ("otter" => "proof of the theorem", "bliksem" => "found a proof", "prover9" => "THEOREM PROVED", "eprover" => "Proof found!", "spass" => "Proof found.");

# lists for every prover the command to be used to call it
my %commands = ("otter" => "otter", "prover9" => "prover9 tpinput/prover9.in", "bliksem" => "bliksem", "eprover" => "eprover --tptp-in", "spass" => "tptp2dfg tpinput/spass.in tpinput/spass2.in; SPASS tpinput/spass2.in");



my %handles = ();

my %results = ();

my %read = ();

my %times = ();

my $timeout = -1;

while ($ARGV[0] =~ /--/) {
     my @parameter = split("=",$ARGV[0]);
     shift(@ARGV);
     if($parameter[0] eq '--timeout') {
          $timeout = $parameter[1];
     }
}

for $prover (keys(%provers)) {
    if($ARGV[0] =~ $prover) {
        $proverCommand = $commands{$prover};
        open $handles{$prover}, "$proverCommand < tpinput/$prover.in 2>/dev/null |" or die "Can't open
+ $prover.in: $!";
        $times{$prover} = time;
        $results{$prover} = 0;
        $read{$prover} = 1;
    }
}


$reading = 1;

@sucessfulProvers = ();

while($reading) {
    $reading = 0;
    for $prover (keys(%read)) {
        my $fileHandle = $handles{$prover};
        if($read{$prover} && defined($_ = <$fileHandle>)) {
            if(0 || $_ =~ /error/) {
                print("$prover : $_\n");
	    }
            my $provenSignal = $provers{$prover};
	    if($_ =~ /$provenSignal/) {
                $times{$prover} = time-$times{$prover};
                print("$prover $_");
                print("   After ".($times{$prover})." seconds\n");
		$results{$prover} = 1;
                $read{$prover} = 0;
                $successfulProvers[@successfulProvers] = $prover;
            } else {
                $reading = 1;
            }
	} else {
	    $read{$prover} = 0;
	}
    }
}


my $success = 0;
open(OUTPUT,">tp.out");


if(@successfulProvers == 0) {
    print OUTPUT "unknown.\n";
} else {
    
    $proverList = "";
    for $prover (@successfulProvers) {
        $proverList .= "$prover,";
    }
    chop($proverList);

    print OUTPUT "proof.\n";
    print OUTPUT "engine([$proverList]).\n";
}



close(OUTPUT);

exit 1;
