#!/usr/bin/env perl

use warnings;
use strict;

sub src {
  my $module = shift;

  $module =~ s#\.#/#g;
  return "$module.lagda.md";
}

my %seen;

sub visit {
  my ($level, $module) = @_;
  $seen{$module}++;

  open my $fh, "<", src($module) or die "Couldn't open $module: $!\n";
  
  my $title;
  my $childs;
  my $in_code;
  while(defined(my $line = <$fh>)) {
    if(not $title and $line =~ /^#\s*(.*?)(?:\s*\/\/.*)?$/) {
      $title++;
      print "  " x $level, "<li><a href=\"$module.html\">$1</a>" unless $level == 0;
    }

    if($line =~ /```/) {
      $in_code = ! $in_code;
    }

    if($in_code and $line =~ /^(?:open\s+)?import\s+([^\s]*)/) {
      unless($seen{$1}) {
        print "<ol>\n" unless $childs++;
        visit($level + 1, $1);
      }
    }
  }

  if($level == 0) {
    print <<EOF;
      <li>
        Agda as a proof language
        <ol>
          <li>Relations</li>
          <li>
            Equality
            <ol>
              <li>Definition</li>
              <li>Basic usage</li>
              <li>Equational reasoning</li>
            </ol>
          </li>
          <li>Results about natural numbers</li>
          <li>Termination and well-founded induction</li>
        </ol>
      </li>
      <li>
        Verified algorithms
        <ol>
          <li>Post-hoc verification</li>
          <li>Correct by construction</li>
          <li>Case study: insertion sort</li>
          <li>Case study: compiler &amp; interpreter</li>
        </ol>
      </li>
      <li>
        Computational content of classical logic
        <ol>
          <li>Minimas as convenient fiction</li>
          <li>Sarcastic interpretation of classical logic</li>
          <li>Case study: Dickson's lemma</li>
        </ol>
      </li>
      <li>
        Cubical Agda
        <ol>
          <li>Issues with standard Agda</li>
          <li>A mathematical rosetta stone</li>
          <li>First steps</li>
        </ol>
      </li>
EOF
  }

  if($childs) {
    print "  " x $level, "</ol>";
  }
  print "</li>\n" unless $level == 0 or not $title;
}

visit(0, $ARGV[0]);
