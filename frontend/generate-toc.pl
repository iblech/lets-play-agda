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
      my $name = $1;
      unless($level == 0) {
        if($name =~ s/\s*🚧//) {
          print "  " x $level, "<li>$name";
        } else {
          print "  " x $level, "<li><a href=\"$module.html\">$name</a>";
        }
      }
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
        Computational content of classical logic
        <ol>
          <li>
            Convenient fictions
            <ol>
              <li>Minimas</li>
              <li>Drinkers</li>
            </ol>
          </li>
          <li>Sarcastic interpretation of classical logic</li>
          <li>Case study: Dickson's lemma</li>
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
