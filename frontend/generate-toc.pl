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
  while(defined(my $line = <$fh>)) {
    chomp $line;
    if(not $title and $line =~ /^#\s*(.*)$/) {
      $title++;
      print "  " x $level, "<li><a href=\"$module.html\">$1</a>" unless $level == 0;
    }

    if($line =~ /import\s+([^\s]*)/) {
      print "<ol>\n" unless $childs++;
      visit($level + 1, $1) unless $seen{$1};
    }
  }

  if($childs) {
    print "  " x $level, "</ol>";
  }
  print "</li>\n" unless $level == 0;
}

visit(0, $ARGV[0]);
