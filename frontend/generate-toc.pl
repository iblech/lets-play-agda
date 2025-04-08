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

    if($in_code and $line =~ /import\s+([^\s]*)/) {
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
