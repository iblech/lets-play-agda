#!/usr/bin/env perl

use warnings;
use strict;

sub src {
  my $module = shift;

  $module =~ s#\.#/#g;
  return "$module.lagda.md";
}

my %seen;
$seen{$_}++ for qw< Padova2025.ProvingBasics.Equality.Reasoning.Core Agda.Primitive >;

sub visit {
  my ($level, $module) = @_;
  $seen{$module}++;

  open my $fh, "<", src($module) or die "Couldn't open $module: $!\n";
  
  my $title;
  my $childs;
  my $in_code;
  my $print_title;
  my $has_printed_title;
  while(defined(my $line = <$fh>)) {
    if(not $title and $line =~ /^#\s*(.*?)(?:\s*\/\/.*)?$/) {
      $title = $1;
      my $name = $1;
      $print_title = sub {
        my $has_children = shift;

        return if $level == 0;
        return if $has_printed_title++;

        my $under_construction = $title =~ /🚧/;

        if($has_children) {
          my $checked = $level <= 1 && !$under_construction ? " checked" : "";
          print "  " x $level, "<li><input$checked id=\"nav-$module\" type=\"checkbox\"><label for=\"nav-$module\">$title</label>";
        } else {
          if($name =~ s/ 🚧//) {
            print "  " x $level, "<li>$name";
          } else {
            print "  " x $level, "<li><a href=\"$module.html\">$name</a>";
          }
        }
      };
    }

    if($line =~ /```/) {
      $in_code = ! $in_code;
    }

    if($in_code and $line =~ /^(?:open\s+)?import\s+([^\s]*)/) {
      unless($seen{$1}) {
        unless($childs++) {
          die "--$module--" unless $print_title;
          $print_title->(1);
          print "<ol>\n";
        }
        visit($level + 1, $1);
      }
    }
  }

  die "--$module--" unless $print_title;
  $print_title->(0);

  if($level == 0) {
    print <<EOF;
      <li>
        <input id="nav-computational-content" type="checkbox">
        <label for="nav-computational-content">Computational content of classical logic</label>
        <ol>
          <li>
            <input id="nav-convenient-fictions" type="checkbox">
            <label for="nav-convenient-fictions">Convenient fictions</label>
            <ol>
              <li>Minimas</li>
              <li>Drinkers</li>
            </ol>
          </li>
          <li>Sarcastic interpretation of classical logic</li>
          <li>Case study: Dickson's lemma</li>
        </ol>
      </li>
      <li>
        <input id="nav-recreational" type="checkbox">
        <label for="nav-recreational">Recreational mathematics</label>
        <ol>
          <li>Fun with the axiom of choice</li>
          <li>The final digit of Graham's number</li>
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
