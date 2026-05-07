#!/usr/bin/env perl
# Extract a single fenced code block from a literate Agda Markdown file.
#
# Reads a .lagda.md from STDIN; writes an .agda transcription to STDOUT.
# Selects the block by the first identifier on its first non-infix line,
# matched against the AGDA_BLOCKNAME environment variable.
#
# For all earlier Agda blocks: emits the code verbatim.
# For the selected block: wraps it in `-- EXERCISE STARTS` / `-- EXERCISE ENDS`
# markers, and applies rewrites:
#   * `{--}...{--}` -> `{!!}`         (inline holes)
#   * `-- Holify\n<name> ...` to end  -> `<name> = {!!}`
#   * trailing `-- Tests` block kept verbatim, with `-- EX: <expr>` lines
#     turned into a private module asserting `<expr>` by `refl`.

use warnings;
use strict;

while(1) {
  while(<STDIN>) {
    last if /^```/;
  }
  my $skip = ! (/^```(?:agda)?$/);

  my $code = "";
  my $id   = "";
  $_ = <STDIN>;
  die "(1) Premature end of file, aborting.\n" unless defined $_;
  until(/^```/) {
    $code .= $_;
    $_ = <STDIN>;
    die "(2) Premature end of file, aborting.\n" unless defined $_;
  }
  ($id) = $code =~ /^(?:infix[lr]?\s+\d+\s+\S+\n)*(\S*)\s/m;

  next if $skip;

  if($id ne $ENV{AGDA_BLOCKNAME}) {
    print $code;
    print "\n";
  } else {
    my $tests;
    if($code =~ s/^(-- Tests.*)$//ms) {
      $tests = $1;
      $tests =~ s/^--\s*EX:\s*(.*)$/module _ where private\n  open import Padova2025.ProvingBasics.Equality.Base\n  lets-play-agda-test : $1\n  lets-play-agda-test = refl\n/gm;
    }
    $code =~ s/\{--\}.*?\{--\}/{!!}/gs;
    $code =~ s#\n-- Holify\n([^ ]*).*$#\n$1 = {!!}\n#s;
    $code =~ s/\n+$/\n/;
    print "-- EXERCISE STARTS\n";
    print $code;
    print "-- EXERCISE ENDS\n";
    print "\n$tests" if $tests;
    last;
  }
}
