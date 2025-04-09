#!/usr/bin/env perl

use List::Util qw< uniq >;
use Encode     qw< decode_utf8 encode_utf8 >;
use utf8;

binmode STDIN, ":utf8";
binmode STDOUT, ":utf8";
binmode STDERR, ":utf8";

our %seen;
our %commands;

open my $fh, "<", "cache/agda-input.el" or die $!;
while(<$fh>) {
  push @{$commands{decode_utf8($2)}}, $1 while /\("([^"]+)"\s+\.\s+\("([^"]+)"\)\)/g;
}

delete $commands{" "};  # NBSP
push @{$commands{"→"}}, "to";
push @{$commands{"π"}}, "pi";
push @{$commands{"₁"}}, "_1";
push @{$commands{"₂"}}, "_2";
push @{$commands{"¹"}}, "^1";
push @{$commands{"²"}}, "^2";
push @{$commands{"ℓ"}}, "ell";

$ignore{$_}++ for qw<
  í ó … ⋅ ♾ ⚙ ✅ ✨ ️🌊 🌳 🎨 🐑 💭 🕵 🗃 🚀 🛠 🤹 🧊 🧭 🧮 🧱 🧾 🌊
>;
$ignore{" "}++;
$ignore{"\x{200c}"}++;
$ignore{"\x{fe0f}"}++;

while(<>) {
  $seen{$_}++ for /([^[:ascii:]])/g;
}

my @pairs;

for my $char (sort keys %seen) {
  if(exists $commands{$char}) {
    push @pairs, "\"$char\": \"" . join(" or ", map { "\\\\$_" } sort @{$commands{$char}}) . "\"";
  } else {
    print STDERR "No input method found for: '$char'\n"
      unless $ignore{$char};
  }
}

print "const characterDescriptions = {";
print join ", ", @pairs;
print "};\n\n";
