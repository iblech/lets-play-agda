#!/usr/bin/env perl

use List::Util qw< uniq >;
use Encode     qw< decode_utf8 encode_utf8 >;
use utf8;

binmode STDIN,  ":utf8";
binmode STDOUT, ":utf8";
binmode STDERR, ":utf8";
binmode DATA,   ":utf8";

our %seen;
our %commands;

my $input_mode_file = `agda --emacs-mode locate`;
$input_mode_file =~ s/agda2\.el$/agda-input.el/;

open my $fh, "<", $input_mode_file or die $!;
while(<$fh>) {
  push @{$commands{decode_utf8($2)}}, $1 while /\("([^"]+)"\s+\.\s+\("([^"]+)"\)\)/g;
}
delete $commands{"ʳ"};  # The extracted key sequence "\^r" is not quite right/complete

while(<DATA>) {
  push @{$commands{$1}}, $2 while /^([^\s]*)\s(.*)$/g;
}

delete $commands{"\x{00a0}"};  # NBSP
$commands{"→"} = [qw[ -> r to ]];

$ignore{$_}++ for qw<
  ♾ ⚙ ✅ ✨ ️🌊 🌳 🎨 🐑 💭 🕵 🗃 🚀 🛠 🤹 🧊 🧭 🧮 🧱 🧾 🌊 👋 🚧 😱
  ―
>;
$ignore{" "}++;
$ignore{"\x{200c}"}++;  # Zero Width Non-Joiner
$ignore{"\x{fe0f}"}++;  # Variation Selector-16 (VS16)

while(<>) {
  $seen{$_}++ for /([^[:ascii:]])/g;
}

my @pairs;

for my $char (sort keys %seen) {
  if(exists $commands{$char}) {
    push @pairs, "\"$char\": \"" . join(" or ", map { "\Q\\$_" } sort @{$commands{$char}}) . "\"";
  } else {
    print STDERR "No input method found for: '$char'\n"
      unless $ignore{$char};
  }
}

print "const characterDescriptions = {";
print join ", ", @pairs;
print "};\n\n";

# Entries given in "LC_ALL=C sort" order
__DATA__
¬ neg
² ^2
³ ^3
· cdot
¹ ^1
× times
á 'a
é 'e
í 'i
ó 'o
ö "o
ć 'c
ʳ ^r4
˘ u{}
Σ Sigma
α alpha
β beta
γ gamma
ε varepsilon
ζ zeta
λ lambda
π pi
σ sigma
ω omega
… ldots
⁴ ^4
₀ _0
₁ _1
₂ _2
₃ _3
₄ _4
₅ _5
ℓ ell
→ to
↝ leadsto
↝ r~
∀ forall
∃ exists
∇ nabla
∈ in
∙ .
∶ :
⊝ o-
⊥ bot
⋰ rddots
⋱ ddots
│ ---
│ vbar
╱ ---
╲ ---
◂ t
⟨ <
⟩ >
