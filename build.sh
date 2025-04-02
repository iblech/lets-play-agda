#!/usr/bin/env bash

set -ex

rm -rf out
mkdir out

cp --reflink=auto -t out -r Padova2025

cd out

find Padova2025 -name '*agda*' | grep -v "#" | xargs perl -i -pwe '
  BEGIN { $/ = undef }
  s/\{--\}.*?\{--\}/{!!}/gs;
  s#```agda/hole\n([^ ]*) (.*?)\1.*?```#```\n$1 $2$1 = {!!}\n```#gs;
'

agda --allow-unsolved-metas --html --html-highlight=code Padova2025/Index.lagda.md

rm -r Padova2025
mv html/* .
rmdir html

for i in *.html; do
  sed -i -e '1 s/^/<pre class="Agda">/' -e '$ s/$/<\/pre>/' "$i"
done

for i in *.md; do
  pandoc -o "${i%.md}.body.html" "$i"
  title="$(head -n1 "$i" | sed -e 's+^#\s*++')"
  echo "$title"

  title="$(head -n1 "$i" | sed -e 's+^#\s*++')" \
  bodyfile="${i%.md}.body.html" \
  < ../frontend/template.html \
  perl -pwe '
    sub slurp {
      local $/;
      open my $fh, "<", $_[0] or die $!;
      return scalar <$fh>;
    }

    s/__TITLE__/$ENV{title}/g;
    s/__BODY__/slurp($ENV{bodyfile})/eg;
  ' > "${i%.md}.html"
done

cp ../frontend/*.woff2 .
