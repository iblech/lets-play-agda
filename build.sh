#!/usr/bin/env bash

set -e

mkdir -p cache
if [ ! -e cache/juliamono.woff2 ]; then
  curl -L https://github.com/cormullion/juliamono/releases/download/v0.059/JuliaMono-webfonts.tar.gz | \
    tar -xvzO webfonts/JuliaMono-Regular.woff2 > \
    cache/juliamono.woff2
fi
if [ ! -e cache/inria-sans.woff2 ]; then
  curl https://aff.quasicoherent.io/inria-sans.woff2 > \
    cache/inria-sans.woff2
fi

sha256sum -c <<EOF
f47be20f9140e3e7f56fe1e552704084b713434377f6f2bad74d5d6ea358278e  cache/inria-sans.woff2
978ac8f14acd3559329ea14fa72d1eba924bdb4cad236ab434f7804c2def1bf5  cache/juliamono.woff2
EOF

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

(cd ..; ./frontend/generate-toc.pl Padova2025.Index) > toc.html

for i in *.md; do
  export bodyfile="${i%.md}.body.html"
  export title="$(head -n1 "$i" | sed -e 's+^#\s*++')"
  export modulename="${i%.md}"

  pandoc -o "$bodyfile" "$i"

  < ../frontend/template.html \
  perl -pwe '
    sub slurp {
      local $/;
      open my $fh, "<", $_[0] or die $!;
      return scalar <$fh>;
    }

    s/__TITLE__/$ENV{title}/g;
    s/__BODY__/slurp($ENV{bodyfile})/eg;
    s/__TOC__/slurp("toc.html")/eg;
    s/__MODULENAME__/$ENV{modulename}/g;
  ' > "${i%.md}.html"

  rm "$bodyfile"
done

cp ../cache/*.woff2 .

ln -s Padova2025.Welcome.html index.html

rm toc.html
