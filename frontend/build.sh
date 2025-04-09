#!/usr/bin/env bash

set -e

mkdir -p cache

echo "* Obtaining external static resources..."

if [ ! -e cache/juliamono.woff2 ]; then
  curl -L https://github.com/cormullion/juliamono/releases/download/v0.059/JuliaMono-webfonts.tar.gz | \
    tar -xvzO webfonts/JuliaMono-Regular.woff2 > \
    cache/juliamono.woff2
fi

if [ ! -e cache/inria-sans.woff2 ]; then
  curl https://aff.quasicoherent.io/inria-sans.woff2 > \
    cache/inria-sans.woff2
fi

if [ ! -e cache/confetti.js ]; then
  curl https://gist.githubusercontent.com/elrumo/3055a9163fd2d0d19f323db744b0a094/raw/d9b09ae21d20adcf85f2ef59d110179a243996e9/confetti.js > \
    cache/confetti.js
fi

if [ ! -e cache/agda-input.el ]; then
  curl https://raw.githubusercontent.com/agda/agda/refs/heads/master/src/data/emacs-mode/agda-input.el > \
    cache/agda-input.el
fi

sha256sum -c <<EOF
f47be20f9140e3e7f56fe1e552704084b713434377f6f2bad74d5d6ea358278e  cache/inria-sans.woff2
978ac8f14acd3559329ea14fa72d1eba924bdb4cad236ab434f7804c2def1bf5  cache/juliamono.woff2
86856036d4e9f9c3b822961f26b972cd86560d07137d7f75abb32705aea49843  cache/confetti.js
f5dd77ce2d35ffe604286ca0dc2d89b65bf8425dcdbafb32aee2a461976b0b76  cache/agda-input.el
EOF

rm -rf out-wip
mkdir out-wip

cp --reflink=auto -t out-wip -r Padova2025

cd out-wip

echo
echo "* Checking solutions..."
# Keep us honest: check our proposed solutions
find Padova2025 -name '*agda*' | grep -v "#" | xargs perl -i -pwe '
  s/^--\s*EX:\s*(.*)$/module _ where private\n  open import Padova2025.Equality.Definition\n  lets-play-agda-test : $1\n  lets-play-agda-test = refl\n/g;
'
agda --safe Padova2025/Index.lagda.md

# Now generate HTML for the solutions
echo
echo "* Generating HTML for solutions..."
find Padova2025 -name '*agda*' | grep -v "#" | xargs perl -i -pwe '
  BEGIN { $/ = undef }
  s#^-- Tests.*?```#```#mgs;
'
agda --safe --html --html-highlight=code Padova2025/Index.lagda.md

mkdir solutions
for i in html/*.md; do
  < "$i" perl -nwe '
    BEGIN { $/ = undef }
    while($_ =~ m#<pre class="Agda"><a id="([^"]*)"></a>(.*?)</pre>#gs) {
      my ($id, $code) = ($1, $2);
      next unless $code =~ /-- Holify/ or $code =~ /\{--\}/;
      $code =~ s/\{--\}//g;
      $code =~ s/<a id="[^"]*"/<a/g;
      $code =~ s/<a class="Comment">-- Holify<\/a>\n//g;
      $code =~ s/<a (?:href="[^"]*" )?class="([^"]*)">/<span class="$1">/g;
      $code =~ s/<\/a>/<\/span>/g;
      $code =~ s/\n+$/\n/;
      print "<pre class=\"Agda reference-solution\" id=\"reference-solution-$id\">$code</pre>\n\n";
    }
  ' > "solutions/$(basename "$i")"
done
rm -rf html

# Now hide the solutions and generate HTML
echo
echo "* Generating HTML for exercises..."
find Padova2025 -name '*agda*' | grep -v "#" | xargs perl -i -pwe '
  BEGIN { $/ = undef }
  s/#[^\n]*\/\/\s*([^\n]*)/# $1/g;
  s/\{--\}.*?\{--\}/{!!}/gs;
  s#-- Holify\n([^ ]*).*?```#$1 = {!!}\n```#gs;
  s#^-- Tests.*?```#```#mgs;
'
agda --allow-unsolved-metas --html --html-highlight=code Padova2025/Index.lagda.md

mv html/* .
rmdir html

for i in *.html; do
  sed -i -e '1 s/^/<pre class="Agda">/' -e '$ s/$/<\/pre>/' "$i"
done

(cd ..; ./frontend/generate-toc.pl Padova2025.Index) > toc.html

echo
echo "* Assembling HTML files..."
for i in *.md; do
  echo "$i..."

  export bodyfile="${i%.md}.body.html"
  export title="$(< "$i" sed -ne '/^# / { s/^#\s*//; p; q; }')"
  export modulename="${i%.md}"
  export filename="${i%.md}.html"
  export basename="${i%.md}"
  export source="${basename//./\/}.lagda.md"

  pandoc -o "$bodyfile" "$i"
  sed -i -e '0,/<pre class="Agda">\(.*module.*where.*\)/ { s/<pre class="Agda">\(.*module.*where.*\)/<pre class="Agda inessential">\1/; }' "$bodyfile"
  perl -i -pe 'BEGIN { $/ = undef } s#\n\n</pre>#\n</pre>#g' "$bodyfile"

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
    s/__SOURCE__/$ENV{source}/g;
    s/__SOLUTIONS__/slurp("solutions\/$ENV{modulename}.md")/eg;
  ' > "$filename"

  rm "$bodyfile" "$i"
  cp --reflink=auto "$source" "$basename.lagda.md"
done

cp --reflink=auto ../cache/*.woff2  .
cp --reflink=auto ../cache/*.js     .

(cd ..; find Padova2025 -name "*.md" | xargs cat | ./frontend/generate-input-tips.pl) > ui.js
cat ../frontend/ui.js >> ui.js

ln -s Padova2025.Welcome.html index.html

rm -r toc.html Padova2025 solutions

cd ..
rm -rf out
mv out-wip out
