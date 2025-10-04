#!/usr/bin/env bash

set -e

export quick="$1"
export commit_id="$(cat COMMIT_ID || echo main)"
export AGDA_DIR=$PWD/backend/config-agda

mkdir -p cache

echo "* Obtaining external static resources..."

if [ ! -e cache/juliamono.ttf ]; then
  curl -L https://github.com/cormullion/juliamono/releases/download/v0.059/JuliaMono-ttf.tar.gz | \
    tar -xvzO JuliaMono-Regular.ttf > \
    cache/juliamono.ttf
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
  curl https://raw.githubusercontent.com/agda/agda/refs/tags/v2.7.0.1/src/data/emacs-mode/agda-input.el > \
    cache/agda-input.el
fi

sha256sum -c <<EOF
f47be20f9140e3e7f56fe1e552704084b713434377f6f2bad74d5d6ea358278e  cache/inria-sans.woff2
3e521304357b22b90c02d003e8fa4fb7b49c1267e6459240fd06b2d1900e36c1  cache/juliamono.ttf
86856036d4e9f9c3b822961f26b972cd86560d07137d7f75abb32705aea49843  cache/confetti.js
da6646b2e4d2d932293a2e277ee38b14dcc08bd73fd5e12464c2221c64db23b9  cache/agda-input.el
EOF

rm -rf out-wip
mkdir out-wip

cp --reflink=auto -t out-wip -r Padova2025

cd out-wip

function generate_zip {
  # Fix timestamps so zip creation is deterministic
  find "$1" -print | xargs touch -d @0
  find "$1" -not -name "*.agdai" -not -name "*.swp" -not -name "*~" -not -name "*#*" | \
    LC_ALL=C sort | \
    TZ=UTC xargs zip --quiet -X -9 -
}

if [ -z "$quick" ]; then
  generate_zip Padova2025 > Padova2025-solutions.zip
fi

if find Padova2025 -name '*agda.md' | grep -v "#" | xargs grep -q $'\t'; then
  echo "Found tabs in source files, aborting."
  exit 1
fi

if [ -z "$quick" ]; then
  echo
  echo "* Checking solutions..."
  # Keep us honest: check our proposed solutions
  find Padova2025 -name '*agda*' | grep -v "#" | xargs perl -i -pwe '
    s/^--\s*EX:\s*(.*)$/module _ where private\n  open import Padova2025.ProvingBasics.Equality.Base\n  lets-play-agda-test : $1\n  lets-play-agda-test = refl\n/g;
  '
  agda --guardedness -WnoUnsupportedIndexedMatch Padova2025/Index.lagda.md
  # We allow people to play with unsafe features.
  # But we hold ourselves to the higher standard of --safe --cubical-compatible.
  # XXX: Make this comment true again.
fi

if [ -z "$quick" ]; then
  # Now generate HTML for the solutions
  echo
  echo "* Generating HTML for solutions..."
  find Padova2025 -name '*agda*' | grep -v "#" | xargs perl -i -pwe '
    BEGIN { $/ = undef }
    s#^-- Tests.*?```#```#mgs;
  '
  agda --guardedness -WnoUnsupportedIndexedMatch --html --html-highlight=code Padova2025/Index.lagda.md

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
fi

# Now hide the solutions and generate HTML
echo
echo "* Generating HTML for exercises..."
find Padova2025 -name '*agda*' | grep -v "#" | xargs perl -i -pwe '
  BEGIN { $/ = undef }
  s/^/```\n{-# OPTIONS --allow-unsolved-metas #-}\n```\n\n/;
  s/#[^\n]*\/\/\s*([^\n]*)/# $1/g;
  s/\{--\}.*?\{--\}/{!!}/gs;
  s#-- Holify\n([^ ]*).*?```#$1 = {!!}\n```#gs;
  s#^-- Tests.*?```#```#mgs;
'
agda --guardedness -WnoUnsupportedIndexedMatch --html --html-highlight=code Padova2025/Index.lagda.md
find Padova2025 -name "*.lagda.md" | xargs perl -i -pe '
  BEGIN { $/ = undef }
  s/```\n\{-# OPTIONS --allow-unsolved-metas #-\}\n```\n\n//;
'

if [ -z "$quick" ]; then
  generate_zip Padova2025 > Padova2025.zip
fi

mv html/* .
rmdir html

for i in *.html; do
  sed -i -e '1 s/^/<pre class="Agda">/' -e '$ s/$/<\/pre>/' "$i"
done

(cd ..; ./frontend/generate-toc.pl Padova2025.Index) > toc.html

echo
echo "* Assembling HTML files..."
for i in *.md; do
  (
    echo "$i..."

    export bodyfile="${i%.md}.body.html"
    export title="$(< "$i" sed -ne '/^# / { s/^#\s*//; p; q; }')"
    export modulename="${i%.md}"
    export filename="${i%.md}.html"
    export basename="${i%.md}"
    export source="${basename//./\/}.lagda.md"

    if [ "$modulename" = "Padova2025.Welcome" ]; then
      title="Welcome"
    fi

    {
      echo -n "recordTargets(\"$modulename\", \""
      < "$i" perl -nwe 'print $_, $/ for /id="([^"]+)"/' | egrep -v "^[0-9]*$" | sed -e 's+&lt;+<+g' -e 's+&gt;+>+g' -e 's+&#39;+'\''+g' -e 's+&amp;+\&+g' | LC_ALL=C sort | tr '\n' ' ' | sed -e 's+ $++'
      echo -n "\")"
    } > "$basename.targets"
    if grep ";" "$basename.targets" >/dev/null; then
      echo "Found lingering HTML entity in link targets of $modulename, aborting."
      cat "$basename.targets"
      exit 1
    fi
    echo ";" >> "$basename.targets"

    pandoc -o "$bodyfile" "$i"
    sed -i -e 's/<a id="[0-9]\+" class="Symbol">{-#.*/<span class="inessential">\0<\/span>/' "$bodyfile"
    perl -i -pe '
      BEGIN { $/ = undef }
      s#\n\n</pre>#\n</pre>#g;
      s#<pre.*?Keyword">OPTIONS.*?--allow-unsolved-metas.*?</span>\n</pre>##;
    ' "$bodyfile"

    < ../frontend/template.html \
    perl -pwe '
      sub slurp {
        local $/;
        open my $fh, "<", $_[0] or die $!;
        return scalar <$fh>;
      }

      sub toc {
        my $module = shift;

        my $toc = slurp("toc.html");
        $toc =~ s#(<input id="nav-([^"]*)")#
          my ($html, $id) = ($1,$2);
          if($module =~ /^\Q$id/) {
            "$html checked";
          } else {
            $html;
          }
        #eg;

        return $toc;
      }

      s/__TITLE__/$ENV{title}/g;
      s/__COMMIT_ID__/$ENV{commit_id}/g;
      s/__COMMIT_ID_SHORT__/substr $ENV{commit_id}, 0, 7/eg;
      s/__BODY__/slurp($ENV{bodyfile})/eg;
      s/__TOC__/toc($ENV{modulename})/eg;
      s/__AGDA_CSS__/slurp("Agda.css")/eg;
      s/__MODULENAME__/$ENV{modulename}/g;
      s/__SOURCE__/$ENV{source}/g;
      s/__SOLUTIONS__/slurp("solutions\/$ENV{modulename}.md")/eg
        unless $ENV{quick};
    ' > "$filename"

    rm "$bodyfile" "$i"
    cp --reflink=auto "$source" "$basename.lagda.md"
  ) &

  if [[ $(jobs -r -p | wc -l) -ge 4 ]]; then
    wait -n
  fi
done
wait

echo
echo "* Copying static files..."
cp --reflink=auto -r ../cache/*.woff2 ../frontend/static/* .
(cd ..; find Padova2025 -name "*.md" | xargs cat | ./frontend/generate-input-tips.pl) > ui.js
cat ../frontend/ui.js >> ui.js
cat *.targets >> ui.js
echo "attachEditors();" >> ui.js
cat ../cache/confetti.js >> ui.js
ln -s Padova2025.Welcome.html index.html
rm -rf toc.html Agda.css Padova2025 solutions *.targets

function do_sri {
  file="$1"
  hashsum="$(sha256sum "$1" | cut -d' ' -f1)"
  newname="${file%.*}-$hashsum.${file##*.}"
  mv "$file" "$newname"
  sed -i -e "s+$file+$newname+g" *.html *.js
  # we should escape the regex pattern, but for our purposes it will be good enough
}

if [ -z "$quick" ]; then
  echo
  echo "* Subsetting font..."
  find . -type f ! \( -name "*.zip" -o -name "*.woff2" \) -print0 | xargs -0 cat | pyftsubset ../cache/juliamono.ttf --text-file=/dev/stdin --output-file=juliamono.woff2 --flavor=woff2
  do_sri juliamono.woff2
fi

for i in ui.js; do
  do_sri $i
done

if [ -z "$quick" ]; then
  echo
  echo "* Checking for broken links..."
  lychee --offline --include-fragments --include-verbatim .
fi

cd ..
rm -rf out
mv out-wip out
