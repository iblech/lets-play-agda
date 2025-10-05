#!/usr/bin/env bash

# Parameters:
# $1 path to source files (containing Padova2025, backend etc.)
# $2 Agda module name
# $3 block id in the Agda file

echo Spawning container...

# XXX: --new-session?

# We try to do without /proc so that remounting /proc in the parent container
# is not required. Let's see whether everything will still work.
exec bwrap \
  --clearenv \
  --setenv PATH "$PATH" \
  --setenv LIBEXEC_PATH "$LIBEXEC_PATH" \
  --setenv TERMINFO_DIRS "$TERMINFO_DIRS" \
  --setenv TERM "$TERM" \
  --setenv LANG en_US.UTF-8 \
  --setenv LOCALE_ARCHIVE "$LOCALE_ARCHIVE" \
  --setenv HOME /home/user \
  --setenv AGDA_MODULENAME "$2" \
  --setenv AGDA_BLOCKNAME "$3" \
  --unshare-all \
  --tmpfs /run \
  --dev /dev \
  --tmpfs /tmp \
  --dir /home/user \
  --ro-bind-try /bin /bin \
  --ro-bind-try /nix/store /nix/store \
  --ro-bind-try /run/current-system /run/current-system \
  --die-with-parent \
  --hostname box \
  --chdir / \
  --ro-bind "$1"/Padova2025 /home/user/Padova2025.orig \
  --ro-bind "$1"/_build /home/user/_build.orig \
  --ro-bind "$1"/padova2025.agda-lib /home/user/padova2025.agda-lib \
  --ro-bind "$1"/backend/site-start.el /home/user/.emacs \
  --ro-bind "$1"/backend/config-agda /home/user/.config/agda \
  --ro-bind "$1"/backend/hello.txt /home/user/.hello.txt \
  bash -c '
    set -e
    cd /home/user
    AGDA_INPUT_FILENAME="${AGDA_MODULENAME//\./\/}".lagda.md
    AGDA_OUTPUT_FILENAME="${AGDA_MODULENAME//\./\/}".agda

    # the files in the "orig" directory are not writeable
    cp -r Padova2025.orig Padova2025
    cp -r _build.orig _build
    chmod -R u+w Padova2025 _build

    perl -we '\''
      while(1) {
        while(<STDIN>) {
          last if /^```/;
        }
        my $skip = ! (/^```(?:agda)?$/);

        my $code = "";
        my $id   = "";
        $_ = <STDIN>;
        die "(1) Premature end of file, aborting.\n" unless defined $_;
        /^([^ ]*)\s+(.*?)/ and $id = $1;
        until(/^```/) {
          $code .= $_;
          $_ = <STDIN>;
          die "(2) Premature end of file, aborting.\n" unless defined $_;
        }

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
    '\'' < "$AGDA_INPUT_FILENAME" > "$AGDA_OUTPUT_FILENAME"
    rm "$AGDA_INPUT_FILENAME"

    AGDA_FIRSTLINE=$(< "$AGDA_OUTPUT_FILENAME" sed -ne "/^-- EXERCISE STARTS/ { =; q }")
    AGDA_LASTLINE=$(< "$AGDA_OUTPUT_FILENAME" sed -ne "/^-- EXERCISE ENDS/ { =; q }")
    : $((AGDA_FIRSTLINE++))
    : $((AGDA_LASTLINE--))

    # in the likely case that an agdai file (containing the solutions) already exists, remove it
    rm -f "$AGDA_OUTPUT_FILENAME"i 2>/dev/null

    (
      previous_hash=""
      inotifywait -m -e close_write -- _build/*/agda/"$(dirname "$AGDA_OUTPUT_FILENAME")" | while read; do
        if echo "$REPLY" | grep "\.agdai" >/dev/null; then
          current_hash="$(sha256sum -- "$AGDA_OUTPUT_FILENAME")"
          if [ "$previous_hash" != "$current_hash" ]; then
            previous_hash="$current_hash"
            date >> verification.log
            echo "$current_hash" >> verification.log
            if agda -- "$AGDA_OUTPUT_FILENAME" &>verification.log; then
              echo success >> verification.log
              echo -en "\033]0;SUCCESS $(< "$AGDA_OUTPUT_FILENAME" sed -ne "/-- EXERCISE STARTS/,/-- EXERCISE ENDS/ p" | sed '\''1d;$d'\'' | base64)\007"
              # no need to exit, allow user to refine their solution
            else
              echo failure >> verification.log
            fi
          fi
        fi
      done
    ) &

    tmux \
      set -g status off \; \
      set-option -g default-terminal screen-256color \; \
      new-session -A -s fun \
      -- \
      emacs "$AGDA_OUTPUT_FILENAME" --eval "(narrow-to-line-range $AGDA_FIRSTLINE $AGDA_LASTLINE)"

    kill %1
  '
