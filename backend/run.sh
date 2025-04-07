#!/usr/bin/env bash

echo Spawning container...

# XXX: --new-session?
exec bwrap \
  --clearenv \
  --setenv PATH "$PATH" \
  --setenv LIBEXEC_PATH "$LIBEXEC_PATH" \
  --setenv TERMINFO_DIRS "$TERMINFO_DIRS" \
  --setenv TERM "$TERM" \
  --setenv LANG en_US.UTF-8 \
  --setenv LOCALE_ARCHIVE "$LOCALE_ARCHIVE" \
  --setenv HOME /home/user \
  --setenv AGDA_MODULENAME "$1" \
  --setenv AGDA_BLOCKNAME "$2" \
  --unshare-all \
  --tmpfs /run \
  --dev /dev \
  --proc /proc \
  --tmpfs /tmp \
  --dir /home/user \
  --ro-bind-try /bin /bin \
  --ro-bind-try /nix/store /nix/store \
  --ro-bind-try /run/current-system /run/current-system \
  --die-with-parent \
  --hostname box \
  --chdir / \
  --overlay-src Padova2025 \
  --tmp-overlay /home/user/Padova2025 \
  --ro-bind-try backend/site-start.el /home/user/.emacs \
  bash -c '
    set -e
    cd /home/user
    AGDA_INPUT_FILENAME="${AGDA_MODULENAME//\./\/}".lagda.md
    AGDA_OUTPUT_FILENAME="${AGDA_MODULENAME//\./\/}".agda
    perl -we '\''
      while(1) {
        my $holify;
        while(<STDIN>) {
          if(/^```agda\/hole/) {
            $holify++;
            last;
          } elsif(/^```/) {
            last;
          }
        }

        my $code = "";
        my $id   = "";
        $_ = <STDIN>;
        die "Premature end of file, aborting.\n" unless defined $_;
        /^([^ ]*)\s+(.*?)/ and $id = $1;
        until(/^```/) {
          $code .= $_;
          $_ = <STDIN>;
          die "Premature end of file, aborting.\n" unless defined $_;
        }

        if($id ne $ENV{AGDA_BLOCKNAME}) {
          print $code;
          print "\n";
        } else {
          my $tests;
          if($code =~ s/^(-- Tests.*)$//ms) {
            $tests = $1;
            $tests =~ s/^--\s*EX:\s*(.*)$/module _ where private\n  open import Padova2025.Equality.Definition\n  lets-play-agda-test : $1\n  lets-play-agda-test = refl\n/gm;
          }
          $code =~ s/\{--\}.*?\{--\}/{!!}/gs;
          $code =~ s#^([^ ]*)(\s+.*?\n)\1.*$#$1$2$1 = {!!}\n#s;
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
    (
      previous_hash=""
      inotifywait -m -e close_write -- "$(dirname "$AGDA_OUTPUT_FILENAME")" | while read; do
        if echo "$REPLY" | grep "\.agdai" >/dev/null; then
          current_hash="$(sha256sum -- "$AGDA_OUTPUT_FILENAME")"
          if [ "$previous_hash" != "$current_hash" ]; then
            previous_hash="$current_hash"
            date >> verification.log
            echo "$current_hash" >> verification.log
            if agda -- "$AGDA_OUTPUT_FILENAME" &>verification.log; then
              echo success >> verification.log
              echo -en "\033]0;SUCCESS $(< "$AGDA_OUTPUT_FILENAME" sed -ne "/-- EXERCISE STARTS/,/-- EXERCISE ENDS/ p" | sed '\''1d;$d'\'' | base64)\007"
              exit
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
