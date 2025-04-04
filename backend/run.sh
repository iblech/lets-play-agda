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
    cd /home/user
    AGDA_FILENAME="${AGDA_MODULENAME//\./\/}".lagda.md
    perl -i -pwe '\''
      BEGIN { $/ = undef }
      s/\{--\}.*?\{--\}/{!!}/gs;
      s#```agda/hole\n([^ ]*) (.*?)\1.*?```#```\n$1 $2$1 = {!!}\n```#gs;
    '\'' "$AGDA_FILENAME"
    perl -i -nwe '\''
      BEGIN { our $in_code = 0 }
      if($in_code) {
        if(/^```/) {
          $in_code = 0;
          print "--$_";
        } else {
          print;
        }
      } else {
        if(/^```/) {
          $in_code = 1;
        }
        print "--$_";
      }
    '\'' "$AGDA_FILENAME"
    AGDA_FIRSTLINE=$(< "$AGDA_FILENAME" sed -ne "/^$AGDA_BLOCKNAME/,/\`\`\`/ =" | head -1)
    AGDA_LASTLINE=$(< "$AGDA_FILENAME" sed -ne "/^$AGDA_BLOCKNAME/,/\`\`\`/ =" | tail -2 | head -1)
    mv "$AGDA_FILENAME" "${AGDA_MODULENAME//\./\/}".agda
    exec tmux \
      set -g status off \; \
      set-option -g default-terminal screen-256color \; \
      new-session -A -s fun \
      -- \
      emacs "${AGDA_MODULENAME//\./\/}".agda --eval "(narrow-to-line-range $AGDA_FIRSTLINE $AGDA_LASTLINE)"
  '
