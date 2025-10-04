#!/usr/bin/env bash

set -e

# precompile the Agda sources for faster C-c C-l in the containers
agda --guardedness -WnoUnsupportedIndexedMatch Padova2025/Index.lagda.md

# -t fontFamily="'JuliaMono', serif" \
exec ttyd \
  -t disableReconnect=true \
  -t disableLeaveAlert=true \
  -t fontSize=20 \
  -t "theme={'background':'white'}" \
  -b /__ttyd \
  -W \
  -a \
  ./backend/run.sh .
