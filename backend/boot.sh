#!/usr/bin/env bash

# -t fontFamily="'JuliaMono', serif" \
exec ttyd \
  -t disableReconnect=true \
  -t disableLeaveAlert=true \
  -t fontSize=20 \
  -t "theme={'background':'white'}" \
  -b /__ttyd \
  -W \
  -a \
  ./backend/run.sh
