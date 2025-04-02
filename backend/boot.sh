#!/usr/bin/env bash

exec ttyd \
  -t disableReconnect=true \
  -t disableLeaveAlert=true \
  -t fontSize=20 \
  -t fontFamily="'JuliaMono', serif" \
  -t "theme={'background':'white'}" \
  -b /__ttyd \
  -W \
  -a \
  ./backend/run.sh
