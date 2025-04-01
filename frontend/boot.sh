#!/usr/bin/env bash

set -e
cd "$(dirname "$0")"

trap "trap - SIGTERM && kill -- -$$" SIGINT SIGTERM EXIT

ttyd -t disableReconnect=true -t disableLeaveAlert=true -t fontFamily="'Julia Mono', serif" -t "theme={'background':'white'}" \
   -b /__ttyd -W -a $(which bash) &
nginx -c $PWD/nginx.conf
