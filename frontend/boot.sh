#!/usr/bin/env bash

exec nginx -p . -c ./frontend/nginx.conf
