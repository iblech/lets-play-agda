#!/usr/bin/env nix-shell
#! nix-shell -i bash -p ttyd bubblewrap "nginxMainline.override { modules = with pkgs.nginxModules; [ brotli zstd ]; }" inotify-tools lychee pandoc tmux zip "(agda.withPackages (p: [ p.standard-library p.cubical p.agda-categories p._1lab p.generics p.functional-linear-algebra ]))" "(emacs-nox.pkgs.withPackages (epkgs: [ epkgs.evil epkgs.tramp-theme epkgs.ahungry-theme epkgs.color-theme-sanityinc-tomorrow epkgs.use-proxy ]))" "python3.withPackages (pkgs: [ pkgs.brotli pkgs.fonttools ])"

./backend/boot.sh &
./frontend/boot.sh &

while :; do
  time ./frontend/build.sh "$1"
  echo -en "\007"

  inotifywait -e close_write -r --exclude "\..*\.sw[px]" Padova2025/ backend/ frontend/
  sleep 0.2  # wait for things to settle
done

wait
