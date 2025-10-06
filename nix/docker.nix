{ pkgs ? import <nixpkgs> { }
, pkgsLinux ? import <nixpkgs> { system = "x86_64-linux"; }
, commit-id ? "main"
}:

let
  frontend = pkgs.callPackage ./frontend-package.nix { commit-id = commit-id; };
  backend  = pkgs.callPackage ./backend-package.nix  { commit-id = commit-id; };
in

pkgs.dockerTools.streamLayeredImage {
  name = "lets-play-agda";
  contents = with pkgs.dockerTools; [
    binSh
    usrBinEnv
    (fakeNss.override {
      extraGroupLines = [ "nogroup:x:65534:" ];
    })
  ];
  config = {
    Cmd = pkgs.lib.getExe (pkgs.writeShellApplication {
      name = "lets-play-agda-boot";
      runtimeInputs = with pkgsLinux; [ coreutils findutils (nginxMainline.override { modules = with nginxModules; [ brotli zstd ]; }) ttyd ];
      text = ''
        mkdir /tmp
        chown nobody /tmp

        rm -rf out
        cp -r ${frontend} out
        chmod -R u+w out
        find out -type f -exec touch {} +

        ttyd \
          -t disableReconnect=true \
          -t disableLeaveAlert=true \
          -t fontSize=20 \
          -t "theme={'background':'white'}" \
          -b /__ttyd \
          -W \
          -a \
          ${backend}/backend/run.sh ${backend} &
        nginx -p . -c ${../frontend/nginx.conf} &
        wait
      '';
    });
    ExposedPorts = { "8080/tcp" = {}; };
  };
}
