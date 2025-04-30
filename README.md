# Let's play Agda

**[Live version](https://lets-play-agda.quasicoherent.io/)**

* License of the Agda files: CC BY-SA
* License of the frontend and backend code: AGPLv3+


## Self-hosting on NixOS

Add the following to your `/etc/nixos/configuration.nix`:

    containers.lets-play-agda = {
      config =
        let lets-play-agda = builtins.fetchTarball {
          url = "https://github.com/iblech/lets-play-agda/archive/main.tar.gz";
        }; in
        { config, pkgs, ... }:
        {
          imports = [ (import "${lets-play-agda}/container.nix" {}) ];
          system.stateVersion = "${config.system.nixos.release}";
        };
      ephemeral = true;
      autoStart = true;
      privateNetwork = true;
      hostAddress = "192.168.0.1";
      localAddress = "192.168.0.2";
    };
