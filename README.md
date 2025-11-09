# Let's play Agda

**[Live version](https://lets-play-agda.quasicoherent.io/)**

* License of the Agda files: CC BY-SA
* License of the frontend and backend code: AGPLv3+


## Self-hosting via Docker

For the time being no pre-made Docker image is published in a registry, but you
can create and load one as follows. The process might take a while but is fully
automated and reproducible, and has Docker as its only dependency.

    # Build and load Docker image, the name will be something like
    # lets-play-agda:ci07i8sf4vwa2lkyp9w699ldamj8mgd4.
    docker run --rm nixos/nix bash -c "
        git clone https://github.com/iblech/lets-play-agda
        cd lets-play-agda
        bash <(nix-build --no-out-link nix/docker.nix)
    " | docker load

    # Run image in ephemeral container, make sure to use the correct tag;
    # unfortunately, currently the privileged mode is necessary so that
    # sub-container creation works inside the Docker container.
    docker run --privileged --rm -p 8080:8080 lets-play-agda:ci07i8sf4vwa2lkyp9w699ldamj8mgd4

If you prefer a version-pinned build, you can use:

    docker run --rm nixos/nix bash -c "
        git clone --revision=97e4198a0d205a0fafb1e5cbc30883e371c800be https://github.com/iblech/lets-play-agda
        cd lets-play-agda
        bash <(nix-build -I nixpkgs=https://github.com/NixOS/nixpkgs/archive/6faeb062ee4cf4f105989d490831713cc5a43ee1.tar.gz --no-out-link nix/docker.nix)
    " | docker load

This will result in the Docker image
lets-play-agda:amg72qk0401ggi2amqcgd3afi07g0ibp, using the (at the time of
writing) latest release of NixOS 25.05.


## Self-hosting on NixOS

Add the following to your `/etc/nixos/configuration.nix`:

    containers.lets-play-agda = {
      config =
        let lets-play-agda = builtins.fetchTarball {
          url = "https://github.com/iblech/lets-play-agda/archive/main.tar.gz";
        }; in
        { config, pkgs, ... }:
        {
          imports = [ (import "${lets-play-agda}/nix/container.nix" {}) ];
          system.stateVersion = "${config.system.nixos.release}";
        };
      ephemeral = true;
      autoStart = true;
      privateNetwork = true;
      hostAddress = "192.168.0.1";
      localAddress = "192.168.0.2";
    };
