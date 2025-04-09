{ config, pkgs, ... }:

let cache = builtins.fetchTarball {
  url = "https://www.speicherleck.de/iblech/stuff/lets-play-agda-cache.tgz";
  sha256 = "sha256:1jlv1a6dnl3kf41ws24ghn5gngfnh8i09aa1zk2dnbkf029gr98j";
}; in

{
  services.journald.extraConfig = ''
    Storage=volatile
    RuntimeMaxUse=20M
  '';

  time.hardwareClockInLocalTime = true;
  networking.firewall.enable = false;

  boot.enableContainers = true;
  boot.isContainer = true;
  documentation.doc.enable = false;

  users.users.user = {
    isNormalUser = true;
    description = "User";
    home = "/home/user";
  };

  systemd.services.lets-play-agda = {
    script = ''
      cd /home/user
      rm -rf lets-play-agda
      cp -r --reflink=auto ${./.} lets-play-agda
      chmod -R u+w lets-play-agda
      cp -r --reflink=auto ${cache} lets-play-agda/cache
      chmod -R u+w lets-play-agda/cache
      cd lets-play-agda

      ./frontend/build.sh
      ./backend/boot.sh
    '';
    path = with pkgs; [
      (emacs-nox.pkgs.withPackages (epkgs: [ epkgs.evil epkgs.tramp-theme epkgs.ahungry-theme epkgs.color-theme-sanityinc-tomorrow epkgs.use-proxy ]))
      (agda.withPackages (p: [ p.standard-library p.cubical p.agda-categories p._1lab p.generics p.functional-linear-algebra ]))
      bash
      bubblewrap
      curl
      gnugrep
      gnused
      gnutar
      gzip
      inotify-tools
      pandoc
      perl
      tmux
      ttyd
      util-linux
      zip
    ];
    wantedBy = [ "multi-user.target" ];
    serviceConfig.User = "user";
  };

  services.nginx = {
    enable = true;
    recommendedGzipSettings = true;
    recommendedOptimisation = true;
    user = "user";

    package = pkgs.nginxMainline.override {
      modules = with pkgs.nginxModules; [ brotli zstd ];
    };

    # important to prevent annoying reconnects
    appendHttpConfig = ''
      proxy_send_timeout 600;
      proxy_read_timeout 600;
      proxy_http_version 1.1;
    '';

    commonHttpConfig = ''
      brotli on;
      brotli_static on;
      brotli_types application/json application/javascript application/xml application/xml+rss image/svg+xml text/css text/javascript text/plain text/xml text/x-agda text/x-scheme text/markdown;
      zstd on;
      zstd_types application/json application/javascript application/xml application/xml+rss image/svg+xml text/css text/javascript text/plain text/xml text/x-agda text/x-scheme text/markdown;
      types {
        text/x-agda   agda lagda;
      }
      charset utf-8;
      charset_types text/x-agda text/markdown text/javascript;
    '';

    virtualHosts.localhost = {
      locations = {
        "/" = {
          root = "/home/user/lets-play-agda/out";
          extraConfig = ''
            expires 15m;
            if ($request_uri ~* "\.(woff2|css)$") {
              expires 365d;
            }
          '';
        };
        "/__tty" = {
          proxyPass = "http://localhost:7681";
          proxyWebsockets = true;
        };
      };
    };
  };
  systemd.services.nginx.serviceConfig.ProtectHome = "no";
}
