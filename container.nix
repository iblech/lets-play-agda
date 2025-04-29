{ commit-id ? "main" }:
{ config, pkgs, lib, ... }:

let
  cache = builtins.fetchTarball {
    url = "https://www.speicherleck.de/iblech/stuff/lets-play-agda-cache.tgz";
    sha256 = "sha256:06vwyggaq7lamw508yy9wyknq1g9psx9rr91jzxn39kqa87arpxr";
  };

  ouragda = pkgs.agda.withPackages (p: [ p.standard-library p.cubical p.agda-categories p._1lab p.generics p.functional-linear-algebra ]);
  ouremacs = pkgs.emacs-nox.pkgs.withPackages (epkgs: [ epkgs.evil epkgs.tramp-theme epkgs.ahungry-theme epkgs.color-theme-sanityinc-tomorrow epkgs.use-proxy ]);

  frontend-data = pkgs.stdenv.mkDerivation rec {
    name = "lets-play-agda-frontend-data";
    src = ./.;
    nativeBuildInputs = with pkgs; [ lychee ouragda pandoc perl (python3.withPackages (p: [ p.brotli p.fonttools ])) zip ];
    postPatch = ''
      patchShebangs .
    '';
    buildPhase = ''
      echo ${lib.escapeShellArg commit-id} > COMMIT_ID
      cp -r --reflink=auto ${cache} cache
      chmod -R u+w cache
      ./frontend/build.sh
    '';
    installPhase = ''
      mkdir -p $out
      cp -r --reflink=auto out/* $out/
    '';
    # See pkgs/build-support/agda/default.nix for explanation
    LC_ALL = lib.optionalString (!pkgs.stdenv.hostPlatform.isDarwin) "C.UTF-8";
  };

  backend-data = pkgs.stdenv.mkDerivation rec {
    name = "lets-play-agda-backend-data";
    src = ./.;
    nativeBuildInputs = [ ouragda pkgs.makeWrapper ];
    buildPhase = ''
      # no --safe or --cubical-compatible here, as we want people to be
      # able to play around with unsafe features
      echo ${lib.escapeShellArg commit-id} > COMMIT_ID
      agda Padova2025/Index.lagda.md
    '';
    patchPhase = ''
      patchShebangs .
    '';
    installPhase = ''
      mkdir -p $out
      cp -r --reflink=auto . $out/
      wrapProgram $out/backend/run.sh \
        --prefix PATH : ${lib.makeBinPath (with pkgs; [ bash bubblewrap inotify-tools ouragda ouremacs perl tmux ])}
    '';
    LC_ALL = lib.optionalString (!pkgs.stdenv.hostPlatform.isDarwin) "C.UTF-8";
  };
in

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

  services.ttyd = {
    enable = true;
    clientOptions = {
      disableReconnect = "true";
      disableLeaveAlert = "true";
      fontSize = "20";
      theme = "{'background':'white'}";
    };
    writeable = true;
    entrypoint = [ "-b" "/__ttyd" "-a" "${backend-data}/backend/run.sh" "${backend-data}" ];
    user = "user";
  };

  services.nginx = {
    enable = true;
    user = "user";

    recommendedGzipSettings = true;
    recommendedOptimisation = true;

    package = pkgs.nginxMainline.override { modules = with pkgs.nginxModules; [ brotli zstd ]; };

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
          root = "/home/user/www";
          extraConfig = ''
            expires 15m;
            if ($request_uri ~* "\.(woff2|css|svg)$") {
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

    # Bump the timestamps from the epoch used for /nix/store.
    # Ideally we would use the timestamp of the source.
    preStart = ''
      rm -rf /home/user/www
      cp -r ${frontend-data} /home/user/www
      chmod -R u+w /home/user/www
      find /home/user/www -type f -exec touch {} +
    '';
  };
  systemd.services.nginx.serviceConfig.ProtectHome = "no";
}
