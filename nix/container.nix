{ commit-id ? "main" }:
{ config, pkgs, lib, ... }:

let
  frontend = pkgs.callPackage ./frontend-package.nix { commit-id = commit-id; };
  backend  = pkgs.callPackage ./backend-package.nix  { commit-id = commit-id; };
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
    entrypoint = [ "-b" "/__ttyd" "-a" "${backend}/backend/run.sh" "${backend}" ];
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
            if ($request_uri ~* "\.(woff2|css|svg|js)$") {
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
      cp -r ${frontend} /home/user/www
      chmod -R u+w /home/user/www
      find /home/user/www -type f -exec touch {} +
    '';
  };
  systemd.services.nginx.serviceConfig.ProtectHome = "no";
}
