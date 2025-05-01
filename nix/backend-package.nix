{ lib, stdenv, agda, bash, bubblewrap, emacs-nox, inotify-tools, perl, tmux, makeWrapper, commit-id ? "main" }:

let
  ouragda = agda.withPackages (p: [ p.standard-library p.cubical p.agda-categories p._1lab p.generics p.functional-linear-algebra ]);
  ouremacs = emacs-nox.pkgs.withPackages (epkgs: [ epkgs.evil epkgs.tramp-theme epkgs.ahungry-theme epkgs.color-theme-sanityinc-tomorrow epkgs.use-proxy ]);
in

stdenv.mkDerivation rec {
  name = "lets-play-agda-backend";
  src = ./..;
  nativeBuildInputs = [ ouragda makeWrapper ];
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
      --prefix PATH : ${lib.makeBinPath [ bash bubblewrap inotify-tools ouragda ouremacs perl tmux ]}
  '';
  LC_ALL = lib.optionalString (!stdenv.hostPlatform.isDarwin) "C.UTF-8";
}
