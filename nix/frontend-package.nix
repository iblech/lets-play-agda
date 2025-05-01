{ lib, stdenv, agda, lychee, pandoc, perl, python3, zip, commit-id ? "main" }:

let
  ouragda = agda.withPackages (p: [ p.standard-library p.cubical p.agda-categories p._1lab p.generics p.functional-linear-algebra ]);

  cache = builtins.fetchTarball {
    url = "https://www.speicherleck.de/iblech/stuff/lets-play-agda-cache.tgz";
    sha256 = "sha256:06vwyggaq7lamw508yy9wyknq1g9psx9rr91jzxn39kqa87arpxr";
  };
in

stdenv.mkDerivation rec {
  name = "lets-play-agda-frontend"; 
  src = ./..;

  nativeBuildInputs = [ lychee ouragda pandoc perl (python3.withPackages (p: [ p.brotli p.fonttools ])) zip ];
  postPatch = ''
    patchShebangs .
  '';
  buildPhase = ''
    echo ${lib.escapeShellArg commit-id} > COMMIT_ID
    rm -rf cache
    cp -r --reflink=auto ${cache} cache
    chmod -R u+w cache
    ls -l
    ls -l cache
    pwd
    ./frontend/build.sh
  '';
  installPhase = ''
    mkdir -p $out
    cp -r --reflink=auto out/* $out/
  '';
  # See pkgs/build-support/agda/default.nix for explanation
  LC_ALL = lib.optionalString (!stdenv.hostPlatform.isDarwin) "C.UTF-8";
}
