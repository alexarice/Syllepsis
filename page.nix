{ mkDerivation, multimarkdown }:

mkDerivation {
  pname = "syllepsis";
  version = "master";

  src = ./.;

  LC_ALL = "en_GB.UTF-8";

  buildInputs = [ multimarkdown ];

  buildPhase = ''
    agda --html --html-highlight=auto *.md --css /css/Agda.css
    mmd html/*.md
  '';

  installPhase = ''
    mkdir -p $out/css
    cp html/*.html $out
    cp css/Agda.css $out/css
  '';
}
