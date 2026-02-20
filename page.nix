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
    mv html/Syllepsis.html html/index.html
  '';

  installPhase = ''
    mkdir -p $out
    cp html/*.html $out
  '';
}
