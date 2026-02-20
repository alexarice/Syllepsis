{ mkDerivation, multimarkdown, sass }:

mkDerivation {
  pname = "syllepsis";
  version = "master";

  src = ./.;

  LC_ALL = "en_GB.UTF-8";

  buildInputs = [ multimarkdown sass ];

  buildPhase = ''
    agda --html --html-highlight=auto *.md --css /css/Agda.css
    mmd html/*.md
    mv html/Syllepsis.html html/index.html
    sass css/*.scss --update
  '';

  installPhase = ''
    mkdir -p $out/css
    cp html/*.html $out
    cp css/*.css $out/css
  '';
}
