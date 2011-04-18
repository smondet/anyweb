#!/bin/sh

ocamlc unix.cma anyweb.ml -o anyweb
anyweb camlbrtxhtml anyweb.ml | \
    brtx -doc -o index.html  -title "The anyweb Source" -link-css anyweb.css
anyweb camlbrtxhtml anyweb.ml | \
    brtx -doc -o anyweb_no_css.html  -title "The anyweb Source"
anyweb camlbrtxlatex anyweb.ml | \
    brtx -latex -doc -o anyweb.tex  -title "The anyweb Source"
pdflatex anyweb
anyweb coqbrtxhtml subset_notes.v | \
    brtx -o coq_example.html -doc -link-css anyweb.css 
anyweb coqbrtxlatex subset_notes.v | \
    brtx -latex -o coq_example.tex -doc -use-package coqdoc
pdflatex coq_example

mkdir -p website
mv *.html *.pdf  website/
cp anyweb.css website/
