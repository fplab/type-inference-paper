MAIN=type-inference-paper

all:
	pdflatex $(MAIN)

bib:
	pdflatex $(MAIN)
	bibtex $(MAIN)
	pdflatex $(MAIN)
	bibtex $(MAIN)
	pdflatex $(MAIN)

clean: 
	rm -f *.aux *.log *.out *.cmo *.cmi *.o lexer.ml parser.ml parser.mli $(MAIN).bbl main.blg main.pdf

debug_test:
	ocamllex lexer.mll
	menhir parser.mly
	ocamlc -g syntax.ml parser.mli lexer.ml parser.ml myparse.ml impl.ml sort.ml util.ml test.ml
