

.PHONY: all clean

all: main.pdf

main.pdf: main.tex
	pdflatex --halt-on-error main
	biber main
	pdflatex --halt-on-error main
	pdflatex --halt-on-error main

clean:
	rm -f main.aux
	rm -f main.bcf
	rm -f main.log
	rm -f main.pdf
	rm -f main.run.xml
	rm -f main.bbl
	rm -f main.blg
