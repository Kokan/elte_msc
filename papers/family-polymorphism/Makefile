

.PHONY: all clean

all: main.pdf slides.pdf

slides.pdf: slides.tex Makefile
	pdflatex --halt-on-error -shell-escape slides
	pdflatex --halt-on-error -shell-escape slides

main.pdf: main.tex ref.bib Makefile
	pdflatex --halt-on-error -shell-escape main
	biber main
	pdflatex --halt-on-error -shell-escape main
	pdflatex --halt-on-error -shell-escape main

view: main.pdf
	evince main.pdf

slideshow: slides.pdf
	evince slides.pdf

clean:
	rm -f main.aux
	rm -f main.bcf
	rm -f main.log
	rm -f main.pdf
	rm -f main.run.xml
	rm -f main.bbl
	rm -f main.blg
	rm -rf _minted-main/
	rm -rf _minted-slides/
	rm -f slides.nav
	rm -f slides.out
	rm -f slides.snm
	rm -f slides.toc
	rm -f slides.vrb

