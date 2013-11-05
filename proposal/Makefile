PDFLATEX=pdflatex
BIBTEX=bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false -picky_multiple_parses false

all : pdf

pdf : main.pdf 

main.pdf : main-src.tex Makefile 
	$(PDFLATEX) main.tex
	$(BIBTEX) main
	$(PDFLATEX) main.tex
	$(PDFLATEX) main.tex 

harley : main.pdf
	skim_revert.sh $(CURDIR)/main.pdf

clean : 
	rm -f *.aux *.dvi *.ps *.log *-inc.tex *-output.tex *.bbl *.blg *~ *.out *.rel
