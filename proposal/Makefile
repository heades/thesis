PDFLATEX=pdflatex
BIBTEX=bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false -picky_multiple_parses false

all : pdf

pdf : main.pdf companion.pdf

companion : companion.pdf

preordered-cats-output.tex : preordered-cats.tex syntax.ott
	$(OTT) $(OTT_FLAGS) -i syntax.ott -o syntax-inc.tex -tex_name_prefix SYN \
		-tex_filter preordered-cats.tex preordered-cats-output.tex

main.pdf : main-src.tex Makefile syntax.ott preordered-cats-output.tex 
	$(PDFLATEX) main.tex
	$(BIBTEX) main
	$(PDFLATEX) main.tex
	$(PDFLATEX) main.tex 

companion.pdf : main.tex main-src.tex companion.tex preordered-cats-output.tex syntax.ott
	$(PDFLATEX) companion.tex 
	$(BIBTEX) companion
	$(PDFLATEX) companion.tex 
	$(PDFLATEX) companion.tex 

harley : main.pdf
	skim_revert.sh $(CURDIR)/main.pdf

clean : 
	rm -f *.aux *.dvi *.ps *.log *-inc.tex *-output.tex *.bbl *.blg *~ *.out *.rel
