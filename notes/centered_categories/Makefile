PDFLATEX=pdflatex
BIBTEX=bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false -picky_multiple_parses false

all : pdf

pdf : note.pdf

note-output.tex : note.tex Makefile syntax.ott
	$(OTT) $(OTT_FLAGS) -i syntax.ott  -o syntax-inc.tex \
		-tex_filter note.tex note-output.tex

note.pdf : note-output.tex 
	$(PDFLATEX) -jobname note note-output.tex
	$(BIBTEX) note
	$(PDFLATEX) -jobname=note note-output.tex
	$(PDFLATEX) -jobname=note note-output.tex
	skim_revert.sh $(CURDIR)/note.pdf

quick : note-output.tex 
	$(PDFLATEX) -jobname note note-output.tex
	skim_revert.sh $(CURDIR)/note.pdf

clean :
	rm -f *.aux *.dvi *.ps *.log *-inc.tex note-output.tex *.bbl *.blg *~ *.rel *.out
