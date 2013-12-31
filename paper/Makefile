PDFLATEX=pdflatex

OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta true -picky_multiple_parses false

BGRD_FILES :=   background/CoC.tex \
		background/CoC_sep.tex \
		background/SSF.tex \
		background/background.tex \
		background/category_theory.tex \
		background/churchSTLC.tex \
		background/combinatory_logic.tex \
		background/currySTLC.tex \
		background/dual-calculus.tex \
		background/history.tex \
		background/lam-bar-mu-mu-tilde.tex \
		background/lamd.tex \
		background/lamu.tex \
		background/sn_F.tex \
		background/sn_stlc.tex \
		background/step_index_lr.tex \
		background/systemF.tex \
		background/systemFomega.tex \
		background/systemT.tex \
		background/type-theory.tex

all : pdf

pdf : Makefile thesis.pdf

background.tex : $(BGRD_FILES)
	cd background; $(MAKE)

thesis.pdf : thesis.tex thesis.bib background.tex
	$(PDFLATEX) thesis.tex
	$(PDFLATEX) thesis.tex
	bibtex thesis
	skim_revert.sh $(CURDIR)/thesis.pdf

root : all

clean : 
	rm -f *.bbl *.blg *.aux *.dvi *.ps *.log *-output.tex *~
	cd background; $(MAKE) clean
