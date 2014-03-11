PDFLATEX = pdflatex
BIBTEX = bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false -picky_multiple_parses false
SKIM = skim_revert.sh

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
		background/type-theory.tex \
	        background/Makefile

FS_FILES := free-speech/FS-analysis.tex \
	    free-speech/FS-design.tex \
	    free-speech/Makefile \
	    free-speech/free-speech.ott

SEP3_FILES := sep3/Makefile \
	      sep3/sep3-annotated.ott \
	      sep3/sep3-unannotated.ott \
              sep3/sep3.tex

all : pdf

pdf : Makefile thesis.pdf

background.tex : $(BGRD_FILES)
	cd background; $(MAKE)

FS : $(FS_FILES)
	cd free-speech; $(MAKE)

SEP : $(SEP3_FILES)
	cd sep3; $(MAKE)

thesis.pdf : background.tex FS SEP thesis.tex thesis.bib
ifndef QUICKPROC
	$(PDFLATEX) thesis.tex
	$(PDFLATEX) thesis.tex
	$(BIBTEX) thesis
	$(PDFLATEX) thesis.tex
endif
	$(PDFLATEX) thesis.tex
ifeq ($(SKIM), skim_revert.sh)
	$(SKIM) $(CURDIR)/thesis.pdf
endif

root : all

clean : 
	rm -f *.bbl *.blg *.aux *.dvi *.ps *.log *-output.tex *~

clean-stuck : 
	rm -f *.aux

clean-all : clean
	cd background; $(MAKE) clean
	cd free-speech; $(MAKE) clean
	cd sep3; $(MAKE) clean
