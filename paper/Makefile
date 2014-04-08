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

LD_FILES := norm-by-hs/lam-delta/lam-delta.tex \
	    norm-by-hs/lam-delta/Makefile \
	    norm-by-hs/lam-delta/lam_Delta.ott

SSF_FILES := norm-by-hs/ssf/ssf.tex \
	     norm-by-hs/ssf+/ssf+.tex \
	     norm-by-hs/dep-ssf/dep-ssf.tex \
	     norm-by-hs/ssf-omega/ssf-omega.tex

DTT_FILE := dil-dtt/L.ott \
	    dil-dtt/dtt.ott \
	    dil-dtt/design.tex \
	    dil-dtt/analysis.tex \
	    dil-dtt/Makefile

all : pdf

pdf : Makefile thesis.pdf

background.tex : $(BGRD_FILES)
	cd background; $(MAKE)

FS : $(FS_FILES)
	cd free-speech; $(MAKE)

SEP : $(SEP3_FILES)
	cd sep3; $(MAKE)

LDT : $(LD_FILES)
	cd norm-by-hs/lam-delta; $(MAKE)

DTT : $(DTT_FILES)
	cd dil-dtt; $(MAKE)

thesis.pdf : background.tex FS SEP LDT DTT thesis.tex thesis.bib $(SSF_FILES)
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
	cd norm-by-hs/lam-delta; $(MAKE) clean
	cd dil-dtt; $(MAKE) clean
