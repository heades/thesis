PDFLATEX=pdflatex
BIBTEX=bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false -picky_multiple_parses false

all : pdf

pdf : paper.pdf

# The section on modern church STLC.
churchSTLC-inc.tex : Makefile churchSTLC.ott churchSTLC.tex
	$(OTT) $(OTT_FLAGS) -i churchSTLC.ott  -o CHSTLC-ott.tex -tex_name_prefix CHSTLC \
		-tex_filter churchSTLC.tex churchSTLC-inc.tex

# The section on modern curry STLC.
currySTLC-inc.tex : Makefile currySTLC.ott currySTLC.tex
	$(OTT) $(OTT_FLAGS) -i currySTLC.ott  -o CSTLC-ott.tex -tex_name_prefix CSTLC \
		-tex_filter currySTLC.tex currySTLC-inc.tex

# The section on combinatory logic.
combinatory_logic-inc.tex : Makefile combinatory_logic.ott combinatory_logic.tex 
	$(OTT) $(OTT_FLAGS) -i combinatory_logic.ott  -o combinatory_logic-ott.tex -tex_name_prefix Comb \
		-tex_filter combinatory_logic.tex combinatory_logic-inc.tex

# The section on system T.
systemT-inc.tex : Makefile systemT.ott systemT.tex 
	$(OTT) $(OTT_FLAGS) -i systemT.ott  -o T-ott.tex -tex_name_prefix T \
		-tex_filter systemT.tex systemT-inc.tex

# The section on system F.
systemF-inc.tex : Makefile systemF.ott systemF.tex
	$(OTT) $(OTT_FLAGS) -i systemF.ott  -o F-ott.tex -tex_name_prefix F \
		-tex_filter systemF.tex systemF-inc.tex

# The section on system F.
SSF-inc.tex : Makefile SSF.ott SSF.tex
	$(OTT) $(OTT_FLAGS) -i SSF.ott  -o SSF-ott.tex -tex_name_prefix SSF \
		-tex_filter SSF.tex SSF-inc.tex

# The section on system F-Omega.
systemFomega-inc.tex : Makefile systemFomega.ott systemFomega.tex
	$(OTT) $(OTT_FLAGS) -i systemFomega.ott  -o Fw-ott.tex -tex_name_prefix Fw \
		-tex_filter systemFomega.tex systemFomega-inc.tex

# The history section.
history-inc.tex : Makefile history.tex lam.ott churchSTLC-inc.tex currySTLC-inc.tex combinatory_logic-inc.tex systemT-inc.tex systemF-inc.tex SSF-inc.tex systemFomega-inc.tex 
	$(OTT) $(OTT_FLAGS) -i lam.ott  -o lam-ott.tex -tex_name_prefix Lam \
		-tex_filter history.tex history-inc.tex

# The category theory section.
category_theory-inc.tex : Makefile category_theory.tex churchSTLC.ott
	$(OTT) $(OTT_FLAGS) -i churchSTLC.ott -tex_name_prefix CHSTLC -tex_filter category_theory.tex category_theory-inc.tex

# The section on the lambda-mu-calculus.
lamu-inc.tex : Makefile lamu.tex lamu.ott
	$(OTT) $(OTT_FLAGS) -i lamu.ott -o lamu-ott.tex -tex_name_prefix Lamu \
		-tex_filter lamu.tex lamu-inc.tex

# The section on the lambda-delta-calculus.
lamd-inc.tex : Makefile lamd.tex lamd.ott
	$(OTT) $(OTT_FLAGS) -i lamd.ott -o lamd-ott.tex -tex_name_prefix Lamd \
		-tex_filter lamd.tex lamd-inc.tex

# The section on the lambda-bar-mu-mu-tilde-calculus.
lam-bar-mu-mu-tilde-inc.tex : Makefile lam-bar-mu-mu-tilde.tex lam-bar-mu-mu-tilde.ott
	$(OTT) $(OTT_FLAGS) -i lam-bar-mu-mu-tilde.ott -o lam-bar-mu-mu-tilde-ott.tex -tex_name_prefix LBMMT \
		-tex_filter lam-bar-mu-mu-tilde.tex lam-bar-mu-mu-tilde-inc.tex

# The section on the dual-calculus.
dual-calculus-inc.tex : Makefile dual-calculus.tex dual-calculus.ott
	$(OTT) $(OTT_FLAGS) -i dual-calculus.ott -o dual-calculus-ott.tex -tex_name_prefix DC \
		-tex_filter dual-calculus.tex dual-calculus-inc.tex

# The section on Martin-Lof's type theory.
type-theory-inc.tex : type-theory.tex type_theory.ott
	$(OTT) $(OTT_FLAGS) -i type_theory.ott -o type-theory-ott.tex -tex_name_prefix TT \
		-tex_filter type-theory.tex type-theory-inc.tex

# The section on calculus of constructions.
CoC-inc.tex : CoC.tex CoC.ott
	$(OTT) $(OTT_FLAGS) -i CoC.ott -o CoC-ott.tex -tex_name_prefix CoC \
		-tex_filter CoC.tex CoC-inc.tex

# The section on the separated calculus of constructions.
CoC_sep-inc.tex : CoC_sep.tex CoC_sep.ott
	$(OTT) $(OTT_FLAGS) -i CoC_sep.ott -o CoC_sep-ott.tex -tex_name_prefix CoCS \
		-tex_filter CoC_sep.tex CoC_sep-inc.tex

# The section on SN of church STLC.
sn_stlc-inc.tex : Makefile churchSTLC.ott sn_stlc.tex
	$(OTT) $(OTT_FLAGS) -i churchSTLC.ott -o CHSTLC-ott.tex -tex_name_prefix CHSTLC \
	-tex_filter sn_stlc.tex sn_stlc-inc.tex

# The section on SN of system F.
sn_F-inc.tex : Makefile systemF.ott sn_F.tex
	$(OTT) $(OTT_FLAGS) -i systemF.ott -o F-ott.tex -tex_name_prefix F \
	-tex_filter sn_F.tex sn_F-inc.tex

# The main paper.
paper.pdf : history-inc.tex category_theory-inc.tex lamu-inc.tex lamd-inc.tex \
	    lam-bar-mu-mu-tilde-inc.tex dual-calculus-inc.tex type-theory-inc.tex \
	    CoC-inc.tex CoC_sep-inc.tex sn_stlc-inc.tex sn_F-inc.tex step_index_lr.tex \
	    Makefile paper.tex references.bib
	$(PDFLATEX) paper.tex
	$(BIBTEX)   paper
	$(PDFLATEX) paper.tex
	$(PDFLATEX) paper.tex
	$(PDFLATEX) paper.tex

clean : 
	rm -f *.aux *.log *.blg *.bbl *.dvi *.ps *.log *-inc.tex *-output.tex *~ *.msg *.out *.vtc *-ott.tex *-inc.tex
