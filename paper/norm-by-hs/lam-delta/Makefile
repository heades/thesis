OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta true -picky_multiple_parses false

FILES := lam_Delta.ott \
         lam-delta.tex \
         Makefile

all : lam-delta-inc.tex

lam-delta-inc.tex : $(FILES)
	$(OTT) $(OTT_FLAGS) -i lam_Delta.ott  -o lam-delta-ott.tex -tex_name_prefix LamDelta \
		-tex_filter lam-delta.tex lam-delta-inc.tex
clean : 
	rm -f *.bbl *.blg *.aux *.dvi *.ps *.log *-inc.tex *-ott.tex *~
