OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false -picky_multiple_parses false

all : design-inc.tex analysis-inc.tex

design-inc.tex : L.ott dtt.ott design.tex
	$(OTT) $(OTT_FLAGS) -i dtt.ott  -o dtt-ott.tex -tex_name_prefix dtt \
		-tex_filter design.tex design-incI.tex	
	scripts/prepr_double_ott.sh design-incI.tex 
	$(OTT) $(OTT_FLAGS) -i L.ott  -o L-ott.tex -tex_name_prefix L \
		-tex_filter design-incI.tex design-inc.tex

analysis-inc.tex : L.ott dtt.ott analysis.tex
	$(OTT) $(OTT_FLAGS) -i dtt.ott -o dtt-ott.tex -tex_name_prefix dtt \
		-tex_filter analysis.tex analysis-incI.tex	
	scripts/prepr_double_ott.sh analysis-incI.tex 
	$(OTT) $(OTT_FLAGS) -i L.ott  -o L-ott.tex -tex_name_prefix L \
		-tex_filter analysis-incI.tex analysis-inc.tex

clean : 	
	rm -f *.aux *.dvi *.ps *.log *-inc.tex *-ott.tex *.bbl *.blg *~ *.out *.rel *.backup *-incI.tex
