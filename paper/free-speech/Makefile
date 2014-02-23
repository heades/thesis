OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false

all : FS-design-inc.tex FS-analysis-inc.tex

free-speech-ott.tex : free-speech.ott
	$(OTT) $(OTT_FLAGS) -i free-speech.ott -o free-speech-ott.tex -tex_name_prefix FS

FS-design-inc.tex : FS-design.tex free-speech-ott.tex
	$(OTT) $(OTT_FLAGS) -i free-speech.ott -tex_name_prefix FS \
		-tex_filter FS-design.tex FS-design-inc.tex

FS-analysis-inc.tex : FS-analysis.tex free-speech-ott.tex
	$(OTT) $(OTT_FLAGS) -i free-speech.ott -tex_name_prefix FS \
			-tex_filter FS-analysis.tex FS-analysis-inc.tex

clean : 
	rm -f *.aux *.dvi *.ps *.pdf *.log *-ott.tex *-inc.tex
