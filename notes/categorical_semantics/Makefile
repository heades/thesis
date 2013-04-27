OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false -picky_multiple_parses false

all : main.pdf

st-gen.tex : simple_types.tex simple_types.ott
	$(OTT) $(OTT_FLAGS) -i simple_types.ott  -o ST-ott.tex -tex_name_prefix ST \
		-tex_filter simple_types.tex st-gen.tex

main.pdf : main.tex st-gen.tex
	pdflatex main.tex
	pdflatex main.tex
	pdflatex main.tex
