OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false -picky_multiple_parses false

all : main.pdf

st-gen.tex : simple_types.tex simple_types.ott
	$(OTT) $(OTT_FLAGS) -i simple_types.ott  -o ST-ott.tex -tex_name_prefix ST \
		-tex_filter simple_types.tex st-gen.tex

category_theory-gen.tex : category_theory.tex category_theory.ott
	$(OTT) $(OTT_FLAGS) -i category_theory.ott  -o CT-ott.tex -tex_name_prefix CT \
		-tex_filter category_theory.tex category_theory-gen.tex

main.pdf : main.tex st-gen.tex category_theory-gen.tex coalgebras_analysis.tex real_nums.tex
	pdflatex main.tex
	pdflatex main.tex
	pdflatex main.tex
	./skim_revert.sh main.pdf

clean : 
	rm *.pdf *.aux *.log *.out *.toc *.lof *.rel 
