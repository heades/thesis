# my distro does not have pdflatex at that path, so I pulled
# this out here to override. AS
PDFLATEX=pdflatex
OTTEX_HELPER=ottex_helper
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false -picky_multiple_parses false

all : sep3-inc.tex

sep3-inc.tex : sep3-annotated.ott sep3-unannotated.ott sep3.tex Makefile
	$(OTT) $(OTT_FLAGS) -i sep3-annotated.ott -o sep3-annotated-ott.tex -tex_name_prefix Sep \
	-tex_filter sep3.tex sep3-inc1.tex

	$(OTT) $(OTT_FLAGS) -i sep3-unannotated.ott -o sep3-unannotated-ott.tex \
	-tex_name_prefix SepU \
	-tex_filter sep3-inc1.tex sep3-inc.tex

clean : 
	rm -f *.aux *.dvi *.ps *.log sep3-inc.tex sep3-inc1.tex \
	sep3-unannotated-ott.tex sep3-annotated-ott.tex *~
