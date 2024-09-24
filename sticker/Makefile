.SUFFIXES: .tex .v .pdf
.v.tex:
	coqdoc -latex -utf8 --bodyonly $<
.tex.pdf:
	latexmk -pdfdvi $<

sources = AutomatonEx.v AutomatonModule.v myLemma.v StickerModule.v ../REG_RSL.v
intermediates = AutomatonEx.tex AutomatonModule.tex myLemma.tex StickerModule.tex REG_RSL.tex

all: $(intermediates) CoqSticker.tex
	coqdoc -latex -utf8 --bodyonly $<
	latexmk -pdfdvi CoqSticker.tex
open:
	open CoqSticker.pdf
clean:
	-rm *.fls *.dvi *.log *.aux *.toc *~ *.fdb_latexmk \
		*.glob *.v.d *.out *.ps *.sol
	-rm $(intermediates)
cleanall:
	make clean
	-rm CoqSticker.pdf coqdoc.sty


