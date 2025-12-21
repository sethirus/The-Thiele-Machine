all: main.pdf

main.pdf: main.tex chapters/*.tex appendix/*.tex
	pdflatex main.tex
	bibtex main
	pdflatex main.tex
	pdflatex main.tex

clean:
	rm -f *.aux *.log *.out *.toc *.bbl *.blg *.pdf
