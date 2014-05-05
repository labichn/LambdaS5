NAME=paper

default:
	xelatex $(NAME)
	bibtex $(NAME)
	xelatex $(NAME)
	xelatex $(NAME)

clean:
	rm -f $(NAME).{dvi,ps,pdf,log,toc,blg,bbl,aux,rel} *.log *~
