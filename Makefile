all: tar

tar:
	tar -cvzf supplementary.tgz --exclude ".git" --exclude ".gitattributes" --exclude Makefile --exclude ".docker" *
