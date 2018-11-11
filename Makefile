all: tar

tar:
	tar -cvzf popl19_artifact.tgz --exclude ".git" --exclude ".gitattributes" --exclude Makefile --exclude ".docker" *
