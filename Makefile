COQDOCFLAGS = --toc --toc-depth 2 --index indexpage --html \
  --interpolate --no-lib-name --parse-comments \
  --with-header resources/header.html --with-footer resources/footer.html

all: Makefile.coq
	+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq COQDOCFLAGS = "$(COQDOCFLAGS)"

html: Makefile.coq resources/index.html
	+$(MAKE) -f Makefile.coq html
	cp resources/*.js resources/*.css resources/index.html html

_CoqProject Makefile: ;

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

.PHONY: all clean html
