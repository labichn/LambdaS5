.PHONY = clean builddir debug

INCLUDES = analyses/aam,analyses/cfg,analyses/cps,analyses/sym,analyses/ses,js,exprjs,ljs,util,experimental,test

OCAMLBUILD = ocamlbuild -build-dir ../obj -libs unix,str,graph,oUnit -lflags -I,../lib -Is $(INCLUDES) -cflags -annot -cflags -I,../lib -Is $(INCLUDES)

EXE = jaam.d.byte

debug: builddir
	@rm -f $(EXE)
	$(OCAMLBUILD) $(EXE)
	@ln -s ../obj/$(EXE)

clean:
	rm -rf ../obj
	@rm -f $(EXE)

builddir:
	@mkdir ../obj 2> /dev/null || true

test: debug
	$(OCAMLBUILD) regexp_tests.d.byte
	$(OCAMLBUILD) gc_tests.d.byte

compare: debug
	$(OCAMLBUILD) sym_compare.d.byte
