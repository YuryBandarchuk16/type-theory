.PHONY: pack all run clean
GENERATED=src/parser.mli src/parser.ml src/lexer.ml
OCAMLC=ocamlopt # ocamlopt for speed
PACKAGE=hw2.zip

ifeq ($(OS),Windows_NT)
	DEL=del /f
else
	DEL=rm -f
endif

all: main.exe

run:
	./main.exe

src/tree.cmi:
	cd src && $(OCAMLC) -c tree.ml

main.exe: $(GENERATED) src/tree.cmi
	cd src && $(OCAMLC) str.cmxa -o ../main.exe tree.ml $(GENERATED:src/%=%) main.ml 

pack: $(GENERATED)
	zip $(PACKAGE) -r Makefile src

$(GENERATED): src/lexer.mll src/parser.mly
	ocamllex src/lexer.mll
	ocamlyacc src/parser.mly

clean:
	cd src && $(DEL) $(GENERATED:src/%=%) *.c* *.o*
	$(DEL) main.exe $(PACKAGE)
