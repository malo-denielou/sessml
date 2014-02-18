###############################################################################
# SessML - Implementation                                                     #
#                                                                             #
# Makefile                                                                    #
###############################################################################
# $Id: Makefile 12483 2009-09-04 09:00:07Z fournet $

default: nc
nc: sessml 
bc: sessml-bc

all: clean default


FILES= common.ml mlsyntax.ml syntax.ml wf.ml graph.ml properties.ml dotgen.ml parser.ml lexer.ml geninterface.ml generation.ml main.ml 

NC1= common.cmx mlsyntax.cmx syntax.cmx graph.cmx properties.cmx dotgen.cmx 
NC2= parser.cmx lexer.cmx geninterface.cmx generation.cmx main.cmx 
BC= common.cmo mlsyntax.cmo syntax.cmo graph.cmo properties.cmo dotgen.cmo parser.cmo lexer.cmo geninterface.cmo generation.cmo main.cmo  

REQNC= parser.ml lexer.ml $(NC1) parser.cmi $(NC2)
REQBC= parser.ml lexer.ml $(BC)


lexer.ml: lexer.mll
	ocamllex lexer.mll

parser.ml parser.mli: common.cmo syntax.cmo parser.mly
	ocamlyacc -v parser.mly
	ocamlc -c parser.mli

# common.cmo: common.ml
# 	ocamlc -c common.ml

# syntax.cmo: common.cmo syntax.ml
# 	ocamlc -c syntax.ml

# %.cmi : %.mli
# 	ocamlc -c $<

%.cmo: %.ml $(FILES)
	ocamlc -c $<

%.cmx: %.ml $(FILES)
	ocamlopt -c $<

# .ml.cmx: $(FILES:.ml=.cmi)
# 	ocamlopt -c $<





###############
# Native-code #
###############
# common.cmx: common.ml
# 	ocamlopt -c common.ml

# mlsyntax.cmx: mlsyntax.ml
# 	ocamlopt -c mlsyntax.ml

# syntax.cmx: syntax.ml common.cmx
# 	ocamlopt -c syntax.ml

# graph.cmx: graph.ml common.cmx syntax.cmx
# 	ocamlopt -c graph.ml

# properties.cmx: properties.ml graph.cmx common.cmx syntax.cmx
# 	ocamlopt -c properties.ml

# dotgen.cmx: dotgen.ml graph.cmx common.cmx syntax.cmx
# 	ocamlopt -c dotgen.ml

# parser.cmx: parser.ml parser.mli common.cmx syntax.cmx
# 	ocamlopt -c parser.ml

# lexer.cmx: lexer.ml common.cmx syntax.cmx
# 	ocamlopt -c lexer.ml

# geninterface.cmx: geninterface.ml graph.cmx common.cmx syntax.cmx
# 	ocamlopt -c geninterface.ml

# generation.cmx: generation.ml geninterface.cmx graph.cmx common.cmx syntax.cmx
# 	ocamlopt -c generation.ml

# main.cmx: main.ml generation.cmx geninterface.cmx properties.cmo graph.cmx common.cmx syntax.cmx
# 	ocamlopt -c main.ml

sessml: $(FILES:.ml=.cmx) # $(REQNC)
	ocamlopt -o sessml $(FILES:.ml=.cmx) # $(NC1) $(NC2)

sessml-bc: $(FILES:.ml=.cmo)
	ocamlopt -o sessml $(FILES:.ml=.cmo)

# sessml-bc: $(REQBC)
# 	ocamlc -o sessml-bc $(BC)

# Windows
# : s2ml-bc
# 	cp s2ml-bc s2ml

clean:
	rm -f $(FILES:.ml=.o) 
	rm -f $(FILES:.ml=.cmx) 
	rm -f $(FILES:.ml=.cmo)
	rm -f $(FILES:.ml=.cmi)
# 	rm -f common.cmi common.cmo common.cmx common.o 
# 	rm -f mlsyntax.cmi mlsyntax.cmo mlsyntax.cmx mlsyntax.o 
# 	rm -f syntax.cmi syntax.cmo syntax.cmx syntax.o 
# 	rm -f graph.cmi graph.cmo graph.cmx graph.o 
# 	rm -f properties.cmi properties.cmo properties.cmx properties.o 
# 	rm -f dotgen.cmi dotgen.cmo dotgen.cmx dotgen.o 
# 	rm -f parser.cmi parser.cmo parser.cmx parser.o 
# 	rm -f lexer.cmi lexer.cmo lexer.cmx lexer.o 
# 	rm -f geninterface.cmi geninterface.cmo geninterface.cmx geninterface.o
# 	rm -f generation.cmi generation.cmo generation.cmx generation.o 
# 	rm -f main.cmi main.cmo main.cmx main.o
	rm -f parser.mli parser.ml parser.output
	rm -f lexer.ml
	rm -f sessml sessml-bc