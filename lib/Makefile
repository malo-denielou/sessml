
FLAGS = -thread

interfaces= global.cmi data.cmi crypto.cmi prins.cmi pi.cmi
nc= global.cmx data.cmx crypto.cmx prins.cmx  pi.cmx openssl_impl.o
bc= global.cmo data.cmo crypto.cmo prins.cmo pi.cmo openssl_impl.o

all: runtime.cmo runtime.cmx


%.cmi: %.mli
	ocamlc $<

%.cmo: %.ml
	ocamlc -c $(FLAGS) $<

%.cmx: %.ml
	ocamlopt -c $(FLAGS) $<

#	ocamlopt -c -cc "cc" -ccopt "-o openssl_impl.o " openssl_impl.c

#s.cmxa: $(interfaces) $(nc)
#	ocamlopt -cclib -lcrypto $(nc) -a -o s.cmxa 

clean:
	rm -f runtime.o runtime.cmi runtime.cmo runtime.cmx
