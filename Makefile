#  Copyright 1997 INRIA
#  $Id: Makefile,v 1.5 2004-04-28 16:30:09 doligez Exp $

CAMLFLAGS = -warn-error A

CAMLOPT = ocamlopt
CAMLOPTFLAGS = ${CAMLFLAGS}

CAMLC = ocamlc
CAMLCFLAGS = ${CAMLFLAGS} -g

CAMLLEX = ocamllex
CAMLYACC = ocamlyacc

MODULES = misc heap globals prio expr phrase llproof mlproof index \
          print step node extension mltoll prove parser lexer tptp \
          ext_coqbool \
          main

IMPL = ${MODULES:%=%.ml}
INTF = ${MODULES:%=%.mli}
OBJBYT = ${MODULES:%=%.cmo}
OBJOPT = ${MODULES:%=%.cmx}

default: all

zenon.opt: ${OBJOPT}
	${CAMLOPT} ${CAMLOPTFLAGS} -o zenon.opt ${OBJOPT}

zenon.byt: ${OBJBYT}
	${CAMLC} ${CAMLCFLAGS} -o zenon.byt ${OBJBYT}

zenon: zenon.opt
	cp zenon.opt zenon

zenon-logo.png: zenon-logo.ps
	gs -sDEVICE=png16m -sOutputFile=zenon-logo.png -r720 -g2400x800 \
	   -dNOPAUSE -dBATCH zenon-logo.ps

all: zenon zenon.opt zenon.byt

.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	${CAMLC} ${CAMLCFLAGS} -c $*.ml

.ml.cmx:
	${CAMLOPT} ${CAMLOPTFLAGS} -c $*.ml

.mli.cmi:
	${CAMLOPT} ${CAMLOPTFLAGS} -c $*.mli

lexer.ml: lexer.mll
	${CAMLLEX} lexer.mll

parser.ml: parser.mly
	${CAMLYACC} parser.mly

parser.mli: parser.ml
	:

clean:
	rm -f *.cmo *.cmi *.cmx *.o
	rm -f parser.ml parser.mli lexer.ml
	rm -f Makefile.bak zenon zenon.opt zenon.byt

test:
	for i in test*.znn test*.coz test*.p; do \
	  echo $$i; \
	  if ./zenon -w -x coqbool $$i; then \
	    : ; \
	  else \
	    echo '>>> TEST FAILED <<<' ; \
	    break ; \
	  fi ; \
	done

depend: ${IMPL} ${INTF}
	mv Makefile Makefile.bak
	(sed -e '/^#DEPENDENCIES/q' Makefile.bak; \
         ocamldep ${IMPL} ${INTF}) \
	>Makefile

# Do NOT change anything below this line.
#DEPENDENCIES
misc.cmo: misc.cmi 
misc.cmx: misc.cmi 
heap.cmo: misc.cmi heap.cmi 
heap.cmx: misc.cmx heap.cmi 
globals.cmo: misc.cmi globals.cmi 
globals.cmx: misc.cmx globals.cmi 
prio.cmo: misc.cmi prio.cmi 
prio.cmx: misc.cmx prio.cmi 
expr.cmo: globals.cmi misc.cmi expr.cmi 
expr.cmx: globals.cmx misc.cmx expr.cmi 
phrase.cmo: expr.cmi misc.cmi phrase.cmi 
phrase.cmx: expr.cmx misc.cmx phrase.cmi 
llproof.cmo: expr.cmi misc.cmi llproof.cmi 
llproof.cmx: expr.cmx misc.cmx llproof.cmi 
mlproof.cmo: expr.cmi misc.cmi mlproof.cmi 
mlproof.cmx: expr.cmx misc.cmx mlproof.cmi 
index.cmo: expr.cmi globals.cmi misc.cmi mlproof.cmi prio.cmi index.cmi 
index.cmx: expr.cmx globals.cmx misc.cmx mlproof.cmx prio.cmx index.cmi 
print.cmo: expr.cmi index.cmi llproof.cmi misc.cmi mlproof.cmi phrase.cmi \
    print.cmi 
print.cmx: expr.cmx index.cmx llproof.cmx misc.cmx mlproof.cmx phrase.cmx \
    print.cmi 
step.cmo: globals.cmi misc.cmi print.cmi step.cmi 
step.cmx: globals.cmx misc.cmx print.cmx step.cmi 
node.cmo: expr.cmi misc.cmi mlproof.cmi prio.cmi node.cmi 
node.cmx: expr.cmx misc.cmx mlproof.cmx prio.cmx node.cmi 
extension.cmo: expr.cmi llproof.cmi misc.cmi mlproof.cmi node.cmi prio.cmi \
    extension.cmi 
extension.cmx: expr.cmx llproof.cmx misc.cmx mlproof.cmx node.cmx prio.cmx \
    extension.cmi 
mltoll.cmo: expr.cmi index.cmi llproof.cmi misc.cmi mlproof.cmi mltoll.cmi 
mltoll.cmx: expr.cmx index.cmx llproof.cmx misc.cmx mlproof.cmx mltoll.cmi 
prove.cmo: expr.cmi extension.cmi globals.cmi heap.cmi index.cmi misc.cmi \
    mlproof.cmi node.cmi print.cmi prio.cmi step.cmi prove.cmi 
prove.cmx: expr.cmx extension.cmx globals.cmx heap.cmx index.cmx misc.cmx \
    mlproof.cmx node.cmx print.cmx prio.cmx step.cmx prove.cmi 
parser.cmo: expr.cmi globals.cmi misc.cmi phrase.cmi parser.cmi 
parser.cmx: expr.cmx globals.cmx misc.cmx phrase.cmx parser.cmi 
lexer.cmo: misc.cmi parser.cmi lexer.cmi 
lexer.cmx: misc.cmx parser.cmx lexer.cmi 
tptp.cmo: expr.cmi lexer.cmi misc.cmi parser.cmi phrase.cmi tptp.cmi 
tptp.cmx: expr.cmx lexer.cmx misc.cmx parser.cmx phrase.cmx tptp.cmi 
ext_coqbool.cmo: expr.cmi extension.cmi globals.cmi index.cmi misc.cmi \
    mlproof.cmi node.cmi prio.cmi ext_coqbool.cmi 
ext_coqbool.cmx: expr.cmx extension.cmx globals.cmx index.cmx misc.cmx \
    mlproof.cmx node.cmx prio.cmx ext_coqbool.cmi 
main.cmo: extension.cmi globals.cmi lexer.cmi misc.cmi mlproof.cmi mltoll.cmi \
    parser.cmi phrase.cmi print.cmi prove.cmi tptp.cmi main.cmi 
main.cmx: extension.cmx globals.cmx lexer.cmx misc.cmx mlproof.cmx mltoll.cmx \
    parser.cmx phrase.cmx print.cmx prove.cmx tptp.cmx main.cmi 
phrase.cmi: expr.cmi 
llproof.cmi: expr.cmi 
mlproof.cmi: expr.cmi 
index.cmi: expr.cmi mlproof.cmi prio.cmi 
print.cmi: expr.cmi llproof.cmi mlproof.cmi phrase.cmi 
step.cmi: expr.cmi mlproof.cmi prio.cmi 
node.cmi: expr.cmi mlproof.cmi prio.cmi 
extension.cmi: expr.cmi llproof.cmi mlproof.cmi node.cmi prio.cmi 
mltoll.cmi: llproof.cmi mlproof.cmi 
prove.cmi: expr.cmi mlproof.cmi 
parser.cmi: phrase.cmi 
lexer.cmi: parser.cmi 
tptp.cmi: phrase.cmi 
