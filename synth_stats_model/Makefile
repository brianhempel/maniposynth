corpus:
	mkdir corpus; curl -L https://github.com/Ekdohibs/ocaml/archive/31e7a6dd1aa50a31a236dbcfc555dad0bdb9b600.zip > ocaml-4.07.1.zip
	# mkdir corpus; curl -L https://github.com/ocaml/ocaml/archive/4.07.1.zip > ocaml-4.07.1.zip
	unzip ocaml-4.07.1.zip
	rm ocaml-4.07.1.zip
	mv ocaml-31e7a6dd1aa50a31a236dbcfc555dad0bdb9b600/ ocaml-4.07.1
	# Need to make to create certain generated stdlib .ml files
	cd ocaml-4.07.1 && ./configure -no-debugger -no-native-compiler -no-ocamldoc -no-ocamlbuild -no-graph && make world
	mv ocaml-4.07.1 corpus/ocaml-4.07.1

test_compiler:
	cd camlboot_interpreter_for_stats; dune build interp.exe
	OCAMLINTERP_DEBUG=true OCAMLRUNPARAM=b OCAMLINTERP_COMMAND=ocamlc OCAMLINTERP_STDLIB_PATH=corpus/ocaml-4.07.1/stdlib OCAMLINTERP_STDLIB_PATH=corpus/ocaml-4.07.1/stdlib OCAMLINTERP_SRC_PATH=corpus/ocaml-4.07.1 ../_build/default/synth_stats_model/camlboot_interpreter_for_stats/interp.exe -nopervasives -nostdlib -I corpus/ocaml-4.07.1/stdlib -I corpus/ocaml-4.07.1/asmcomp -I corpus/ocaml-4.07.1/asmrun -I corpus/ocaml-4.07.1/boot -I corpus/ocaml-4.07.1/bytecomp -I corpus/ocaml-4.07.1/byterun -I corpus/ocaml-4.07.1/compilerlibs -I corpus/ocaml-4.07.1/config -I corpus/ocaml-4.07.1/debugger -I corpus/ocaml-4.07.1/driver -I corpus/ocaml-4.07.1/experimental -I corpus/ocaml-4.07.1/flexdll -I corpus/ocaml-4.07.1/lex -I corpus/ocaml-4.07.1/man -I corpus/ocaml-4.07.1/manual -I corpus/ocaml-4.07.1/middle_end -I corpus/ocaml-4.07.1/ocamldoc -I corpus/ocaml-4.07.1/ocamltest -I corpus/ocaml-4.07.1/otherlibs -I corpus/ocaml-4.07.1/parsing -I corpus/ocaml-4.07.1/testsuite -I corpus/ocaml-4.07.1/tools -I corpus/ocaml-4.07.1/toplevel -I corpus/ocaml-4.07.1/typing -I corpus/ocaml-4.07.1/utils -I corpus/ocaml-4.07.1/yacc stdlib.ml test.ml