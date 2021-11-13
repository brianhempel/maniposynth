corpus:
	mkdir corpus; curl -L https://github.com/Ekdohibs/ocaml/archive/31e7a6dd1aa50a31a236dbcfc555dad0bdb9b600.zip > ocaml-4.07.1.zip
	unzip ocaml-4.07.1.zip
	rm ocaml-4.07.1.zip
	mv ocaml-31e7a6dd1aa50a31a236dbcfc555dad0bdb9b600/ ocaml-4.07.1
	# Need to make to create certain generated stdlib .ml files
	cd ocaml-4.07.1 && ./configure -no-debugger -no-ocamldoc -no-ocamlbuild -no-graph && make world.opt
	mv ocaml-4.07.1 corpus/ocaml-4.07.1
	make apply_fixes_for_stats

apply_fixes_for_stats:
	# Not complete fixes (eventually I gave up and just had the analyzer skip stuff)
	cp fixes/targetint.ml corpus/ocaml-4.07.1/utils/targetint.ml
	cp fixes/flambda_utils.ml corpus/ocaml-4.07.1/middle_end/flambda_utils.ml
	cp fixes/flambda_iterators.ml corpus/ocaml-4.07.1/middle_end/flambda_iterators.ml
	cp fixes/freshening.ml corpus/ocaml-4.07.1/middle_end/freshening.ml
	cp fixes/simple_value_approx.ml corpus/ocaml-4.07.1/middle_end/simple_value_approx.ml
	cp fixes/import_approx.ml corpus/ocaml-4.07.1/asmcomp/import_approx.ml
	cp fixes/build_export_info.ml corpus/ocaml-4.07.1/asmcomp/build_export_info.ml
	cp fixes/inline_and_simplify_aux.ml corpus/ocaml-4.07.1/middle_end/inline_and_simplify_aux.ml
	cp fixes/invariant_params.ml corpus/ocaml-4.07.1/middle_end/invariant_params.ml
	cp fixes/flambda_to_clambda.ml corpus/ocaml-4.07.1/asmcomp/flambda_to_clambda.ml
	cp fixes/middle_end.ml corpus/ocaml-4.07.1/middle_end/middle_end.ml
	cp fixes/closure_conversion.ml corpus/ocaml-4.07.1/middle_end/closure_conversion.ml
	cp fixes/lift_code.ml corpus/ocaml-4.07.1/middle_end/lift_code.ml
	cp fixes/lift_constants.ml corpus/ocaml-4.07.1/middle_end/lift_constants.ml


# test_compiler:
# 	cd camlboot_interpreter_for_stats; dune build interp.exe
# 	OCAMLINTERP_DEBUG=true OCAMLRUNPARAM=b OCAMLINTERP_COMMAND=ocamlc OCAMLINTERP_STDLIB_PATH=corpus/ocaml-4.07.1/stdlib  OCAMLINTERP_SRC_PATH=corpus/ocaml-4.07.1 ../_build/default/synth_stats_model/camlboot_interpreter_for_stats/interp.exe -nopervasives -nostdlib -I corpus/ocaml-4.07.1/stdlib -I corpus/ocaml-4.07.1/asmcomp -I corpus/ocaml-4.07.1/asmrun -I corpus/ocaml-4.07.1/boot -I corpus/ocaml-4.07.1/bytecomp -I corpus/ocaml-4.07.1/byterun -I corpus/ocaml-4.07.1/compilerlibs -I corpus/ocaml-4.07.1/config -I corpus/ocaml-4.07.1/debugger -I corpus/ocaml-4.07.1/driver -I corpus/ocaml-4.07.1/experimental -I corpus/ocaml-4.07.1/flexdll -I corpus/ocaml-4.07.1/lex -I corpus/ocaml-4.07.1/man -I corpus/ocaml-4.07.1/manual -I corpus/ocaml-4.07.1/middle_end -I corpus/ocaml-4.07.1/ocamldoc -I corpus/ocaml-4.07.1/ocamltest -I corpus/ocaml-4.07.1/otherlibs -I corpus/ocaml-4.07.1/parsing -I corpus/ocaml-4.07.1/testsuite -I corpus/ocaml-4.07.1/tools -I corpus/ocaml-4.07.1/toplevel -I corpus/ocaml-4.07.1/typing -I corpus/ocaml-4.07.1/utils -I corpus/ocaml-4.07.1/yacc stdlib.ml test.ml

stats:
	dune build make_stats.exe
	make apply_fixes_for_stats
	OCAMLRUNPARAM=b OCAMLINTERP_DEBUG=true OCAMLINTERP_STDLIB_PATH=corpus/ocaml-4.07.1/stdlib OCAMLINTERP_SRC_PATH=corpus/ocaml-4.07.1 ../_build/default/synth_stats_model/make_stats.exe

