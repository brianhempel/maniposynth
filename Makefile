./_build/default/server.exe: *.ml dune **/dune **/*.ml # lib/*.ml lib/*.mli dune **/dune
	# Maybe dune doesn't update the executable if the file has no changes, confusing Make about dirtiness. This fixes.
	touch ./_build/default/server.exe; dune build --auto-promote server.exe

run: ./_build/default/server.exe
	./_build/default/server.exe

# build_and_run: ./_build/default/interpreter.exe
# 	OCAMLINTERP_DEBUG=true ./_build/default/interpreter.exe

./_build/default/interpret_simple_ml.exe: *.ml dune **/dune **/*.ml # lib/*.ml lib/*.mli dune **/dune
	# Maybe dune doesn't update the executable if the file has no changes, confusing Make about dirtiness. This fixes.
	touch ./_build/default/interpret_simple_ml.exe; dune build --auto-promote interpret_simple_ml.exe

interpret_simple_ml: ./_build/default/interpret_simple_ml.exe
	OCAMLINTERP_DEBUG=true ./_build/default/interpret_simple_ml.exe

./_build/default/interpret_intepreter_interpreting_simple_ml.exe: *.ml dune **/dune **/*.ml # lib/*.ml lib/*.mli dune **/dune
	# Maybe dune doesn't update the executable if the file has no changes, confusing Make about dirtiness. This fixes.
	touch ./_build/default/interpret_intepreter_interpreting_simple_ml.exe; dune build --auto-promote interpret_intepreter_interpreting_simple_ml.exe

interpret_intepreter_interpreting_simple_ml:
	OCAMLINTERP_DEBUG=true ./_build/default/interpret_intepreter_interpreting_simple_ml.exe

clean:
	rm -rf _build/

watch:
	ruby scripts/continuously_make.rb

setup:
	opam init
	opam switch 4.07.1 || opam switch create 4.07.1
	opam install utop
	opam install core
	curl -L https://github.com/ocaml/ocaml/archive/4.07.1.zip > ocaml-4.07.1.zip
	unzip ocaml-4.07.1.zip
	# Need to make to create certain generated stdlib .ml files
	cd ocaml-4.07.1 && ./configure && make world.opt
