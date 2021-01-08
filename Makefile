./_build/default/interpreter.exe: *.ml dune **/dune # lib/*.ml lib/*.mli dune **/dune
	# Maybe dune doesn't update the executable if the file has no changes, confusing Make about dirtiness. This fixes.
	touch ./_build/default/interpreter.exe; dune build --auto-promote interpreter.exe

build_and_run: ./_build/default/interpreter.exe
	OCAMLINTERP_DEBUG=true ./_build/default/interpreter.exe

clean:
	rm -rf _build/

watch:
	ruby scripts/continuously_make.rb

setup:
	opam init
	opam switch 4.07.1 || opam switch create 4.07.1
	opam install utop
	# opam install base stdio
	curl -L https://github.com/ocaml/ocaml/archive/4.07.1.zip > ocaml-4.07.1.zip
	unzip ocaml-4.07.1.zip
	# Need to make to create certain generated stdlib .ml files
	cd ocaml-4.07.1 && ./configure && make world.opt
