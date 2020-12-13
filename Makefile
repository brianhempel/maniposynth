./_build/default/interpreter.exe: *.ml dune **/dune # lib/*.ml lib/*.mli dune **/dune
	dune build --auto-promote interpreter.exe
	touch ./_build/default/interpreter.exe # Maybe dune doesn't update the executable if the file has no changes, confusing Make about dirtiness. This fixes.

build_and_run: ./_build/default/interpreter.exe
	./_build/default/interpreter.exe

clean:
	rm -rf _build/

watch:
	ruby scripts/continuously_make.rb

setup:
	opam init
	opam switch 4.11.1 || opam switch create 4.11.1
	opam install utop