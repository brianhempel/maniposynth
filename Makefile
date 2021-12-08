# Usually I run "make watch", but if it's acting goofy, "make run" is okay as well.
# "make watch" will run "make" and then "make run" and will kill/restart "make run" on "make" success.

./_build/default/server.exe: server.ml dune **/dune lib/*.ml shared/*.ml camlboot_interpreter/*.ml
	# Maybe dune doesn't update the executable if the file has no changes, confusing Make about dirtiness. This fixes.
	touch ./_build/default/server.exe; dune build --auto-promote server.exe

run: ./_build/default/server.exe
	OCAMLRUNPARAM=b ./_build/default/server.exe

profile:
	# Must already be running, samples for 10 seconds
	sample server.exe

# synth_stats:
# 	cd synth_stats_model; make corpus
# 	dune build --auto-promote synth_stats_model.exe
# 	./_build/default/synth_stats_model.exe

# Artifact for distributing to study participants.
artifact:
	rm -r artifact.zip; rm -rf artifact; mkdir artifact; cp ./_build/default/server.exe artifact/maniposynth
	cp -r assets artifact/assets
	rm -r artifact/assets/*.amdn; # don't need rich image files
	mkdir -p artifact/ocaml-4.07.1/stdlib; cp -r ocaml-4.07.1/stdlib/*.ml artifact/ocaml-4.07.1/stdlib/
	cp ocaml-4.07.1/stdlib/*.cmi artifact/
	cp ARTIFACT_README.md artifact/
	cp -r expert_eval_manual artifact/examples
	rm artifact/examples/*-old.ml
	zip artifact -r artifact

# build_and_run: ./_build/default/interpreter.exe
# 	OCAMLINTERP_DEBUG=true ./_build/default/interpreter.exe

./_build/default/scratch.exe: scratch.ml dune simple.ml
	# Maybe dune doesn't update the executable if the file has no changes, confusing Make about dirtiness. This fixes.
	touch ./_build/default/scratch.exe; dune build --auto-promote scratch.exe

scratch: ./_build/default/scratch.exe
	./_build/default/scratch.exe

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

repl:
	# See .ocamlinit for preamble commands run.
	dune utop || ./_build/default/.utop/utop.exe

clean:
	rm -rf _build/

watch:
	ruby scripts/continuously_make.rb

setup:
	opam init
	opam switch 4.07.1 || opam switch create 4.07.1
	opam install utop
	# opam install core
	opam install ocamlformat
	opam install yojson
	# opam install ppxlib
	# opam install ppx_yojson_conv
	# opam install ppx_yojson_conv_lib
	opam install uri
	# opam install lz4
	opam install base64
	curl -L https://github.com/ocaml/ocaml/archive/4.07.1.zip > ocaml-4.07.1.zip
	unzip ocaml-4.07.1.zip
	# Need to make to create certain generated stdlib .ml files
	cd ocaml-4.07.1 && ./configure && make world.opt
	# Install the Highlight extension (fabiospampinato.vscode-highlight) in vscode
	# (There's a setting in .vscode/settings.json that will dim OCaml attribute
	# annotations, thus making Maniposynth user code a little bit less noisy.)
