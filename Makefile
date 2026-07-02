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

./_build/default/maniposynth_in_js.bc.js: maniposynth_in_js.ml dune **/dune lib/*.ml shared/*.ml camlboot_interpreter/*.ml
	# Maybe dune doesn't update the executable if the file has no changes, confusing Make about dirtiness. This fixes.
	touch ./_build/default/maniposynth_in_js.bc.js; dune build --auto-promote maniposynth_in_js.bc.js

js: ./_build/default/maniposynth_in_js.bc.js


# synth_stats:
# 	cd synth_stats_model; make corpus
# 	dune build --auto-promote synth_stats_model.exe
# 	./_build/default/synth_stats_model.exe

# Artifact for distributing to study participants, AEC, etc.
.PHONY: artifact
artifact:
	make ./_build/default/server.exe
	rm -r artifact.zip; rm -rf artifact; mkdir artifact; cp ./_build/default/server.exe artifact/maniposynth
	cp -r assets artifact/assets
	rm -r artifact/assets/*.amdn; # don't need rich image files
	rm -r artifact/assets/Maniposynth_Overview.mp4; # don't include the video
	mkdir -p artifact/ocaml-4.07.1/stdlib; cp -r ocaml-4.07.1/stdlib/*.ml artifact/ocaml-4.07.1/stdlib/
	cp ocaml-4.07.1/stdlib/*.cmi artifact/
	cp ARTIFACT_README.md artifact/
	mkdir -p artifact/.vscode
	cp .vscode/settings.json artifact/.vscode/settings.json
	cp -r expert_eval_manual artifact/examples
	rm artifact/examples/*-old.ml; zip artifact -r artifact

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

# SETUP
#
# Maniposynth requires OCaml 4.07.1.
#
# Apple Silicon (arm64) note: OCaml 4.07.1 predates native arm64 support, so
# opam refuses to install it on arm64 ("No compiler matching '4.07.1' found" --
# the ocaml-base-compiler.4.07.1 package is marked `available: ! (os = "macos"
# & arch = "arm64")`). Build it as an x86_64 toolchain under Rosetta 2 instead:
#
#     softwareupdate --install-rosetta --agree-to-license   # once
#     arch -x86_64 make setup                               # note the prefix
#
# Running under `arch -x86_64` makes opam (and ./configure below) report
# arch=x86_64, which satisfies the compiler's availability constraint. Keep
# using the `arch -x86_64` prefix for every opam command in this switch. The
# resulting x86_64 binaries run transparently under Rosetta, so plain
# `make run` / `make watch` work without the prefix. On Intel Macs and Linux,
# drop the `arch -x86_64` prefix entirely.

setup:
	opam init
	make install_deps

# OPAMYES makes the opam commands below non-interactive (assume yes).
install_deps: export OPAMYES := 1
install_deps:
	# Project-local switch pinned to 4.07.1 (lives in ./_opam). Idempotent:
	# if it already exists that's fine -- opam auto-selects ./_opam in this dir.
	opam switch create . 4.07.1 --no-install || true
	# opam archived all pre-4.08 package versions; add the archive repo so the
	# old dependency versions below still resolve on this switch.
	opam repository add archive git+https://github.com/ocaml/opam-repository-archive || true
	# Install the EXACT, fully-pinned dependency set -- every transitive package
	# at a known-good version -- recorded in maniposynth.opam.export. This is the
	# source of truth so a drifting opam-repository can't swap in a newer release
	# that fails to build on this old 4.07.1 switch. After an intentional
	# dependency change, regenerate it with:
	#   arch -x86_64 opam switch export --full maniposynth.opam.export
	opam switch import maniposynth.opam.export
	# For reference, `import` is equivalent to these top-level installs (the
	# pins matter -- see each note):
	#   opam install utop.2.9.2 yojson.2.2.2 base64.3.5.2
	#   opam install js_of_ocaml.4.0.0 js_of_ocaml-ppx.4.0.0 js_of_ocaml-compiler.4.0.0
	#   # ocamlformat: base pinned to v0.12.2 -- base >= v0.14 won't build on 4.07
	#   # (its build script uses the 4.08-only `Fun` module).
	#   opam install ocamlformat.0.16.0 base.v0.12.2 sexplib0.v0.12.0 stdio.v0.12.0
	#   # uri pinned < 4.0 -- uri 4.x pulls in angstrom -> bigstringaf ->
	#   # conf-pkg-config, which needs a system `pkgconf`; uri 3.1.0 uses `re`.
	#   C_INCLUDE_PATH=`ocamlc -where`:$C_INCLUDE_PATH opam install uri.3.1.0
	# The interpreter reads the stdlib *.ml SOURCE files from ./ocaml-4.07.1/stdlib
	# at runtime (see camlboot_interpreter/conf.ml), so fetch the compiler sources:
	curl -L https://github.com/ocaml/ocaml/archive/4.07.1.zip > ocaml-4.07.1.zip
	unzip ocaml-4.07.1.zip
	# sys.ml is the only generated stdlib source; produce it with the compiler's
	# own sed rule (substitutes %%VERSION%%). We deliberately do NOT run
	# `make world.opt`: this pre-arm64 compiler can't bootstrap under Rosetta on
	# Apple Silicon (the boot ocamlrun dies with "Sys.getcwd not implemented"),
	# and local dev only needs the *.ml sources. The stdlib *.cmi files -- used
	# only by the standalone `artifact` target -- require a native 4.07 build on
	# an Intel Mac or Linux.
	sed -e "s|%%VERSION%%|`sed -e 1q ocaml-4.07.1/VERSION | tr -d '\r'`|" \
	    ocaml-4.07.1/stdlib/sys.mlp > ocaml-4.07.1/stdlib/sys.ml
	# Install the Highlight extension (fabiospampinato.vscode-highlight) in vscode
	# (There's a setting in .vscode/settings.json that will dim OCaml attribute
	# annotations, thus making Maniposynth user code a little bit less noisy.)
