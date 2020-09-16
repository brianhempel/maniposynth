_build/default/server.exe: *.ml lib/*.ml lib/*.mli dune **/dune
	dune build --auto-promote server.exe

_build/default/playing.exe: *.ml lib/*.ml lib/*.mli dune **/dune
	dune build --auto-promote playing.exe

clean:
	rm -rf _build/

hard_reset:
	make clean; rm -rf vendor; rm -rf ../custom_merlin

run: _build/default/server.exe
	./_build/default/server.exe

run_playing: _build/default/playing.exe
	./_build/default/playing.exe

# Open an OCaml REPL.
# May need to run `opam install utop`
repl:
	dune utop

# Auto-rebuild on save.
watch:
	# Dune's watch just keeps rebuilding over and over. Use our own.
	./scripts/continuously_make.rb

# Our version of merlin with a dump typedtree command.
# Can't install in a subdir because that confuses dune. Will be installed in a dir next to the maniposynth dir
../custom_merlin/ocamlmerlin:
	cd ..; git clone --branch dump_typedtree https://github.com/brianhempel/merlin.git custom_merlin; cd custom_merlin && make

setup:
	opam switch 4.11.0 || opam switch create 4.11.0
	opam install utop
	opam install dune
	opam install tyxml
	opam install merlin
	opam install yojson
	opam install ppxlib
	opam install ppx_yojson_conv
	opam install ppx_yojson_conv_lib
	# Using ocamlformat's parser/printer, which preserves comments.
	mkdir vendor; cd vendor; curl -L https://github.com/ocaml-ppx/ocamlformat/archive/0.15.0.zip > ocamlformat-0.15.0.zip && unzip ocamlformat-0.15.0.zip && mv ocamlformat-0.15.0 ocamlformat
	# Need to make certain sub-libraries public so dune will build the whole gambit.
	# Add "(public_name ocamlformat.asdf)" after "(library (name asdf)" to the appropriate dune files.
	ruby -e 'ARGV.each {|path| File.write(path, File.read(path).sub(/\(library\s+\(name (\w+)\)/, "\\0\n (public_name ocamlformat.\\1)"))}' vendor/ocamlformat/lib/dune vendor/ocamlformat/lib/*/dune vendor/ocamlformat/vendor/*/dune vendor/ocamlformat/vendor/*/lib/dune
	# Need to expose an ocamlformat profile to use
	echo ""                            >> vendor/ocamlformat/lib/Conf.mli
	echo "val ocamlformat_profile : t" >> vendor/ocamlformat/lib/Conf.mli
	# Expose the formatter itself
	echo ""                                                 >> vendor/ocamlformat/lib/Translation_unit.mli
	echo "type 'a t"                                        >> vendor/ocamlformat/lib/Translation_unit.mli
	echo ""                                                 >> vendor/ocamlformat/lib/Translation_unit.mli
	echo "val impl : Parsetree.toplevel_phrase list t"      >> vendor/ocamlformat/lib/Translation_unit.mli
	echo ""                                                 >> vendor/ocamlformat/lib/Translation_unit.mli
	echo "val format :"                                     >> vendor/ocamlformat/lib/Translation_unit.mli
	echo "     'a t"                                        >> vendor/ocamlformat/lib/Translation_unit.mli
	echo "  -> ?output_file:string"                         >> vendor/ocamlformat/lib/Translation_unit.mli
	echo "  -> input_name:string"                           >> vendor/ocamlformat/lib/Translation_unit.mli
	echo "  -> source:string"                               >> vendor/ocamlformat/lib/Translation_unit.mli
	echo "  -> parsed:'a Parse_with_comments.with_comments" >> vendor/ocamlformat/lib/Translation_unit.mli
	echo "  -> Conf.t"                                      >> vendor/ocamlformat/lib/Translation_unit.mli
	echo "  -> Conf.opts"                                   >> vendor/ocamlformat/lib/Translation_unit.mli
	echo "  -> (string, error) result"                      >> vendor/ocamlformat/lib/Translation_unit.mli
	# Turn off the check that requires the AST not to change between parse/unparse
	ruby -e 'path = ARGV[0]; File.write(path, File.read(path).sub(/\(\* Ast not preserved \? \*\)\s+\( if/, "\\0 false && (* Maniposynth hotfix! *)"))' vendor/ocamlformat/lib/Translation_unit.ml
	# Ensure we have our custom version of merlin that can dump typedtrees
	# Can't install in a subdir because that confuses dune. Will be installed in a dir next to the maniposynth dir
	make ../custom_merlin/ocamlmerlin
