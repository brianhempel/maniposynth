_build/default/parse_test.exe:
	dune build parse_test.exe

run: _build/default/parse_test.exe
	./_build/default/parse_test.exe

# Open an OCaml REPL.
# May need to run `opam install utop`
repl:
	dune utop

# Auto-rebuild on save.
watch:
	dune build -w parse_test.exe

setup:
	opam switch 4.11.0 || opam switch create 4.11.0
	opam install utop
	opam install dune
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
