# Maniposynth

## Setup

Make sure you have [opam](https://opam.ocaml.org/) and some version of [Ruby](https://www.ruby-lang.org/en/), and then:

```
$ make setup
```

Note that `make setup` will install a `custom_merlin` folder alongside your `maniposynth` directory. It cannot be a subdir because that confuses dune.

Various make commands:

```
$ make                 # Rebuild.
$ make run             # Run the executable.
$ make repl            # Open an OCaml REPL in the project environment.
$ make clean           # Remove the _build directory.
$ make watch           # Automatically rebuild and run on file save.
```

Read the Makefile for more details.

