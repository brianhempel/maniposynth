# Maniposynth

## Setup

Make sure you have [opam](https://opam.ocaml.org/) and some version of [Ruby](https://www.ruby-lang.org/en/), and then:

```
$ make setup
```

Various make commands:

```
$ make                 # Rebuild.
$ make run             # Run the executable.
$ make repl            # Open an OCaml REPL in the project environment.
$ make clean           # Remove the _build directory.
$ make watch           # Automatically rebuild and run on file save.
$ make chrome_reloader # Reload front tab of chrome whenever an html/css file changes (requires Applescript)
```

Read the Makefile for more details.

