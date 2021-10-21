# ![The Magnificent Maniposynth](assets/maniposynth.svg)

Visual non-linear editing, live programming, and synthesis for (some of) OCaml.

## Development

```
$ make setup
```

```
$ make watch # Rebuilds on file changes
# OR
$ make run
$ make ./_build/default/server.exe # If you don't want to run
```

Running Maniposynth starts a webserver at [http://localhost:1111/](http://localhost:1111/). Make a file (e.g. `simple.ml`) in the directory in which you started the server, then append that file name to the url (e.g. [http://localhost:1111/simple.ml](http://localhost:1111/simple.ml)).

```
$ make repl # Opens utop with project modules opened (see .ocamlinit)
```

```
$ make clean
```

For scratchwork, make a  `scratch.ml` at the top level, uncomment the scratch bits in the  `dune` file, then, to build and run:

```
$ make scratch
```

## Artifact for User Study

```
$ make artifact.zip
```

