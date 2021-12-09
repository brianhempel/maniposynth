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

You *must* set up your editor with the OCaml language server. Its type hints, instant errors, and tooltip docs probably doubled my productivity. Also I didn't bother with writing many type annotations because the language server for VS Code shows the function types. Note that type `int` is often displayed as `frame_no`. Ah, type synonyms.

For VS Code: Make sure you've run `opam install ocaml-lsp-server`, and in VS Code install the `OCaml Platform` extension by OCaml Labs.

## Artifact for User Study

```
$ make artifact.zip
```

## User Code

To dim AST attribute annotations to make user code more readable, in VS Code install the Highlight extension (fabiospampinato.vscode-highlight). In this repo, the config file in `.vscode/settings.json` contains the regex and styling for annotations. You may have to edit the styling if you use a dark theme (I use a light theme).