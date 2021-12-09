# ![The Magnificent Maniposynth](assets/maniposynth.svg)

Visual non-linear editing, live programming, and synthesis for (some of) OCaml.

## Quickstart

Start the server:

```
$ ./maniposynth
```

Then open your browser and navigate to a relative file path, e.g. [http://localhost:1111/examples/length.ml](http://localhost:1111/examples/length.ml). You can also create a new file (in your editor) and type that file path in the URL.

Open up the same file in your editor, side by side, for the full bimodal experience.

If you have `ocamlformat` installed and in your `$PATH`, generated code will have better formatting.

## Live refresh

VS Code will automatically refresh when code is changed on disk. For Vim and Emacs, see below:

### Vim

Thanks to [eli on Super User](https://superuser.com/a/1286322) for this solution. Run this in Vim:

```
:set autoread | au CursorHold * checktime | call feedkeys("lh")
```

After cursor stops moving, this will check every updatetime seconds for file changes, which is every 4 seconds by default. (More specifically, Vim waits for the cursor to stop moving for some time, then checks disk, then moves the cursor again with “lh” to retrigger and loop.)

To poll every half second instead of every 4 seconds:

```
:set updatetime=500
```

If you get annoying bells, [turn Vim’s bell off](https://unix.stackexchange.com/a/5313):

```
:set visualbell t_vb=
```

### Emacs

For Emacs, enable `global-auto-revert-mode`:

1. Hit F10 to go to the top menu
2. Options > Customize Emacs > Specific Option
3. Type `global-auto-revert-mode`
4. Move the cursor to `[ Toggle ]` and hit Enter
5. Move to `[ Apply and Save ]` and hit Enter


## Dimming AST Annotations

To dim AST attribute annotations to make user code more readable, in VS Code install the Highlight extension (fabiospampinato.vscode-highlight). This artifact includes a `.vscode/settings.json` that contains the regex and styling for annotations. It should "just work" if you open this folder in VS code (e.g. via `code artifact`). You may have to edit the styling in `.vscode/settings.json` if you use a dark theme.
