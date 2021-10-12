## vim

```
:set autoread | au CursorHold * checktime | call feedkeys("lh")
```

via https://superuser.com/a/1286322

After cursor stops moving, checks every *updatetime* seconds for file changes (every 4 seconds). (More specifically, it waits for the cursor to stop moving for some time, then checks disk, then moves the cursor again “lh” to retrigger and loop.)

I’m a fan of faster polling, so the following will poll every half second instead:

```
:set updatetime=500
```

If you get annoying bells, [turn vim’s bell off](https://unix.stackexchange.com/a/5313):

```
:set visualbell t_vb=
```

## emacs

f10 to go to menu

Options > Customize Emacs > Specific Option

type `global-auto-revert-mode`

Navigate cursor to `[ Toggle ]` hit Enter. Navigate to `[ Apply and Save ]` hit enter.

