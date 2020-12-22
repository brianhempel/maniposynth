Intepreter from Camlboot, a bootstrapping project for OCaml. Forked from https://github.com/Ekdohibs/camlboot/tree/996c0d94e6b930f79b2e532f5b50732db449a809

MIT License

Copyright (c) 2018 Nathanaël Courant

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

# OCaml interpreter

This directory contains an interpreter for OCaml, written in miniml. It aims to be as correct as possible while only using the untyped representation of the program.

It has three main modes:
- `./interp ocamlc`, which will interpret the compiler sources to get a replacement for `ocamlc`,
- `./interp ocamlopt`, which will interpret the compiler sources to get a replacement for `ocamlopt`,
- `./interp files [list of files]`, which will interpret the list of files given as argument.

For now, it is written in a subset of OCaml a bit larger than miniml, but we are working on making it compatible with miniml by avoiding the use of unnecessary features and adding other features to miniml.
