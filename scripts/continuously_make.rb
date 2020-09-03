#!/usr/bin/env ruby

# Expected to be run from the project root via `make watch`.

EXE_PATH = "_build/default/test.exe"

loop do
  if system("make --question")
    sleep 0.2
  else
    success = system("TERM=xterm make")
    system("touch #{EXE_PATH}") # Maybe dune doesn't update the executable if the file has no changes. then make wants to continuously re-run. This fixes.
    system("make run") if success
  end
end
