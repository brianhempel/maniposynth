#!/usr/bin/env ruby

# Expected to be run from the project root via `make watch`.

EXE_PATH = "_build/default/test.exe"


server_pid = nil

loop do
  if system("make --question")
    sleep 0.2
  else
    success = system("TERM=xterm make")
    system("touch #{EXE_PATH}") # Maybe dune doesn't update the executable if the file has no changes. Then make wants to continuously re-run. This fixes.
    puts
    if success
      if server_pid
        Process.kill(3, server_pid)
        Process.wait
      end
      server_pid = Process.spawn("./_build/default/test.exe")
    end
  end
end
