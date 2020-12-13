#!/usr/bin/env ruby

# Expected to be run from the project root via `make watch`.

EXE_PATH = "_build/default/interpreter.exe"

# server_pid = nil

loop do
  if system("make --question")
    sleep 0.1
  else
    success = system("TERM=xterm make build_and_run")
    # if success
    # #   if server_pid
    # #     Process.kill(3, server_pid)
    # #     Process.wait
    # #   end
    # #   server_pid = Process.spawn("./" + EXE_PATH)
    #   system("./" + EXE_PATH)
    # end
  end
end
