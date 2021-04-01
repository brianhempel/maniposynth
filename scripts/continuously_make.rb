#!/usr/bin/env ruby

# Expected to be run from the project root via `make watch`.

server_pid = nil

at_exit do
  begin
    server_pid && Process.kill(-2, server_pid) # kill process group
  rescue
  end
end

loop do
  if system("make --question")
    sleep 0.1
  else
    success = system("TERM=xterm make")
    puts
    if success
      if server_pid
        begin
          Process.kill(-2, server_pid) # kill process group
          Process.wait
        rescue
        end
      end
      server_pid = Process.spawn("make run",  :pgroup => true)
    end
  end
end
