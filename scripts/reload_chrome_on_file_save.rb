#!/usr/bin/env ruby

# Expected to be run from the project root via `make chrome_reloader`.

# https://stackoverflow.com/a/7335517
APPLESCRIPT = <<-APPLESCRIPT
tell application "Google Chrome" to tell the active tab of its first window
    reload
end tell
APPLESCRIPT

MOD_TIMES = {}

EXTENTIONS_TO_WATCH = %w[html css js jpg jpeg png gif]

loop do
  paths = EXTENTIONS_TO_WATCH.flat_map { |extn| Dir.glob("**/*.#{extn}") }
  10.times do
    should_reload = false
    paths.each do |path|
      mod_time = File.mtime(path)
      should_reload = true if !MOD_TIMES[path] || MOD_TIMES[path] < mod_time
      MOD_TIMES[path] = mod_time
    end
    if should_reload
      system("osascript -e '#{APPLESCRIPT}'")
    else
      sleep 0.1
    end
  end
end
