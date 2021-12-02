# ml_files = ["server.ml", "synth_stats_model/make_stats.ml"] + Dir.glob("shared/*.ml") + Dir.glob("lib/*.ml")
# js_files = ["assets/maniposynth.js", "assets/reload_on_file_changes.js"]

ml_files = Dir.glob("smyth-main/lib/smyth/*.ml")
js_files = []

ml_lines_count = 0

ml_files.each do |path|
  lines_count = File.read(path).split(/\s*\n\s*/).count
  puts "#{lines_count}\t#{path}"
  ml_lines_count += lines_count
end

js_lines_count = 0

js_files.each do |path|
  lines_count = File.read(path).split(/\s*\n\s*/).count
  puts "#{lines_count}\t#{path}"
  js_lines_count += lines_count
end

puts "#{ml_lines_count}\tlines of OCaml"
puts "#{js_lines_count}\tlines of Javascript"
