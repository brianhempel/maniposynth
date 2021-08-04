paths_to_watch = [
  document.location.href,
  "/assets/maniposynth.css",
  "/assets/maniposynth.js",
  "/assets/reload_on_file_changes.js"
];

last_seen_versions = {};

function handle_possible_change (path, latest_version) {
  if (!last_seen_versions[path]) {
    // console.log(path + "\n" + latest_version);
    last_seen_versions[path] = latest_version;
  } else if (last_seen_versions[path] != latest_version) {
    document.location.reload();
    return;
  }
  wait_and_check_for_changes(path);
}

function check_for_changes(path) {
  let request = new XMLHttpRequest();
  request.addEventListener("load", function () { handle_possible_change(path, this.responseText) });
  request.addEventListener("error", () => wait_and_check_for_changes(path));
  request.addEventListener("timeout", () => wait_and_check_for_changes(path));
  request.open("GET", path);
  request.send();
}

function wait_and_check_for_changes(path) {
  window.setTimeout(() => check_for_changes(path), 300);
}

window.addEventListener('DOMContentLoaded', () => {
  paths_to_watch.forEach(wait_and_check_for_changes);
});
