function doAction(action) {
  let request = new XMLHttpRequest();
  request.open("PATCH", document.location.href);
  request.setRequestHeader("Content-type", "application/json");
  request.addEventListener("loadend", () => document.location.reload() );
  request.send(JSON.stringify(action));
}

function addCodeToScopeBindings(newCode, scopeIdStr) {
  doAction([
    "AddCodeToScopeBindings",
    newCode,
    scopeIdStr
  ]);
}

function replaceCodeAtExpr(newCode, exprIdStr) {
  doAction([
    "ReplaceCodeAtExpr",
    newCode,
    exprIdStr
  ]);
}

function destructAndReplaceCodeAtExpr(destructPathStr, exprIdStr) {
  doAction([
    "DestructAndReplaceCodeAtExpr",
    destructPathStr,
    exprIdStr
  ]);
}


//////////////// Drag and Drop /////////////////////////////////

function draggableHover(event) {
  event.currentTarget.classList.add("draggable-hovered");
  event.stopPropagation();
}

function draggableUnhover(event) {
  event.currentTarget.classList.remove("draggable-hovered");
}

// When drag starts, store information.
function dragstart(event) {
  let node = event.target;
  if (node.dataset.newCode)         { event.dataTransfer.setData("application/new-code", node.dataset.newCode); }
  if (node.dataset.destructPathStr) { event.dataTransfer.setData("application/destruct-path-str", node.dataset.destructPathStr); }
}

function dragend(event) {
  document.querySelectorAll('.current-drop-target').forEach(elem => {
    elem.classList.remove("current-drop-target");
  });
}

function dragover(event) {
  // Ignore child elements of the drop target.
  if (event.target === event.currentTarget) {
    event.preventDefault();
    event.dataTransfer.dropEffect = "copy";
    event.currentTarget.classList.add("current-drop-target");
  }
}

function dragleave(event) {
  event.currentTarget.classList.remove("current-drop-target");
}

function drop(event) {
  event.preventDefault();
  let dropTarget = event.currentTarget;
  let newCode = event.dataTransfer.getData("application/new-code");
  let destructPathStr = event.dataTransfer.getData("application/destruct-path-str");
  if (dropTarget.dataset.scopeIdStr && dropTarget.classList.contains("bindings") && newCode) {
    addCodeToScopeBindings(newCode, dropTarget.dataset.scopeIdStr);
    event.stopPropagation();
  } else if (dropTarget.dataset.exprIdStr) {
    if (newCode) {
      replaceCodeAtExpr(newCode, dropTarget.dataset.exprIdStr);
    } else if (destructPathStr) {
      destructAndReplaceCodeAtExpr(destructPathStr, dropTarget.dataset.exprIdStr);
    }
    event.stopPropagation();
  } else {
    console.log("No valid actions for drop on");
    console.log(dropTarget);
  }
}

// Attach event handlers on load.
window.addEventListener('DOMContentLoaded', () => {

  // Make appropriate items draggable.

  document.querySelectorAll('[data-new-code],[data-destruct-path-str]').forEach(elem => {
    elem["draggable"] = true;
  });

  document.querySelectorAll('[draggable=true]').forEach(elem => {
    elem.addEventListener("dragstart", dragstart);
    elem.addEventListener("dragend", dragend);
    elem.addEventListener("mouseover", draggableHover);
    elem.addEventListener("mouseout", draggableUnhover);
  });

  // Add drop zone events.

  document.querySelectorAll('[data-scope-id-str],[data-expr-id-str]').forEach(elem => {
    elem.addEventListener("dragover", dragover);
    elem.addEventListener("dragleave", dragleave);
    elem.addEventListener("drop", drop);
  });
});




/////////////////// Example Management ///////////////////


function current_frame_n() {
  // Frame 0 is the toplevel, frame 1 is the first function call.
  return parseInt(sessionStorage.getItem("current_frame_n")) || 1;
}

function set_frame_n(frame_n) {
  sessionStorage.setItem("current_frame_n", parseInt(frame_n));
  show_current_frame_values();
  return current_frame_n();
}

function show_current_frame_values() {
  var frames_seen = [];
  var anything_visible = false;
  document.querySelectorAll('[data-frame-n]').forEach(elem => {
    elem.classList.remove("in-current-frame");
    let frame_n = parseInt(elem.dataset.frameN);
    frames_seen.push(frame_n);
    if (current_frame_n() === frame_n) {
      elem.classList.add("in-current-frame");
      anything_visible = true;
    }
  });
  if (!anything_visible && frames_seen.length >= 1) {
    set_frame_n(frames_seen[0]);
  }
}

// Attach event handlers on load.
window.addEventListener('DOMContentLoaded', () => {

  document.querySelectorAll('[data-frame-n]').forEach(elem => {
    elem.addEventListener("mouseover", e => set_frame_n(e.currentTarget.dataset.frameN));
  });

  document.querySelectorAll('[data-failure-in-frame-n]').forEach(elem => {
    elem.addEventListener("click", e => set_frame_n(e.currentTarget.dataset.failureInFrameN));
  });

  show_current_frame_values();
});
