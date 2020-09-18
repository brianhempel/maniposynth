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
  });

  // Add drop zone events.

  document.querySelectorAll('[data-scope-id-str],[data-expr-id-str]').forEach(elem => {
    elem.addEventListener("dragover", dragover);
    elem.addEventListener("dragleave", dragleave);
    elem.addEventListener("drop", drop);
  });
});
