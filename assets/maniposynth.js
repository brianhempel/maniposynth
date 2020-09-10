function addCodeToScopeBindings(newCode, scopeIdJson) {
  let action = [
    "AddCodeToScopeBindings",
    newCode,
    scopeIdJson
  ];
  var request = new XMLHttpRequest();
  request.open("PATCH", document.location.href);
  request.setRequestHeader("Content-type", "application/json");
  request.send(JSON.stringify(action));
}


//////////////// Drag and Drop /////////////////////////////////


// When drag starts, store information.
function dragstart(event) {
  node = event.target;
  event.dataTransfer.setData("application/new-code", node.dataset.newCode);
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
  dropTarget = event.currentTarget;
  newCode = event.dataTransfer.getData("application/new-code");
  scopeIdJson = JSON.parse(dropTarget.dataset.scopeIdJsonStr);
  if (dropTarget.classList.contains("bindings")) {
    addCodeToScopeBindings(newCode, scopeIdJson);
  } else if (dropTarget.classList.contains("rets")) {
    addCodeToScopeRet(newCode, scopeIdJson);
  }
}

// Attach event handlers on load.
window.addEventListener('DOMContentLoaded', () => {

  // Make appropriate items draggable.

  document.querySelectorAll('[data-new-code]').forEach(elem => {
    elem["draggable"] = true;
  });

  document.querySelectorAll('[draggable=true]').forEach(elem => {
    elem.addEventListener("dragstart", dragstart);
    elem.addEventListener("dragend", dragend);
  });

  // Add drop zone events.

  document.querySelectorAll('[data-scope-id-json-str]').forEach(elem => {
    elem.addEventListener("dragover", dragover);
    elem.addEventListener("dragleave", dragleave);
    elem.addEventListener("drop", drop);
  });
});
