function doAction(action) {
  let request = new XMLHttpRequest();
  request.open("PATCH", document.location.href);
  request.setRequestHeader("Content-type", "application/json");
  request.addEventListener("loadend", () => document.location.reload() );
  request.send(JSON.stringify(action));
}

function dropValueBeforeVb(beforeVbId, value) {
  doAction([
    "DropValueBeforeVb",
    beforeVbId,
    value
  ]);
}

// function addCodeToScopeBindings(newCode, scopeIdStr) {
//   doAction([
//     "AddCodeToScopeBindings",
//     newCode,
//     scopeIdStr
//   ]);
// }

// function replaceCodeAtExpr(newCode, exprIdStr) {
//   doAction([
//     "ReplaceCodeAtExpr",
//     newCode,
//     exprIdStr
//   ]);
// }

// function deleteExpr(exprIdStr) {
//   doAction([
//     "DeleteExpr",
//     exprIdStr
//   ]);
// }

// function destructAndReplaceCodeAtExpr(destructPathStr, exprIdStr) {
//   doAction([
//     "DestructAndReplaceCodeAtExpr",
//     destructPathStr,
//     exprIdStr
//   ]);
// }

// function setExample(funcStr, arg1Str, arg2Str, arg3Str) {
//   doAction([
//     "SetExample",
//     funcStr,
//     arg1Str,
//     arg2Str,
//     arg3Str
//   ]);
// }

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
  if (node.dataset.value) { event.dataTransfer.setData("application/value", node.dataset.value); }
  // if (node.dataset.newCode)         { event.dataTransfer.setData("application/new-code", node.dataset.newCode); }
  // if (node.dataset.destructPathStr) { event.dataTransfer.setData("application/destruct-path-str", node.dataset.destructPathStr); }
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
  let dropTarget      = event.currentTarget;
  let droppedValue    = event.dataTransfer.getData("application/value");
  if (dropTarget.dataset.beforeVbId && droppedValue) {
    dropValueBeforeVb(dropTarget.dataset.beforeVbId, droppedValue);
  // let newCode         = event.dataTransfer.getData("application/new-code");
  // let destructPathStr = event.dataTransfer.getData("application/destruct-path-str");
  // if (dropTarget.dataset.scopeIdStr && dropTarget.classList.contains("bindings") && newCode) {
  //   addCodeToScopeBindings(newCode, dropTarget.dataset.scopeIdStr);
  //   event.stopPropagation();
  // } else if (dropTarget.dataset.exprIdStr) {
  //   if (newCode) {
  //     replaceCodeAtExpr(newCode, dropTarget.dataset.exprIdStr);
  //   } else if (destructPathStr) {
  //     destructAndReplaceCodeAtExpr(destructPathStr, dropTarget.dataset.exprIdStr);
  //   }
  //   event.stopPropagation();
  } else {
    console.warn("No valid actions for drop on ", dropTarget);
  }
}

// Attach event handlers on load.
window.addEventListener('DOMContentLoaded', () => {

  // Make appropriate items draggable.

  document.querySelectorAll('[data-value]').forEach(elem => {
    elem.draggable = true;
  });

  document.querySelectorAll('[draggable=true]').forEach(elem => {
    // console.log(elem);
    elem.addEventListener("dragstart", dragstart);
    elem.addEventListener("dragend", dragend);
    elem.addEventListener("mouseover", draggableHover);
    elem.addEventListener("mouseout", draggableUnhover);
  });

  // Add drop zone events.

  document.querySelectorAll('[data-before-vb-id],[data-before-scope-id]').forEach(elem => {
    elem.addEventListener("dragover", dragover);
    elem.addEventListener("dragleave", dragleave);
    elem.addEventListener("drop", drop);
  });
});


//////////////// Selection /////////////////////////////////

function select(elem) {
  elem.classList.add("selected");
  updateInspector();
}

function deselect(elem) {
  elem.classList.remove("selected");
  updateInspector();
}

function deselectAll() {
  document.querySelectorAll('.selected').forEach(deselect);
}

// Selectable element clicked...
function toggleSelect(event) {
  const elem = event.target;
  event.stopPropagation();
  if (elem.classList.contains("selected")) {
    deselectAll();
  } else {
    deselectAll();
    select(elem);
  }
}

window.addEventListener('DOMContentLoaded', () => {

  // Make appropriate items selectable.

  document.querySelectorAll('[data-value]').forEach(elem => {
    elem.classList.add("selectable");
  });

  document.querySelectorAll('.selectable').forEach(elem => {
    elem.addEventListener("click", toggleSelect);
  });
});


/////////////////// Inspector ///////////////////

window.addEventListener('DOMContentLoaded', () => {
  window.inspector = document.getElementById("inspector");
});

function updateInspector() {
  // START HERE
  // const elems = document.querySelectorAll('.selected');

  // Ideally, offer functions whose type is T -> a where T unifies with the selected item.
  // For now, just allow any expression of type T -> non-function?

  // Easiest way to track types may be to tag the value with its type when introduced...?
  // But values can be introduced in polymorphic context... e.g. (\x -> [x]) 0
  // :/
  // Actually, runtime value to concrete type should be..."fairly" easy.
  // Unification is harder.

  const elem = document.querySelector('.selected');

  if (elem) {
    const type_str = elem.dataset.type || "Unknown";
    window.inspector.innerHTML = type_str;
  } else {
    window.inspector.innerHTML = "";
  }
}

/////////////////// Example Management ///////////////////


// function current_frame_n() {
//   // Frame 0 is the toplevel, frame 1 is the first function call.
//   return parseInt(sessionStorage.getItem("current_frame_n")) || 1;
// }

// function set_frame_n(frame_n) {
//   sessionStorage.setItem("current_frame_n", parseInt(frame_n));
//   show_current_frame_values();
//   return current_frame_n();
// }

// function show_current_frame_values() {
//   var frames_seen = [];
//   var anything_visible = false;
//   document.querySelectorAll('[data-frame-n]').forEach(elem => {
//     elem.classList.remove("in-current-frame");
//     let frame_n = parseInt(elem.dataset.frameN);
//     frames_seen.push(frame_n);
//     if (current_frame_n() === frame_n) {
//       elem.classList.add("in-current-frame");
//       // console.log(elem);
//       anything_visible = true;
//     }
//   });
//   document.querySelectorAll('[data-failure-in-frame-n]').forEach(elem => {
//     elem.classList.remove("in-current-frame");
//     let frame_n = parseInt(elem.dataset.failureInFrameN);
//     if (current_frame_n() === frame_n) {
//       // console.log(elem);
//       elem.classList.add("in-current-frame");
//     }
//   });
//   if (!anything_visible && frames_seen.length >= 1) {
//     set_frame_n(frames_seen[0]);
//   } else {
//     // Hide skeletons on the branch not taken.
//     var paths_taken = [];
//     document.querySelectorAll('[data-branch-path]').forEach(elem => {
//       if (elem.querySelectorAll('.tracesnap.in-current-frame').length >= 1) {
//         paths_taken.push(elem.dataset.branchPath);
//       }
//     });
//     // console.log(paths_taken);
//     if (paths_taken.length >= 0) {
//       document.querySelectorAll('[data-branch-path]').forEach(elem => {
//         if (paths_taken.includes(elem.dataset.branchPath)) {
//           elem.classList.remove("not-taken");
//         } else {
//           elem.classList.add("not-taken");
//         }
//       });
//     } else {
//       document.querySelectorAll('[data-branch-path]').forEach(elem => {
//         elem.classList.remove("not-taken");
//       });
//     }
//   }
// }

// // Attach event handlers on load.
// window.addEventListener('DOMContentLoaded', () => {

//   document.querySelectorAll('[data-frame-n]').forEach(elem => {
//     elem.addEventListener("mouseover", e => set_frame_n(e.currentTarget.dataset.frameN));
//   });

//   document.querySelectorAll('[data-failure-in-frame-n]').forEach(elem => {
//     elem.addEventListener("click", e => set_frame_n(e.currentTarget.dataset.failureInFrameN));
//   });

//   show_current_frame_values();
// });






/////////////////// Deletion ///////////////////

// function toggleSelect(event) {
//   if (event.currentTarget.classList.contains("selected")) {
//     event.currentTarget.classList.remove("selected");
//   } else {
//     document.querySelectorAll('.selected').forEach(elem => {
//       elem.classList.remove("selected");
//     });
//     event.currentTarget.classList.add("selected");
//   }
//   event.stopPropagation();
// }

// // Attach event handlers on load.
// window.addEventListener('DOMContentLoaded', () => {
//   document.querySelectorAll('[data-expr-id-str]').forEach(elem => {
//     elem.addEventListener("click", toggleSelect);
//   });
// });

// document.addEventListener("keydown", function(event) {
//   if (event.key === "Backspace" || event.key === "Delete") {
//     let elem = document.querySelector('[data-expr-id-str].selected')
//     if (elem) {
//       deleteExpr(elem.dataset.exprIdStr);
//       event.stopPropagation();
//     }
//   }
// });




/////////////////// Set Example ///////////////////

// window.addEventListener('DOMContentLoaded', () => {
//   let form = document.getElementById('set-example-form');

//   form.addEventListener("submit", (event) => {
//     console.log("Set example.");
//     let fd = new FormData(event.target);
//     setExample(
//       fd.get("func"),
//       fd.get("arg1"),
//       fd.get("arg2"),
//       fd.get("arg3"),
//     );
//     event.preventDefault();
//     event.stopPropagation();
//   });
// });
