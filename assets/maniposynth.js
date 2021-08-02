Array.prototype.addAsSet = function(elem) { // pretend array is a set and add something to it
  if (!this.includes(elem)) {
    this.push(elem);
  }
  // console.log(this);
  return this;
};

Array.prototype.removeAsSet = function(elem) {
  // https://love2dev.com/blog/javascript-remove-from-array/#remove-from-array-splice-value
  for (var i = 0; i < this.length; i += 1) {
    if (this[i] === elem) {
      this.splice(i, 1);
      i -= 1;
    }
  }
  // console.log(this);
  return this;
};

function doAction(action) {
  let request = new XMLHttpRequest();
  request.open("PATCH", document.location.href);
  request.setRequestHeader("Content-type", "application/json");
  request.addEventListener("loadend", () => document.location.reload() );
  request.send(JSON.stringify(action));
}

function moveValue(vbId, vtrace) {
  doAction([
    "MoveValue",
    vbId,
    vtrace
  ]);
}

function addVis(loc, vis) {
  doAction([
    "AddVis",
    loc,
    vis
  ]);
}

function removeVis(loc, vis) {
  doAction([
    "RemoveVis",
    loc,
    vis
  ]);
}

function editLoc(loc, code) {
  doAction([
    "EditLoc",
    loc,
    code
  ]);
}

function newAssert(locToAssertBefore, codeToAssertOn, expectedCode) {
  doAction([
    "NewAssert",
    locToAssertBefore,
    codeToAssertOn,
    expectedCode
  ]);
}

function doSynth() {
  doAction([
    "DoSynth"
  ]);
}

function undo() {
  doAction([
    "Undo"
  ]);
}

function redo() {
  doAction([
    "Redo"
  ]);
}

function insertCode(code) {
  doAction([
    "InsertCode",
    code
  ]);
}

function setPos(loc, x, y) {
  doAction([
    "SetPos",
    loc,
    x,
    y
  ]);
}

function moveVb(vbs_loc, mobile_loc, new_pos) {
  let new_pos_opt = ["None"];
  if (new_pos) { new_pos_opt = ["Some", new_pos.x, new_pos.y] }
  doAction([
    "MoveVb",
    vbs_loc,
    mobile_loc,
    new_pos_opt
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

//////////////// Drag and Drop of (Sub)Values /////////////////////////////////

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
  if (node.dataset.vtrace) { event.dataTransfer.setData("application/vtrace", node.dataset.vtrace); }
  // if (node.dataset.newCode)         { event.dataTransfer.setData("application/new-code", node.dataset.newCode); }
  // if (node.dataset.destructPathStr) { event.dataTransfer.setData("application/destruct-path-str", node.dataset.destructPathStr); }
}

function removeDropTargetStyles() {
  document.querySelectorAll('.current-drop-target').forEach(unhighlightDropTarget);
}

function highlightDropTarget(elem) {
  elem.classList.add("current-drop-target");
}

function unhighlightDropTarget(elem) {
  elem.classList.remove("current-drop-target");
}

function dragend(event) {
  removeDropTargetStyles()
}

function dragover(event) {
  // Ignore child elements of the drop target.
  if (event.target === event.currentTarget) {
    event.preventDefault();
    event.dataTransfer.dropEffect = "copy";
    highlightDropTarget(event.currentTarget);
  }
}

function dragleave(event) {
  event.currentTarget.classList.remove("current-drop-target");
}

function drop(event) {
  event.preventDefault();
  let dropTarget      = event.currentTarget;
  let droppedVTrace   = event.dataTransfer.getData("application/vtrace");
  // if (dropTarget.dataset.beforeVbId && droppedVTrace) {
  //   moveValue(dropTarget.dataset.beforeVbId, droppedVTrace);
  // } else {
  //   console.warn("No valid actions for drop on ", dropTarget);
  // }
}

window.addEventListener('DOMContentLoaded', () => {

  // Make appropriate items draggable.
  document.querySelectorAll('[data-vtrace]').forEach(elem => {
    // console.log(elem);
    elem.addEventListener("dragstart", dragstart);
    elem.addEventListener("dragend", dragend);
    elem.addEventListener("mouseover", draggableHover);
    elem.addEventListener("mouseout", draggableUnhover);
  });

  // Add drop zone events.
  // document.querySelectorAll('[data-before-vb-id],[data-before-scope-id]').forEach(elem => {
  //   elem.addEventListener("dragover", dragover);
  //   elem.addEventListener("dragleave", dragleave);
  //   elem.addEventListener("drop", drop);
  // });
});


//////////////// Selection /////////////////////////////////

function select(elem) {
  elem.classList.add("selected");
  saveSelection();
  updateInspector();
}

function deselect(elem) {
  elem.classList.remove("selected");
  saveSelection();
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

// Attempt to preserve selections over page reloads.
//
// Referencing by item number on page.
function saveSelection() {
  const selectedIndices = [];

  var i = 0
  document.querySelectorAll('.selectable').forEach(elem => {
    if (elem.classList.contains("selected")) {
      selectedIndices.push(i);
    }
    i++;
  });

  window.sessionStorage.setItem("selectedIndices", JSON.stringify(selectedIndices));
}

function restoreSelection() {
  // document.querySelectorAll('.selectable').length
  const selectedIndices = JSON.parse(window.sessionStorage.getItem("selectedIndices") || "[]");

  deselectAll();
  var i = 0
  document.querySelectorAll('.selectable').forEach(elem => {
    if (selectedIndices.includes(i)) {
      select(elem);
    }
    i++;
  });
}


window.addEventListener('DOMContentLoaded', () => {

  // Make appropriate items selectable.
  document.querySelectorAll('[data-vtrace]').forEach(elem => {
    elem.classList.add("selectable");
    elem.addEventListener("click", toggleSelect);
  });

  restoreSelection();
});


/////////////////// Inspector ///////////////////

// Visualizers root, also for determining where to place new asserts.
function containingLoc(elem) {
  return elem.closest("[data-loc]").dataset.loc;
}

window.addEventListener('DOMContentLoaded', () => {
  window.inspector = document.getElementById("inspector");

  document.getElementById("add-vis-textbox").addEventListener("keydown", event => {
    let textbox = event.currentTarget;
    if (event.key === "Enter" && textbox.value) {
      const elem = document.querySelector('.selected');
      if (elem) {
        const vis = textbox.value;
        addVis(containingLoc(elem), vis);
      }
    } else if (event.key === "Escape") {
      textbox.value = "";
    }
  });

  updateInspector();
});


function updateInspector() {
  const inspector        = window.inspector;
  const typeOfSelected   = document.getElementById("type-of-selected");
  const visesForSelected = document.getElementById("vises-for-selected");
  const addVisTextbox    = document.getElementById("add-vis-textbox");

  const elem = document.querySelector('.selected');

  const makeCheck = (vis, isChecked) => {
    const label = document.createElement("label");
    const checkbox = document.createElement("input");
    checkbox.type = "checkbox";
    checkbox.checked = isChecked;
    label.appendChild(checkbox);
    label.appendChild(document.createTextNode(vis));

    checkbox.addEventListener("change", ev => {
      const checkbox = ev.target;
      const loc = containingLoc(elem);
      if (checkbox.checked) {
        addVis(loc, vis);
      } else {
        removeVis(loc, vis);
      }
    });
    return label;
  }

  if (elem) {
    show(inspector);
    const typeStr = elem.dataset.type || "Unknown";
    typeOfSelected.innerHTML = "";
    visesForSelected.innerHTML = "";
    typeOfSelected.appendChild(document.createTextNode(typeStr));
    const activeVises   = (elem.dataset.activeVises || "").split("  ").removeAsSet("");
    const possibleVises = (elem.dataset.possibleVises || "").split("  ").removeAsSet("");
    activeVises.forEach(vis => visesForSelected.appendChild(makeCheck(vis, true)));
    possibleVises.forEach(vis => {
      if (!activeVises.includes(vis)) {
        visesForSelected.appendChild(makeCheck(vis, false));
      }
    });
  } else {
    hide(inspector);
  }
}


/////////////////// Text Editing ///////////////////

function hide(originalElem) {
  originalElem.classList.add("hidden");
}

function show(originalElem) {
  originalElem.classList.remove("hidden");
}

function beginEditCallback(editType) {
  return function (event) {
    const originalElem = event.currentTarget;
    // const parent = originalElem.parentElement;
    console.log(originalElem);
    const input = document.createElement("input");
    input.type = "text";
    input.value = originalElem.innerText;
    // originalElem.appendChild(input);
    originalElem.insertAdjacentElement("afterend", input);
    hide(originalElem);
    // input.focus();
    input.select();

    input.addEventListener('keyup', event => {
      console.log(event.key);
      if (event.key === "Enter") {
        if (editType === "in-place") {
          editLoc(originalElem.dataset.inPlaceEditLoc, input.value);
        } else if (editType === "new assert") {
          newAssert(containingLoc(originalElem), originalElem.dataset.codeToAssertOn, input.value);
        } else {
          console.warn("Unknown edit type " + editType)
        }
      } else if (event.key === "Esc" || event.key === "Escape") {
        input.remove();
        show(originalElem);
      }
    });
  }
}

window.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll('[data-in-place-edit-loc]').forEach(elem => {
    elem.addEventListener("dblclick", beginEditCallback("in-place"));
  });

  document.querySelectorAll('[data-code-to-assert-on]').forEach(elem => {
    elem.addEventListener("dblclick", beginEditCallback("new assert"));
  });
});



/////////////////// Synth Button ///////////////////

window.addEventListener('DOMContentLoaded', () => {
  document.getElementById("synth-button").addEventListener("click", _ => doSynth());
});



/////////////////// Undo/Redo ///////////////////

window.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll(".undo").forEach(elem => elem.addEventListener("click", _ => undo()));
  document.querySelectorAll(".redo").forEach(elem => elem.addEventListener("click", _ => redo()));

  document.addEventListener('keydown', event => {
    if (event.metaKey && event.shiftKey && event.key === 'z') {
      redo();
      event.preventDefault();
    } else if (event.metaKey && event.key === 'z') {
      undo();
      event.preventDefault();
    }
  });
});


/////////////////// Topbar Tools ///////////////////

window.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll("[data-insert-code]").forEach(elem => {
    elem.addEventListener("click", _ => {
      insertCode(elem.dataset.insertCode);
    });
  });
});



/////////////////// Moving Boxes ///////////////////

function isStartingVbs(vbsElem, boxElem) {
  // console.log(Array.from(vbsElem.children), boxElem);
  return Array.from(vbsElem.children).includes(boxElem);
}
function topLeftOffsetFromMouse(elem, event) {
  const rect = elem.getBoundingClientRect();
  return { dx: rect.left - event.clientX, dy: rect.top - event.clientY }
}
function vbDropTarget(event) {
  const descendentVbs = Array.from(window.stuffMoving.elem.querySelectorAll(".vbs"));
  const dropTarget = Array.from(document.querySelectorAll(".vbs")).reverse().find(elem => {
    const rect = elem.getBoundingClientRect();
    // console.log(rect.bottom, event.clientX, event.clientY)
    // console.log(event.clientX >= rect.left, event.clientX <= rect.right, event.clientY >= rect.top, event.clientY <= rect.bottom)
    const isDescendentVbs = descendentVbs.includes(elem);
    return !isDescendentVbs && event.clientX >= rect.left && event.clientX <= rect.right && event.clientY >= rect.top && event.clientY <= rect.bottom;
  });
  if (isStartingVbs(dropTarget, window.stuffMoving.elem)) {
    return undefined;
  } else {
    return dropTarget;
  }
}

window.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll(".box").forEach(elem => {
    elem.addEventListener("mousedown", event => {
      window.stuffMoving = {
        startX          : event.pageX,
        startY          : event.pageY,
        startOffsetX    : elem.offsetLeft,
        startOffsetY    : elem.offsetTop,
        offsetFromMouse : topLeftOffsetFromMouse(elem, event),
        elem            : elem,
      }
      event.stopPropagation();
    });
  });
});


window.addEventListener('DOMContentLoaded', () => {

  document.querySelectorAll(".top_level").forEach(elem => {
    elem.addEventListener("mousemove", event => {
      if (window.stuffMoving) {
        const dx = event.pageX - stuffMoving.startX;
        const dy = event.pageY - stuffMoving.startY;
        window.stuffMoving.elem.style.left = `${stuffMoving.startOffsetX + dx}px`
        window.stuffMoving.elem.style.top  = `${stuffMoving.startOffsetY + dy}px`
        window.stuffMoving.elem.style.zIndex = 1;
        // resizeVbHolders(document);

        removeDropTargetStyles();
        const dropTarget = vbDropTarget(event)
        if (dropTarget) { highlightDropTarget(dropTarget) }
      }

    });

    elem.addEventListener("mouseup", event => {
      if (window.stuffMoving) {
        const dx = event.pageX - stuffMoving.startX;
        const dy = event.pageY - stuffMoving.startY;
        const elem = stuffMoving.elem;
        const dropTarget = vbDropTarget(event)
        if ((dx !== 0 || dy !== 0) && !dropTarget) {
          const x = dx + stuffMoving.startOffsetX;
          const y = dy + stuffMoving.startOffsetY;
          setPos(elem.dataset.loc, x, y);
        } else if (dropTarget) {
          const dropTargetOffsetFromMouse = topLeftOffsetFromMouse(dropTarget, event);
          const x = stuffMoving.offsetFromMouse.dx - dropTargetOffsetFromMouse.dx;
          const y = stuffMoving.offsetFromMouse.dy - dropTargetOffsetFromMouse.dy;
          moveVb(dropTarget.dataset.loc, elem.dataset.loc, { x : x, y : y });
        } else {
          elem.style.zIndex = "auto";
        }
        window.stuffMoving = undefined;
        removeDropTargetStyles();
      }
    });
  });
});

// Make sure each vbs holder has place for all the vbs
// Resize deepest first.
function resizeVbHolders(elem) {
  const vbsHolders = elem.querySelectorAll(".vbs");
  vbsHolders.forEach(vbsHolder => {
    // console.log(vbsHolder.children);
    let maxWidth = 0;
    let maxHeight = 0;
    for (box of vbsHolder.children) {
      resizeVbHolders(box);
      maxWidth  = Math.max(maxWidth, box.offsetLeft + box.offsetWidth);
      maxHeight = Math.max(maxHeight, box.offsetTop + box.offsetHeight);
    }
    if (vbsHolder.tagName === "TD") {
      vbsHolder.style.width  = `${maxWidth + 10}px`
      vbsHolder.style.height = `${maxHeight + 10}px`
    } else {
      vbsHolder.style.minWidth  = `${maxHeight + 10}px`
      vbsHolder.style.minHeight = `${maxHeight + 10}px`
    }
  });
};
function reflowUnpositionedElems(elem) {
  const vbsHolders = elem.querySelectorAll(".vbs");
  function left(box)  { return box.offsetLeft; }
  function top(box)   { return box.offsetTop; }
  function right(box) { return box.offsetLeft + box.offsetWidth; }
  function bot(box)   { return box.offsetTop + box.offsetHeight; }
  function areOverlapping(box1, box2) {
    // console.log(left(box1), top(box1), right(box1), bot(box1), left(box2), top(box2), right(box2), bot(box2),)
    if (right(box1) < left(box2) || right(box2) < left(box1)) { return false; }
    if (bot(box1)   < top(box2)  || bot(box2)   < top(box1))  { return false; }
    return true;
  }
  vbsHolders.forEach(vbsHolder => {
    const boxes = Array.from(vbsHolder.children);
    const placedBoxes = boxes.filter(box => box.style.left); /* If box has an explicit position */
    for (box of vbsHolder.children) {
      if (!box.classList.contains("value_binding")) {
        console.log("expected only value bindings in a .vbs", box);
        continue;
      }
      if (!placedBoxes.includes(box)) {
        box.style.left = `10px`
        let top = 0;
        box.style.top = `${top}px`
        while (placedBoxes.find(box2 => areOverlapping(box, box2))) {
          top += 10
          // console.log(top);
          box.style.top = `${top}px`
        }
        box.style.top = `${top + 10}px`
        placedBoxes.push(box)
      }
    }
  });
}
window.addEventListener('DOMContentLoaded', () => {
  resizeVbHolders(document);
  reflowUnpositionedElems(document);
  resizeVbHolders(document);
  reflowUnpositionedElems(document);
  resizeVbHolders(document);
  reflowUnpositionedElems(document);
  resizeVbHolders(document);
  reflowUnpositionedElems(document);
  resizeVbHolders(document);
});



/////////////////// Frame Number Handling ///////////////////


// The below code is wonkey because nested fun exps are not nested in the HTML, but instead are
// sibling rows (so that arguments line up in the display).
//
// So there's a bit of finagling to "find the first fun-exp" on which to place the frame number,
// and then to find is "children" (actually, later siblings and their children) to propogate
// the styling.

function findFrameNoElem(elem) {
  // console.log(elem)
  if ("activeFrameNo" in elem.dataset) {
    return elem;
  } else if (elem.parentElement) {
    let firstFunSibling = Array.from(elem.parentElement.children).find(elem => elem.classList.contains("fun"));
    if (firstFunSibling) {
      return firstFunSibling
    } else {
      return findFrameNoElem(elem.parentElement);
    }
  } else {
    return undefined
  }
}

function setFrameNo(frameRootElem, frameNo) {
  frameRootElem.dataset.activeFrameNo = frameNo;
  for (child of frameRootElem.children) { updateActiveValues(child, frameNo) }
  const siblings = Array.from(frameRootElem.parentElement.children);
  while (siblings[0] !== frameRootElem) { siblings.shift() }
  siblings.shift()
  const laterSiblings = siblings;
  for (sibling of laterSiblings) { updateActiveValues(sibling, frameNo) }
}

function updateActiveValues(elem, frameNo) {
  if ("frameNo" in elem.dataset) {
    if (parseInt(elem.dataset.frameNo) === parseInt(frameNo)) {
      elem.classList.remove("not-in-active-frame");
    } else {
      elem.classList.add("not-in-active-frame");
    }
  } else if (Array.from(elem.children).find(child => child.classList.contains("fun"))) {
    // Stop recursing, new set of nested lambdas
  } else {
    for (child of elem.children) { updateActiveValues(child, frameNo) }
  }
}

window.addEventListener('DOMContentLoaded', () => {
  // Set an initial frame-no
  // document.querySelectorAll("tr.fun").forEach(elem => {
  //   if (elem.activeFrameNo === undefined) {

  //   }
  // });

  document.querySelectorAll("[data-frame-no]").forEach(elem => {
    elem.addEventListener("mouseenter", event => {
      const frameNoElem = findFrameNoElem(elem);
      // console.log(frameNoElem, elem.dataset.frameNo);
      if (frameNoElem) { setFrameNo(frameNoElem, elem.dataset.frameNo) }
    });
  })
});


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
