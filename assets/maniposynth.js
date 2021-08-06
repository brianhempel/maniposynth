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

function doAction(action, reload) {
  if (reload === undefined) { reload = true };
  let request = new XMLHttpRequest();
  request.open("PATCH", document.location.href);
  request.setRequestHeader("Content-type", "application/json");
  request.addEventListener("loadend", () => { reload && document.location.reload() });
  request.send(JSON.stringify(action));
}

function dropValueIntoVbs(loc, vtrace) {
  doAction([
    "DropValueIntoVbs",
    loc,
    vtrace
  ]);
}

function dropValueIntoExp(loc, vtrace) {
  doAction([
    "DropValueIntoExp",
    loc,
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

function deleteLoc(loc) {
  doAction([
    "DeleteLoc",
    loc
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
  ], false);
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
  event.stopImmediatePropagation();
}

function draggableUnhover(event) {
  event.currentTarget.classList.remove("draggable-hovered");
}

// When drag starts, store information.
function dragstart(event) {
  let node = event.currentTarget;
  if (node.dataset.vtrace) { event.dataTransfer.setData("application/vtrace", node.dataset.vtrace); }
  // if (node.dataset.newCode)         { event.dataTransfer.setData("application/new-code", node.dataset.newCode); }
  // if (node.dataset.destructPathStr) { event.dataTransfer.setData("application/destruct-path-str", node.dataset.destructPathStr); }
  event.stopImmediatePropagation();
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
  event.stopImmediatePropagation();
}

function dragover(event) {
  // Ignore child elements of the drop target.
  if (event.target === event.currentTarget) {
    event.preventDefault();
    event.dataTransfer.dropEffect = "copy";
    highlightDropTarget(event.currentTarget);
  }
  event.stopImmediatePropagation();
}

function dragleave(event) {
  event.currentTarget.classList.remove("current-drop-target");
  event.stopImmediatePropagation();
}

function drop(event) {
  event.preventDefault();
  let dropTarget      = event.currentTarget;
  let droppedVTrace   = event.dataTransfer.getData("application/vtrace");
  console.log(dropTarget, droppedVTrace);
  if (dropTarget.classList.contains("vbs") && droppedVTrace) {
    dropValueIntoVbs(dropTarget.dataset.loc, droppedVTrace);
  } else if (dropTarget.classList.contains("exp") && droppedVTrace) {
    dropValueIntoExp(dropTarget.dataset.inPlaceEditLoc, droppedVTrace);
  } else {
    console.warn("No valid actions for drop on ", dropTarget);
  }
  event.stopImmediatePropagation();
}

window.addEventListener('DOMContentLoaded', () => {

  // Make appropriate items draggable.
  document.querySelectorAll('[data-vtrace]').forEach(elem => {
    // console.log(elem);
    elem.draggable = true;
    elem.addEventListener("dragstart", dragstart);
    elem.addEventListener("dragend", dragend);
    elem.addEventListener("mouseover", draggableHover);
    elem.addEventListener("mouseout", draggableUnhover);
  });

  // Add drop zone events.
  document.querySelectorAll('.vbs,.exp[data-in-place-edit-loc]').forEach(elem => {
    elem.addEventListener("dragover", dragover);
    elem.addEventListener("dragleave", dragleave);
    elem.addEventListener("drop", drop);
  });
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
  const elem = event.currentTarget;
  event.stopImmediatePropagation();
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

  function globalEscape() {
    const transientTextboxes = document.querySelectorAll(".transient-textbox");
    if (transientTextboxes.length > 0) {
      transientTextboxes.forEach(abortTextEdit);
    } else {
      deselectAll();
    }
  }

  document.querySelectorAll('.top-level, .top-level *').forEach(elem => {
    elem.addEventListener("click", globalEscape);
  });
  // Make appropriate items selectable.
  document.querySelectorAll('[data-vtrace],.vb,.exp').forEach(elem => {
    elem.classList.add("selectable");
    elem.addEventListener("click", toggleSelect);
  });
  document.addEventListener("keydown", event => {
    if (event.key === "Esc" || event.key === "Escape") {
      globalEscape();
      event.stopImmediatePropagation();
    }
  });

  restoreSelection();
});


/////////////////// Suggestions ///////////////////

// The Inspector code later also displays suggestions.

function elemSuggestions(elem) {
  return elem.dataset.suggestions?.split("  ") || [];
}

function useSuggestionNumber(elem, i) {
  editLoc(elem.dataset.inPlaceEditLoc, elemSuggestions(elem)[i-1]);
}

window.addEventListener('DOMContentLoaded', () => {
  document.addEventListener("keydown", event => {
    const elem = document.querySelector('.selected[data-suggestions]');
    if (elem) {
      const suggestions = elemSuggestions(elem);
      const i = parseInt(event.key);
      if (!isNaN(i) && i >= 1 && i <= suggestions.length) {
        useSuggestionNumber(elem, i);
        event.stopImmediatePropagation();
      }
    }
  });
});


/////////////////// Inspector ///////////////////

// Visualizers root, also for determining where to place asserts.
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
    } else if (event.key === "Esc" || event.key === "Escape") {
      textbox.value = "";
      textbox.blur();
      // document.querySelector(".top-level").focus(); // I don't think this works :/
    }
    event.stopImmediatePropagation();
  });

  updateInspector();
});


function updateInspector() {
  const inspector              = window.inspector;
  const typeOfSelected         = document.getElementById("type-of-selected");
  const visesForSelected       = document.getElementById("vises-for-selected");
  const suggestionsForSelected = document.getElementById("suggestions-for-selected");
  const visPane                = document.getElementById("vis-pane");
  const suggestionsPane        = document.getElementById("suggestions-pane");
  // const addVisTextbox    = document.getElementById("add-vis-textbox");

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
    suggestionsForSelected.innerHTML = "";
    visesForSelected.innerHTML = "";
    typeOfSelected.appendChild(document.createTextNode(typeStr));
    const suggestions = elemSuggestions(elem);
    if (suggestions.length > 0) {
      show(suggestionsPane);
      let i = 1;
      suggestions.forEach(code => {
        const suggestion = document.createElement("button");
        suggestion.classList.add("suggestion");
        suggestion.innerHTML = `${i}. ${code}`;
        suggestion.addEventListener("click", _ => { useSuggestionNumber(elem, i) });
        suggestionsForSelected.appendChild(suggestion);
      });
    } else {
      hide(suggestionsPane);
    }
    if ("possibleVises" in elem.dataset) { // If the item can have vises (i.e. is a value)
      show(visPane);
      const activeVises   = (elem.dataset.activeVises || "").split("  ").removeAsSet("");
      const possibleVises = (elem.dataset.possibleVises || "").split("  ").removeAsSet("");
      activeVises.forEach(vis => visesForSelected.appendChild(makeCheck(vis, true)));
      possibleVises.forEach(vis => {
        if (!activeVises.includes(vis)) {
          visesForSelected.appendChild(makeCheck(vis, false));
        }
      });
    } else {
      hide(visPane);
    }
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

function abortTextEdit(textbox) {
  if (textbox.originalElem) { show(textbox.originalElem) };
  textbox.remove();
}

function beginEditCallback(editType) {
  return function (event) {
    event.stopImmediatePropagation();
    const originalElem = event.currentTarget;
    // const parent = originalElem.parentElement;
    console.log(originalElem);
    const input = document.createElement("input");
    input.type = "text";
    input.value = originalElem.innerText;
    input.classList.add("transient-textbox");
    input.originalElem = originalElem;
    // originalElem.appendChild(input);
    originalElem.insertAdjacentElement("afterend", input);
    hide(originalElem);
    // input.focus();
    input.select();

    input.addEventListener('keydown', event => {
      // console.log(event.key);
      if (event.key === "Enter") {
        if (editType === "in-place") {
          if (input.value.length > 0) {
            editLoc(originalElem.dataset.inPlaceEditLoc, input.value);
          } else {
            deleteLoc(originalElem.dataset.inPlaceEditLoc);
          }
        } else if (editType === "new assert") {
          if (input.value.length > 0) {
            newAssert(containingLoc(originalElem), originalElem.dataset.codeToAssertOn, input.value);
          }
        } else {
          console.warn("Unknown edit type " + editType)
        }
      } else if (event.key === "Esc" || event.key === "Escape") {
        abortTextEdit(input);
      }
      event.stopImmediatePropagation();
    });
  }
}

function beginNewCodeEdit(vbs_holder) {
  return function (event) {
    if (event.target !== vbs_holder) { return; }
    event.stopImmediatePropagation();
    const input = document.createElement("input");
    input.type = "text";
    input.classList.add("transient-textbox");
    input.style.position = "absolute";
    const { dx, dy } = topLeftOffsetFromMouse(vbs_holder, event)
    input.style.left = `${-dx - 5}px`;
    input.style.top  = `${-dy - 10}px`;
    vbs_holder.appendChild(input);
    input.select();

    input.addEventListener('keydown', event => {
      // console.log(event.key);
      if (event.key === "Enter") {
        if (input.value.length > 0) { insertCode(input.value); }
      } else if (event.key === "Esc" || event.key === "Escape") {
        abortTextEdit(input);
      }
      event.stopImmediatePropagation();
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

  document.querySelectorAll('.vbs').forEach(elem => {
    elem.addEventListener("dblclick", beginNewCodeEdit(elem));
  });
});



/////////////////// Synth Button ///////////////////

window.addEventListener('DOMContentLoaded', () => {
  document.getElementById("synth-button").addEventListener("click", event => { gratuitousLamdas(event); doSynth() });
});

function gratuitousLamdas(event) {
  const particleLife  = 5  * 1000;
  const generatorLife = 15 * 1000;
  const generatorStart = new Date();
  let synthTimeout = false;
  function makeLambda() {
    if (new Date() - generatorStart > generatorLife) { synthTimeout = true; return; }
    const particleStart = new Date();
    const particle = document.createElement("div");
    particle.classList.add("gratuitous-lambda");
    particle.style.color = `rgb(${Math.floor(256*Math.random())},${Math.floor(256*Math.random())},${Math.floor(256*Math.random())})`;
    particle.innerText = "λ";
    const vx = 20 * (Math.random() - 0.5) * 60;
    let   vy = 20 * -Math.random() * 60;
    const vr = 20 * (Math.random() - 0.5) * 60;
    const g = 0.1 * 60 * 60;
    let x = event.clientX - 10;
    let y = event.clientY - 20;
    let r = 360 * Math.random();
    let lastTime = new Date();
    const moveParticle = _ => {
      const t = new Date();
      if (t - particleStart > particleLife) { particle.remove(); return; }
      particle.style.transform = `translate(${x}px, ${y}px) rotate(${r}deg)`
      if (synthTimeout) { particle.innerText = "😞" }
      const dt = (t - lastTime) * 0.001;
      lastTime = t;
      x += vx * dt;
      y += vy * dt;
      r += vr * dt;
      vy += g * dt;
      requestAnimationFrame(moveParticle);
    };
    moveParticle();
    document.body.appendChild(particle);
    requestAnimationFrame(makeLambda);
  }
  makeLambda();
}

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
      if (event.target === elem) {
        window.stuffMoving = {
          startX          : event.pageX,
          startY          : event.pageY,
          startOffsetX    : elem.offsetLeft,
          startOffsetY    : elem.offsetTop,
          offsetFromMouse : topLeftOffsetFromMouse(elem, event),
          elem            : elem,
        }
        event.stopImmediatePropagation();
      }
    });
  });
});


window.addEventListener('DOMContentLoaded', () => {

  document.querySelectorAll(".top-level").forEach(elem => {
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
      vbsHolder.style.minWidth  = `${maxWidth + 10}px`
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
      if (!box.classList.contains("vb")) {
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


function findFrameNoElem(elem) {
  return elem.closest(".fun");
}

function setFrameNo(frameRootElem, frameNo) {
  frameRootElem.dataset.activeFrameNo = frameNo;
  for (child of frameRootElem.children) { updateActiveValues(child, frameNo) }
}

function updateActiveValues(elem, frameNo) {
  if (elem.classList.contains("fun")) {
    // Stop recursing, new set of nested lambdas
  } else if ("frameNo" in elem.dataset) {
    if (parseInt(elem.dataset.frameNo) === parseInt(frameNo)) {
      elem.classList.remove("not-in-active-frame");
    } else {
      elem.classList.add("not-in-active-frame");
    }
  } else {
    for (child of elem.children) { updateActiveValues(child, frameNo) }
  }
}

window.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll("[data-frame-no]").forEach(elem => {
    elem.addEventListener("mouseenter", event => {
      const frameNoElem = findFrameNoElem(elem);
      if (frameNoElem) { setFrameNo(frameNoElem, elem.dataset.frameNo) }
    });
  })
});



/////////////////// Deletion ///////////////////

document.addEventListener("keydown", function(event) {
  if (event.key === "Backspace" || event.key === "Delete") {
    const elem = document.querySelector('.vb.selected,.exp.selected')
    if (elem) {
      deleteLoc(elem.dataset.loc || elem.dataset.inPlaceEditLoc);
      event.stopImmediatePropagation();
    }
  }
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
