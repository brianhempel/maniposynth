
// Keep track of event listeners so we can remove them
// Based on Ivan Castellanos & alex, https://stackoverflow.com/a/6434924
Element.prototype.origAddEventListener = Element.prototype.addEventListener;
Element.prototype.addEventListener = function (eventName, f, opts) {
  this.origAddEventListener(eventName, f, opts);
  this.listeners = this.listeners || [];
  this.listeners.push({ eventName: eventName, f: f , opts: opts });
};
Element.prototype.removeEventListeners = function () {
  for (const { eventName, f, opts } of (this.listeners || [])) {
    this.removeEventListener(eventName, f, opts)
  }
  this.listeners = [];
};

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

Array.prototype.dedup = function () {
  // https://stackoverflow.com/a/9229821
  return this.filter((item, pos) => this.indexOf(item) == pos );
}

function doAction(action, reload) {
  if (reload === undefined) { reload = true };
  let request = new XMLHttpRequest();
  request.open("PATCH", document.location.href);
  request.setRequestHeader("Content-type", "application/json");
  request.addEventListener("loadend", () => { reload && request.status === 200 && document.location.reload() });
  request.send(JSON.stringify(action));
}

// function dropValueIntoVbs(loc, vtrace) {
//   doAction([
//     "DropValueIntoVbs",
//     loc,
//     vtrace
//   ]);
// }

// function dropValueIntoExp(loc, vtrace) {
//   doAction([
//     "DropValueIntoExp",
//     loc,
//     vtrace
//   ]);
// }

function addVis(loc, vis) {
  if ("" + vis === "undefined") { console.error("removeVis(): undefined vis"); return; };
  doAction([
    "AddVis",
    loc,
    vis
  ]);
}

function removeVis(loc, vis) {
  if ("" + vis === "undefined") { console.error("removeVis(): undefined vis"); return; };
  doAction([
    "RemoveVis",
    loc,
    vis
  ]);
}

function replaceLoc(loc, code) {
  if ("" + code === "undefined") { console.error("replaceLoc(): undefined code"); return; };
  doAction([
    "ReplaceLoc",
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

function insertCode(loc, code, pos) {
  if ("" + code === "undefined") { console.error("insertCode(): undefined code"); return; };
  let posOpt = ["None"];
  if (pos) { posOpt = ["Some", pos.x, pos.y] }
  doAction([
    "InsertCode",
    loc,
    code,
    posOpt
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

function moveVb(vbsLoc, mobileLoc, newPos) {
  let newPosOpt = ["None"];
  if (newPos) { newPosOpt = ["Some", newPos.x, newPos.y] }
  doAction([
    "MoveVb",
    vbsLoc,
    mobileLoc,
    newPosOpt
  ]);
}

function setRecFlag(vbLoc, isRec) {
  doAction([
    "SetRecFlag",
    vbLoc,
    isRec
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
  // if (node.dataset.vtrace) { event.dataTransfer.setData("application/vtrace", node.dataset.vtrace); }
  if (node.dataset.extractionCode) { event.dataTransfer.setData("application/extractionCode", node.dataset.extractionCode); }
  event.dataTransfer.setData("application/toolKey", getMainToolElem(node)?.dataset?.toolKey);
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
  // let droppedVTrace   = event.dataTransfer.getData("application/vtrace");
  let droppedExtractionCode = event.dataTransfer.getData("application/extractionCode");
  if (droppedExtractionCode === dropTarget.dataset.extractionCode) { // Don't allow drop onto self
    event.stopImmediatePropagation();
    return;
  }
  // console.log(dropTarget, droppedVTrace);
  // if (dropTarget.classList.contains("vbs") && droppedVTrace) {
  //   dropValueIntoVbs(dropTarget.dataset.loc, droppedVTrace);
  // } else if (dropTarget.classList.contains("exp") && droppedVTrace) {
  //   dropValueIntoExp(dropTarget.dataset.inPlaceEditLoc, droppedVTrace);
  const toolKey = event.dataTransfer.getData("application/toolKey");
  const mainToolElem = toolKey && Array.from(document.querySelectorAll("[data-tool-key]")).find(elem => elem.dataset.toolKey === toolKey);
  if (dropTarget.classList.contains("vbs") && droppedExtractionCode) {
    setMainTool(droppedExtractionCode, mainToolElem);
    insertCode(dropTarget.dataset.loc, droppedExtractionCode, mouseReletiveToElem(dropTarget, event));
  } else if (dropTarget.dataset.inPlaceEditLoc && droppedExtractionCode) {
    setMainTool(droppedExtractionCode, mainToolElem);
    replaceLoc(dropTarget.dataset.inPlaceEditLoc, droppedExtractionCode);
  } else {
    console.warn("No valid actions for drop on ", dropTarget);
  }
  event.stopImmediatePropagation();
}

window.addEventListener('DOMContentLoaded', () => {

  // Make appropriate items draggable.
  // document.querySelectorAll('[data-vtrace]').forEach(elem => {
  document.querySelectorAll('[data-extraction-code]').forEach(elem => {
    // console.log(elem);
    elem.draggable = true;
    elem.addEventListener("dragstart", dragstart);
    elem.addEventListener("dragend", dragend);
    elem.addEventListener("mouseover", draggableHover);
    elem.addEventListener("mouseout", draggableUnhover);
  });

  // Add drop zone events.
  document.querySelectorAll('.vbs,.exp[data-in-place-edit-loc],.value[data-in-place-edit-loc]').forEach(elem => {
    elem.addEventListener("dragover", dragover);
    elem.addEventListener("dragleave", dragleave);
    elem.addEventListener("drop", drop);
  });
});


//////////////// Selection /////////////////////////////////

function selectedElems() {
  return document.querySelectorAll('.selected');
}

function select(elem) {
  elem.classList.add("selected");
  saveSelection();
  updateInspector();
  // selectInspectorTextbox();
}

function deselect(elem) {
  elem.classList.remove("selected");
  saveSelection();
  updateInspector();
}

function deselectAll() {
  selectedElems().forEach(deselect);
}

window.atEndOfDragSoPreventClickSelect = false;
// Selectable element clicked...
function clickSelect(event) {
  if (atEndOfDragSoPreventClickSelect) {
    atEndOfDragSoPreventClickSelect = false;
    event.stopImmediatePropagation();
    return;
  }
  submitAllChangedTextboxes();
  const elem = event.currentTarget;
  if (elem.closest(".not-in-active-frame")) {
    // Don't select. Instead let the click bubble to the handler that will set the active frame.
    return;
  }
  event.stopImmediatePropagation();
  if (elem.classList.contains("selected")) {
    // Is this a double click?
    if (500 >= new Date() - (elem.lastClickTime || 0)) {
      selectInspectorTextbox();
    } else {
      deselectAll();
    }
  } else {
    deselectAll();
    select(elem);
    elem.lastClickTime = new Date()
  }
}

// Attempt to preserve selections over page reloads.
//
// Referencing by item number on page.
function saveSelection() {
  const selectedIndices = [];

  var i = 0
  const selectables = document.querySelectorAll('.selectable');
  selectables.forEach(elem => {
    if (elem.classList.contains("selected")) {
      selectedIndices.push(i);
    }
    i++;
  });

  window.sessionStorage.setItem("selectedIndices",  JSON.stringify(selectedIndices));
  window.sessionStorage.setItem("selectablesCount", JSON.stringify(selectables.length));
}

function restoreSelection() {
  const selectedIndices          = JSON.parse(window.sessionStorage.getItem("selectedIndices") || "[]");
  const previousSelectablesCount = JSON.parse(window.sessionStorage.getItem("selectablesCount") || "-1");

  deselectAll();
  var i = 0
  const selectables = document.querySelectorAll('.selectable');
  if (previousSelectablesCount != selectables.length) { return; }
  selectables.forEach(elem => {
    if (selectedIndices.includes(i)) {
      select(elem);
    }
    i++;
  });
}

function submitAllChangedTextboxes() {
  document.querySelectorAll("input[type=text],.textbox").forEach(elem => {
    elem.submit && elem.submit();
  });
}

window.addEventListener('DOMContentLoaded', () => {

  function globalEscape() {
    if (transientTextboxes().length > 0) {
      transientTextboxes().forEach(abortTextEdit);
    } else if (selectedElems().length > 0) {
      deselectAll();
    } else {
      // document.location.reload();
    }
  }

  // When you click out of everything
  function globalSubmitEscape() {
    submitAllChangedTextboxes();
    globalEscape();
  }

  document.querySelectorAll('.vbs').forEach(elem => {
    elem.addEventListener("click", globalSubmitEscape);
  });
  // Make appropriate items selectable.
  document.querySelectorAll('[data-extraction-code]:not(.tool),.vb,[data-in-place-edit-loc],[code-to-assert-on]').forEach(elem => {
    elem.classList.add("selectable");
    elem.addEventListener("click", clickSelect);
  });
  document.addEventListener("keydown", event => {
    if (event.key === "Esc" || event.key === "Escape") {
      globalEscape();
      event.stopImmediatePropagation();
    }
  });

  // Still not sure when to do this
  // restoreSelection();
});



/////////////////// Inspector ///////////////////

// Visualizers root, also for determining where to place asserts.
function containingLoc(elem) {
  return elem.closest("[data-loc]").dataset.loc;
}

function textboxKeydownHandler(event) {
  let textbox = event.currentTarget;
  if (event.key === "Enter" && textbox.value) {
    textbox.submit();
  } else if (event.key === "Esc" || event.key === "Escape") {
    textbox.value = textbox.originalValue || "";
    textbox.blur();
    delete textbox.targetElem;
  }
  event.stopImmediatePropagation();
}

// function onAdd(code) {
//   const elem = selectedElems()[0];
//   const vbsHolder = vbsHolderForInsert(elem);
//   insertCode(vbsHolder.dataset.loc, code);
// }

function onVisualize(code) {
  const selectedElem = selectedElems()[0];
  // lastElemInTextbox = visTextbox.childNodes[visTextbox.childNodes.length - 1];
  // if (lastElemInTextbox?.dataset?.valueId) {
  //   if (lastElemInTextbox.dataset.valueId === selectedElem?.dataset?.valueId) {
  //     lastElemInTextbox.remove()
  //   }
  // }
  const vis = code;
  const loc = containingLoc(selectedElem);
  addVis(loc, vis);
}

window.addEventListener('DOMContentLoaded', () => {
  window.inspector = document.getElementById("inspector");

  // document.getElementById("use-textbox").addEventListener("keydown", textboxKeydownHandler((targetElem, text) => {
  //   const vis = text;
  //   addVis(containingLoc(targetElem), vis);
  // }));

  // document.getElementById("node-textbox").addEventListener("keydown", textboxKeydownHandler((targetElem, text) => {
  //   replaceLoc(targetElem.dataset.inPlaceEditLoc, text);
  // }));

  // document.getElementById("root-node-textbox").addEventListener("keydown", textboxKeydownHandler((targetElem, text) => {
  //   replaceLoc(targetElem.dataset.inPlaceEditLoc, text);
  // }));

  const assertTextbox = document.getElementById("assert-textbox");
  assertTextbox.submit = () => {
    const code = assertTextbox.value;
    if (code !== assertTextbox.originalValue) {
      let elem = assertTextbox.targetElem;
      elem && newAssert(containingLoc(elem), elem.dataset.codeToAssertOn, code);
    }
  };
  assertTextbox.addEventListener("keydown", textboxKeydownHandler);

  // document.getElementById("add-button").addEventListener("click", event => {
  //   const code = textboxDivToCode(document.getElementById("use-textbox"));
  //   onAdd(code);
  //   // event.stopImmediatePropagation();
  //   // event.preventDefault();
  // });

  // document.getElementById("visualize-button").addEventListener("click", event => {
  //   const selectedElem = selectedElems()[0];
  //   const useTextbox = document.getElementById("use-textbox")
  //   // Visualizers are supposed be code of type 'a -> 'b
  //   // But if you provide a simple example application, we'll curry it for you.
  //   lastElemInTextbox = useTextbox.childNodes[useTextbox.childNodes.length - 1];
  //   if (lastElemInTextbox?.dataset?.valueId) {
  //     if (lastElemInTextbox.dataset.valueId === selectedElem?.dataset?.valueId) {
  //       lastElemInTextbox.remove()
  //     }
  //   }
  //   const vis = textboxDivToCode(useTextbox);
  //   const loc = containingLoc(selectedElem);
  //   addVis(loc, vis);
  // });

  document.getElementById("visualize-button").addEventListener("click", event => {
    const visTextbox = document.getElementById("vis-textbox");
    onVisualize(textboxDivToCode(visTextbox));
  });

  window.addEventListener("resize", updateInspector);
  window.addEventListener("scroll", updateInspector);

  updateInspector();
});

function selectInspectorTextbox() {
  let found = false;
  window.inspector.querySelectorAll("input[type=text],.textbox").forEach(textbox => {
    if (!found) {
      if (selfAndParents(textbox).every(isShown)) {
        found = true;
        // textbox.select();
        textbox.focus();
      }
    }
  });
}

function updateInspector() {
  const inspector         = window.inspector;
  const textEditPane      = document.getElementById("text-edit-pane");
  const textEditRootStuff = document.getElementById("text-edit-root-stuff");
  const rootNodeTextbox   = document.getElementById("root-node-textbox");
  const nodeTextbox       = document.getElementById("node-textbox");
  const assertPane        = document.getElementById("assert-pane");
  const assertOn          = document.getElementById("assert-on");
  const assertTextbox     = document.getElementById("assert-textbox");
  const typeOfSelected    = document.getElementById("type-of-selected");
  // const usePane           = document.getElementById("use-pane");
  // const useTextbox        = document.getElementById("use-textbox");
  const visPane           = document.getElementById("vis-pane");
  const visTextbox        = document.getElementById("vis-textbox");
  const visList           = document.getElementById("vis-list");

  const elem = selectedElems()[0];

  inspector.querySelectorAll(".autocomplete-options").forEach(autocompleteDiv => autocompleteDiv.remove()); decolorizeSubvalues();

  function onTextEditAbort(event, textboxDiv) {
    textboxDiv.innerText = textboxDiv.originalValue;
    textboxDiv.blur();
    event.stopImmediatePropagation();
  }

  const makeVisRow = (vis, isVised) => {
    const label = document.createElement("label");
    const checkbox = document.createElement("input");
    checkbox.type = "checkbox";
    checkbox.checked = isVised;
    label.appendChild(checkbox);
    label.appendChild(document.createTextNode("Visualize"));
    checkbox.addEventListener("change", ev => {
      const loc = containingLoc(elem);
      if (checkbox.checked) {
        // well, there was a time when we needed this
        // now this isn't even shown if the vis isn't active
        addVis(loc, vis);
      } else {
        removeVis(loc, vis);
      }
    });

    const row = document.createElement("div");
    row.classList.add("vis-row");
    row.appendChild(document.createTextNode(vis));
    row.appendChild(label);
    // const addButton = document.createElement("button");
    // addButton.innerText = "Add"
    // addButton.addEventListener("click", ev => {
    //   const vbsHolder = vbsHolderForInsert(elem);
    //   const code = `${vis} (${elem.dataset.extractionCode})`;
    //   insertCode(vbsHolder.dataset.loc, code);
    // });
    // row.appendChild(addButton);
    return row;
  }

  if (elem && transientTextboxes().length === 0) {
    const rect = elem.getBoundingClientRect();
    // const viewWidth =
    inspector.style.width = 280;
    // Position to the right or below.
    if (rect.right + 300 < document.body.clientWidth) {
      inspector.style.left = rect.right
      inspector.style.top  = rect.top
    } else {
      inspector.style.left  = Math.min(rect.left, document.body.clientWidth - 300);
      inspector.style.top   = rect.bottom;
    }
    show(inspector);

    if (elem.dataset.inPlaceEditLoc) {
      let rootNodeElem = undefined;
      if (elem.classList.contains('exp')) {
        for (const parent of selfAndParents(elem)) {
          if (parent.dataset.inPlaceEditLoc) {
            rootNodeElem = parent;
          } else {
            break;
          }
        }
      }
      const rootNodeCode            = rootNodeElem?.dataset?.inPlaceEditCode || rootNodeElem?.innerText;
      // rootNodeTextbox.value         = rootNodeCode;
      rootNodeTextbox.innerText     = rootNodeCode;
      // rootNodeTextbox.originalValue = rootNodeCode;
      // rootNodeTextbox.targetElem    = rootNodeElem;
      const nodeCode                = elem.dataset.inPlaceEditCode || elem.innerText;
      // nodeTextbox.value             = nodeCode;
      nodeTextbox.innerText         = nodeCode;
      // nodeTextbox.originalValue     = nodeCode;
      // nodeTextbox.targetElem        = elem;
      if (!rootNodeElem || rootNodeElem === elem) {
        hide(textEditRootStuff);
      } else {
        show(textEditRootStuff);
        attachAutocomplete(rootNodeTextbox, rootNodeElem, code => replaceLoc(rootNodeElem.dataset.inPlaceEditLoc, code), onTextEditAbort);
      }
      show(textEditPane);
      attachAutocomplete(nodeTextbox,     elem,         code => replaceLoc(elem.dataset.inPlaceEditLoc, code),         onTextEditAbort);
    } else {
      hide(textEditPane);
    }
    if (elem.dataset.codeToAssertOn) {
      assertOn.innerText          = elem.dataset.codeToAssertOn;
      assertTextbox.value         = "";
      assertTextbox.originalValue = "";
      assertTextbox.targetElem    = elem;
      show(assertPane);
    } else {
      hide(assertPane);
    }

    const typeStr = elem.dataset.type;
    if (typeStr) {
      typeOfSelected.innerText = typeStr;
      show(typeOfSelected);
    } else {
      hide(typeOfSelected);
    }

    if (elem.dataset.valueId) {
      // useTextbox.innerText     = "";
      // useTextbox.originalValue = "";
      // attachAutocomplete(useTextbox, elem, onAdd, onTextEditAbort, elem.dataset.valueId);
      // useTextbox.targetElem = elem;
      // show(usePane);
    } else {
      // hide(usePane);
    }

    visList.innerHTML = "";
    const activeVises = (elem.dataset.activeVises || "").split("  ").removeAsSet("");
    activeVises.forEach(vis => visList.appendChild(makeVisRow(vis, true)));

    if (!elem.closest(".derived-vis-value") && (elem.dataset.hasOwnProperty('activeVises') || activeVises.length > 0)) {
      visTextbox.innerText     = "(* something 'a -> 'b *)";
      // visTextbox.originalValue = "";
      attachAutocomplete(visTextbox, elem, onVisualize, onTextEditAbort);
      // useTextbox.targetElem = elem;
      show(visPane);
      const possibleVises = (elem.dataset.possibleVises || "").split("  ").removeAsSet("");
      possibleVises.forEach(vis => {
        if (!activeVises.includes(vis)) {
          visList.appendChild(makeVisRow(vis, false));
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

// https://stackoverflow.com/a/17323608
function mod(n, m) {
  return ((n % m) + m) % m;
}

function hide(elem) {
  elem.classList.add("hidden");
}

function show(elem) {
  elem.classList.remove("hidden");
}

function isShown(elem) {
  return !elem.classList.contains("hidden");
}

function abortTextEdit(textbox) {
  // if (textbox.originalElem) { show(textbox.originalElem) };
  textbox.autocompleteDiv?.remove(); decolorizeSubvalues();
  textbox.remove();
  updateInspector();
}

function isNotVis(elem) {
  return !elem.closest(".derived-vis-value");
}
function isNotInLabel(elem) {
  return !elem.closest(".label");
}
function allExtractableValues() {
  // We add valueIds to all of these.
  return Array.from(document.querySelectorAll(".root-value-holder .value[data-extraction-code]"));
}
function localValuesShownInFrame(elem) {
  const frameNoElem = findFrameNoElem(elem);
  // Erroneously includes more deeply nested values that are otherwise inaccessible...
  return Array.from(frameNoElem.querySelectorAll(".root-value-holder:not(.not-in-active-frame) .value[data-extraction-code]")).filter(isShown).filter(isNotVis).filter(isNotInLabel);
}
window.addEventListener('DOMContentLoaded', () => {
  let valueId = 1;
  allExtractableValues().forEach(elem => {
    elem.dataset.valueId = `${valueId}`;
    valueId++;
  });
});


autocompleteOpen = false;
function colorizeSubvalues(elem) {
  let hue = 30;
  localValuesShownInFrame(elem).forEach(elem => {
    elem.style.color = `hsl(${hue}, 90%, 40%)`;
    hue = (hue + 152) % 360;
  });
  autocompleteOpen = true;
}
function decolorizeSubvalues(elem) {
  allExtractableValues().forEach(elem => {
    elem.style.color = null;
  });
  autocompleteOpen = false;
}

function transientTextboxes() {
  return document.querySelectorAll(".transient-textbox");
}

// function beginEditCallback(editType) {
//   return function (event) {
//     event.stopImmediatePropagation();
//     const originalElem = event.currentTarget;
//     // const parent = originalElem.parentElement;
//     console.log(originalElem);
//     const input = document.createElement("input");
//     input.type = "text";
//     input.value = originalElem.dataset.inPlaceEditCode || originalElem.innerText;
//     input.classList.add("transient-textbox");
//     input.originalElem = originalElem;
//     // originalElem.appendChild(input);
//     originalElem.insertAdjacentElement("afterend", input);
//     hide(originalElem);
//     // input.focus();
//     updateInspector();
//     input.select();

//     input.addEventListener('keydown', event => {
//       // console.log(event.key);
//       if (event.key === "Enter") {
//         if (editType === "in-place") {
//           if (input.value.length > 0) {
//             replaceLoc(originalElem.dataset.inPlaceEditLoc, input.value);
//           } else {
//             deleteLoc(originalElem.dataset.inPlaceEditLoc);
//           }
//         } else if (editType === "new assert") {
//           if (input.value.length > 0) {
//             newAssert(containingLoc(originalElem), originalElem.dataset.codeToAssertOn, input.value);
//           }
//         } else {
//           console.warn("Unknown edit type " + editType)
//         }
//       } else if (event.key === "Esc" || event.key === "Escape") {
//         abortTextEdit(input);
//       }
//       event.stopImmediatePropagation();
//     });
//   }
// }

// Convert autocompleted values to code
function textboxDivToCode(textboxDiv) {
  let code = "";
  for (child of textboxDiv.childNodes) {
    if (child.nodeType === 3) {
      // Text node
      code += child.data.replaceAll("\u00A0"," "); /* Remove non-breaking spaces...which are produced by space bar */
    } else if (child.tagName === "BR") {
      code += "\n"
    } else {
      // value node
      code += `(${child.dataset.extractionCode})`
    }
  }
  return code;
}

// if (option.isValue) {
//   option.remove();
//   option.contentEditable = false;
// } else {
//   textboxDiv.appendChild(document.createTextNode(option.innerText));
// }

// What we send to server to ask for suggestions
// Autocompleted (sub)values are turned into (vtrace "hJWmvgAAAg4AAACUAAAB9wAAAfSgoKABANGwwClzaW1wbGUubWxBQE_ABAJBQGRAoLC6Ijo6QJCwmaCwkUCgoKABANCwwAQRRQB_AQCQwAQSRQB_AQCRQEBAkMCWwLOQsEEjaW50QECQQAED70ABAyYBA_BAAQMmoLC6BBlAkLCZoLCRQKCgoAEA0LDABClFAH8BAJPABCpFAH8BAJRAQECQwJYEGAED70ABAyqgsLoEK0CQsJmgsJFAoKCgAQDQsMAEO0UAfwEAlsAEPEUAfwEAl0BAQJDAlgQqAQPvQAEDLqCwuiJbXUBAoKCgAQDQsMAESEUAfwEAmMAESUUAfwEAmUFAQJDAlsCzkLBJJGxpc3RAoMCWBD8BA-9AAQMsQJBAAQPvQAEDLQED70ABAy9AoKCgAQDQsAQfBBFBQEBAoKCgAQDQBARAQJDAs5CwSSRsaXN0QKDABCYBA_BAAQM8QJBAAQPwQAEDO0CgoKABANCwBEEEIUFAQECgoKABANAEBEBAkMCzBBCgwARFAQPwQAEDP0CQQAED8EABAz5AoKCgAQDQsARmBC5BQEBAoKCgAQDQsMAEe0cBAKsBALzABHxHAQCrAQDEQEGgoKABANCwwASBRQB_AQCDwASCRQB_AQCLQKCwBICgoKABANCwwASJRQB_AQCOBEFAQECQwLMELaDABHoBA_BAAQNCQJBAAQPwQAEDQUAECwQGQAQZ")
function textboxDivToSuggestionQuery(textboxDiv) {
  let code = "";
  // Convert autocompleted values to code
  for (child of textboxDiv.childNodes) {
    if (child.nodeType === 3) {
      // Text node
      code += child.data.replaceAll("\u00A0"," "); /* Remove non-breaking spaces...which are produced by space bar */
    } else {
      // value node
      code += `value_id_${child.dataset.valueId}`
    }
  }
  return code;
}

function subvalueToOptionPart(subvalueElem) {
  let subvaluePart = subvalueElem.cloneNode(true);
  subvaluePart.querySelectorAll(".subvalue-annotations").forEach(elem => elem.remove());
  subvaluePart.isValue = true;
  subvaluePart.originalElem = subvalueElem;
  subvaluePart.contentEditable = false;
  // console.log(subvaluePart);
  // console.log(subvaluePart.innerText);
  // console.log(subvaluePart.innerHTML);
  return subvaluePart;
}

function optionFromSuggestion(suggestion) {
  const parts = suggestion.split(/\b/); /* Split on word boundaries */
  // Convert to nodes, turning value_id_123 into a pretty clone of that subvalue on the screen
  const values = allExtractableValues();
  const nodes = parts.map(part => {
    let subvalueElem = null;
    if (part.startsWith('value_id_')) {
      // Try to find that subvalue
      const valueIdStr = "" + part.match(/value_id_(\d+)/)[1];
      subvalueElem = values.find(elem => elem.dataset.valueId && elem.dataset.valueId === valueIdStr);
    }
    if (subvalueElem) {
      return subvalueToOptionPart(subvalueElem);
    } else {
      return document.createTextNode(part);
    }
  });
  const option = document.createElement("div");
  for (const node of nodes) { option.appendChild(node); }
  return option;
}

function attachAutocomplete(textboxDiv, targetElem, onSubmit, onAbort, selectedValueIdStr) {
  // No autocomplete for pats, for now
  const should_show_autocomplete = !targetElem.classList.contains("pat")

  const autocompleteDiv = document.createElement("div");
  autocompleteDiv.classList.add("autocomplete-options");
  autocompleteDiv.style.position = "absolute";
  hide(autocompleteDiv);
  textboxDiv.targetElem = targetElem;
  textboxDiv.autocompleteDiv?.remove();
  textboxDiv.parentElement.appendChild(autocompleteDiv);
  textboxDiv.autocompleteDiv = autocompleteDiv;
  textboxDiv.originalValue = textboxDivToCode(textboxDiv);
  textboxDiv.submit = () => {
    const code = textboxDivToCode(textboxDiv);
    if (code !== textboxDiv.originalValue) {
      onSubmit(code);
    }
  };

  textboxDiv.removeEventListeners();
  textboxDiv.addEventListener('keydown', event => {
    // console.log(event.key);
    if (event.key === "Enter") {
      if (textboxDiv.innerText.length > 0) {
        textboxDiv.submit();
        // insertCode(vbsHolder.dataset.loc, code);
        event.stopImmediatePropagation(); /* does this even do anything? */
        event.preventDefault(); /* Don't insert a newline character */
      }
    } else if (event.key === "Esc" || event.key === "Escape") {
      decolorizeSubvalues();
      onAbort(event, textboxDiv);
    } else if (event.key === "ArrowDown") {
      textboxDiv.blur();
      autocompleteDiv.children[0]?.focus();
      event.preventDefault();
    } else if (event.key === "ArrowUp") {
      textboxDiv.blur();
      autocompleteDiv.children[autocompleteDiv.children.length - 1]?.focus();
      event.preventDefault();
    } else if (event.key === "Backspace" || event.key === "Delete") {
      event.stopImmediatePropagation(); /* Don't hit the global delete handler */
    }
    // event.stopImmediatePropagation();
  }, { capture: true }); /* Run this handler befooooorrre the typing happens */
  textboxDiv.addEventListener('keyup', _ => { should_show_autocomplete && updateAutocompleteAsync(textboxDiv, selectedValueIdStr); });
  // Prevent click on elem from bubbling to the global deselect/abort handler
  textboxDiv.addEventListener('click', event => {
    event.stopPropagation();
  });
  textboxDiv.addEventListener('focus', event => {
    should_show_autocomplete && colorizeSubvalues(targetElem);
    window.getSelection().selectAllChildren(textboxDiv);
    should_show_autocomplete && updateAutocompleteAsync(textboxDiv, selectedValueIdStr);
  });
}

function updateAutocompleteAsync(textboxDiv, selectedValueIdStr) {
  const vbsLoc          = vbsHolderForInsert(textboxDiv.targetElem).dataset.loc;
  const valuesVisible   = localValuesShownInFrame(textboxDiv.targetElem);
  const valueIdsVisible = valuesVisible.map(elem => elem.dataset.valueId);
  const valueStrs       = valuesVisible.map(elem => subvalueToOptionPart(elem).innerText.replaceAll("\n"," ").trim().replaceAll(",","~CoMmA~") /* escape commas */ );
  // console.log(valueStrs);
  const query           = textboxDivToSuggestionQuery(textboxDiv);

  // https://stackoverflow.com/a/57067829
  const searchURL = new URL(document.location.href + "/search");
  let queryParams = { vbs_loc: vbsLoc, value_ids_visible: valueIdsVisible, value_strs: valueStrs, q: query };
  if (selectedValueIdStr) { queryParams["selected_value_id"] = selectedValueIdStr; }
  searchURL.search = new URLSearchParams(queryParams).toString();
  let request = new XMLHttpRequest();
  request.open("GET", searchURL);
  request.addEventListener("loadend", _ => {
    // console.log(request.responseText);
    updateAutocomplete(textboxDiv, request.responseText.split("|$SEPARATOR$|").filter(str => str.length > 0).filter(str => str !== textboxDiv.originalValue))
  });
  request.send();
}

function updateAutocomplete(textboxDiv, suggestions) {
  // console.log(suggestions);
  const autocompleteDiv = textboxDiv.autocompleteDiv;
  autocompleteDiv.innerHTML = "";

  if (suggestions.length > 0) {
    autocompleteDiv.style.left = `${textboxDiv.offsetLeft}px`;
    autocompleteDiv.style.top  = `${textboxDiv.offsetTop + textboxDiv.offsetHeight}px`;
    show(autocompleteDiv);
  } else {
    hide(autocompleteDiv);
  }
  for (const suggestion of suggestions) {
    // const optionDiv = document.createElement("div");
    // optionDiv.innerText = option;
    let option = optionFromSuggestion(suggestion);
    option.tabIndex = 0; /* Make element focusable, even though below we override tab */
    function chooseOption(event) {
      option.remove()
      autocompleteDiv.innerHTML = "";
      textboxDiv.innerHTML = "";
      for (const child of Array.from(option.childNodes)) { /* If we don't convert to array, for some reason the whitespace nodes are skipped. */
        textboxDiv.appendChild(child);
      }
      // label.appendChild(document.createTextNode("Visualize"));
      textboxDiv.focus()
      // Set cursor to end of "input" element
      window.getSelection().selectAllChildren(textboxDiv);
      window.getSelection().collapseToEnd();
      event.stopImmediatePropagation();
      event.preventDefault();
    }
    option.addEventListener('keydown', event => {
      let focusedOptionIdx = -1;
      for (i in autocompleteDiv.children) {
        if (document.activeElement === autocompleteDiv.children[i]) {
          focusedOptionIdx = parseInt(i);
        }
      }
      // console.log(autocompleteDiv.children.length);
      // console.log(focusedOptionIdx);
      // console.log(focusedOptionIdx + 1);
      // console.log(mod(focusedOptionIdx + 1, autocompleteDiv.children.length));
      if (event.key === "ArrowDown") {
        autocompleteDiv.children[mod(focusedOptionIdx + 1, autocompleteDiv.children.length)].focus();
        event.stopImmediatePropagation();
        event.preventDefault();
      } else if (event.key === "ArrowUp") {
        autocompleteDiv.children[mod(focusedOptionIdx - 1, autocompleteDiv.children.length)].focus();
        event.stopImmediatePropagation();
        event.preventDefault();
      } else if (event.key === "Enter" || event.key === "Tab") {
        chooseOption(event);
      } else if (event.key === "Esc" || event.key === "Escape") {
        textboxDiv.focus()
        event.stopImmediatePropagation();
        event.preventDefault();
      } else if (event.key === "Backspace" || event.key === "Escape") {
        textboxDiv.focus()
        event.stopImmediatePropagation();
        // event.preventDefault(); /* By default the event will actually delete in the textbox. Which we want. */
      }
    }, { capture: true }); /* Run handler beefoooore it triggers a scroll */

    option.addEventListener('click', chooseOption);
    option.addEventListener('focus', event => {
      document.querySelectorAll(".highlighted").forEach(elem => { elem.classList.remove("highlighted") });
      for (const part of option.children) {
        part.originalElem?.classList?.add("highlighted");
      }
    });
    option.addEventListener('blur', event => {
      for (const part of option.children) {
        part.originalElem?.classList?.remove("highlighted");
      }
    });

    autocompleteDiv.appendChild(option);
  }

  removeTreeEdges();
  redrawTreeEdges();
}


function beginNewCodeEdit(vbsHolder) {
  return function (event) {
    if (event.target !== vbsHolder) { return; }
    event.stopImmediatePropagation();

    const textboxDiv = document.createElement("div");
    textboxDiv.contentEditable = true;
    textboxDiv.classList.add("transient-textbox");
    textboxDiv.classList.add("textbox");
    textboxDiv.style.position = "absolute";
    // textboxDiv.style.backgroundColor = "white";
    const { x, y } = mouseReletiveToElem(vbsHolder, event);
    const pos = { x: x - 5, y: y - 10 };
    textboxDiv.style.left = `${pos.x}px`;
    textboxDiv.style.top  = `${pos.y}px`;
    vbsHolder.appendChild(textboxDiv);
    attachAutocomplete(textboxDiv, vbsHolder, code => insertCode(vbsHolder.dataset.loc, code, pos), _ => abortTextEdit(textboxDiv));
    textboxDiv.focus();
  }
}



window.addEventListener('DOMContentLoaded', () => {
  // document.querySelectorAll('[data-in-place-edit-loc]').forEach(elem => {
  //   elem.addEventListener("dblclick", beginEditCallback("in-place"));
  // });

  // document.querySelectorAll('[data-code-to-assert-on]').forEach(elem => {
  //   elem.addEventListener("dblclick", beginEditCallback("new assert"));
  // });


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
    particle.style.left = 0;
    particle.style.top = 0;
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

function vbsHolderForInsert(elem) {
  const deeperVbs =
    // Function vbs for selected binding
    elem.querySelector(":scope > .tv > .fun > .vbs") ||
    // Nested vbs for selected binding
    elem.querySelector(":scope > .tv > .vbs");
  if (deeperVbs) {
    return deeperVbs;
  }

  const scopeElem = elem.closest(".vbs, .exp.fun");
  if (scopeElem.classList.contains("vbs")) {
    return scopeElem;
  } else {
    return scopeElem.querySelector(".vbs");
  }
}

function setMainTool(code, mainToolElem) {
  // console.log(mainToolElem);
  if (mainToolElem) {
    mainToolElem.innerText              = code;
    mainToolElem.dataset.extractionCode = code;
    window.sessionStorage.setItem("selected tool " + mainToolElem.dataset.toolKey,  code);
  }
}
function getMainToolElem(toolElem) {
  return toolElem.closest(".tool-menu")?.previousSibling;
}

window.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll(".tool[data-extraction-code]").forEach(elem => {
    elem.addEventListener("click", _ => {
      const code = elem.dataset.extractionCode;
      const selected = selectedElems()[0] || document.querySelector(".top-level");
      // console.log(selected);
      // console.log(vbsHolderForInsert(selected));
      setMainTool(code, getMainToolElem(elem));
      insertCode(vbsHolderForInsert(selected).dataset.loc, code);
    });
  });

  // Restore most recently used tools
  document.querySelectorAll("[data-tool-key]").forEach(elem => {
    const code = window.sessionStorage.getItem("selected tool " + elem.dataset.toolKey);
    if (code && elem.nextElementSibling.innerHTML.includes(code)) {
      elem.innerText              = code;
      elem.dataset.extractionCode = code;
    }
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
function mouseReletiveToElem(elem, event) {
  const { dx, dy } = topLeftOffsetFromMouse(elem, event);
  return { x: -dx, y: -dy };
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
  if (dropTarget && isStartingVbs(dropTarget, window.stuffMoving.elem)) {
    return undefined;
  } else {
    return dropTarget;
  }
}

// Need to only show movability border when hovering over the box but NOT any of its children.
function moveableMaybeHover(boxElem) {
  return function(event) {
    // https://stackoverflow.com/questions/8813051/determine-which-element-the-mouse-pointer-is-on-top-of-in-javascript
    if (boxElem === document.elementFromPoint(event.clientX, event.clientY)) {
      boxElem.classList.add("moveable-hovered");
    } else {
      boxElem.classList.remove("moveable-hovered");
    }
  };
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

  // Show border on hover/unhover. Must be JS because we don't want the border when children hovered.

  document.querySelectorAll(".box").forEach(elem => {
    elem.addEventListener("mouseover", moveableMaybeHover(elem));
    elem.addEventListener("mouseout",  moveableMaybeHover(elem));
  });

});


// function stuffMoved(event) {
//   if (window.stuffMoving) {
//     const dx = event.pageX - stuffMoving.startX;
//     const dy = event.pageY - stuffMoving.startY;
//     return (dx !== 0 || dy !== 0);
//   } else {
//     return false;
//   }
// }


window.addEventListener('DOMContentLoaded', () => {

  document.querySelectorAll(".top-level").forEach(elem => {
    elem.addEventListener("mousemove", event => {
      if (window.stuffMoving) {
        hide(window.inspector);
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
          atEndOfDragSoPreventClickSelect = true;
        } else if (dropTarget) {
          const dropTargetOffsetFromMouse = topLeftOffsetFromMouse(dropTarget, event);
          const x = stuffMoving.offsetFromMouse.dx - dropTargetOffsetFromMouse.dx;
          const y = stuffMoving.offsetFromMouse.dy - dropTargetOffsetFromMouse.dy;
          moveVb(dropTarget.dataset.loc, elem.dataset.loc, { x : x, y : y });
          atEndOfDragSoPreventClickSelect = true;
        } else {
          elem.style.zIndex = "auto";
        }
        window.stuffMoving = undefined;
        removeDropTargetStyles();
        event.stopImmediatePropagation();
      }
    });
  });
});

// Make sure each vbs holder has place for all the vbs
// Resize deepest first.
function resizeVbHolders() {
  const vbsHolders = document.querySelectorAll(".vbs:not(.top-level)");
  const minVbHolderHeight = 70;
  // Traverse deepest first
  Array.from(vbsHolders).reverse().forEach(vbsHolder => {
    // console.log(vbsHolder.children);
    let maxWidth = 0;
    let maxHeight = 0;
    for (box of vbsHolder.children) {
      // console.log(box);
      if (box.classList.contains("box")) { /* Skip transient textboxes in the vbs elem */
        maxWidth  = Math.max(maxWidth, box.offsetLeft + box.offsetWidth);
        maxHeight = Math.max(maxHeight, box.offsetTop + box.offsetHeight);
        console.log(maxWidth,maxHeight,box);
      }
    }
    if (vbsHolder.tagName === "TD") {
      vbsHolder.style.width  = `${maxWidth + 10}px`
      vbsHolder.style.height = `${Math.max(maxHeight + 10, minVbHolderHeight)}px`
    } else {
      vbsHolder.style.minWidth  = `${maxWidth + 10}px`
      vbsHolder.style.minHeight = `${Math.max(maxHeight + 10, minVbHolderHeight)}px`
    }
  });
};
function reflow() {
  const vbsHolders = document.querySelectorAll(".vbs");
  function left(box)  { return box.offsetLeft; }
  function top(box)   { return box.offsetTop; }
  function right(box) { return box.offsetLeft + box.offsetWidth; }
  function bot(box)   { return box.offsetTop + box.offsetHeight; }
  function areOverlapping(box1, box2) {
    if (right(box1) < left(box2) || right(box2) < left(box1)) { return false; }
    if (bot(box1)   < top(box2)  || bot(box2)   < top(box1))  { return false; }
    // console.log(box1, box2, left(box1), top(box1), right(box1), bot(box1), left(box2), top(box2), right(box2), bot(box2));
    return true;
  }
  function size(box) { return box.offsetWidth * box.offsetHeight; }
  vbsHolders.forEach(vbsHolder => {
    const boxes = Array.from(vbsHolder.children).filter(box => box.classList.contains("box")); /* Skip transient textboxes in the vbs elem */
    // Position largest stuff first.
    boxes.sort((box1, box2) => size(box2) - size(box1));
    for (box of boxes) {
      const mySize = size(box);
      const boxesToDodge = boxes.filter(otherBox => otherBox.style.left && otherBox !== box && mySize <= size(otherBox)); /* If box has an explicit position and is larger */
      var left0 = parseInt(box.dataset.left);
      var top0  = parseInt(box.dataset.top);
      if (isNaN(left0)) { left0 = 10 };
      if (isNaN(top0) && vbsHolder.classList.contains("top-level")) { top0 = 50 };
      if (isNaN(top0)) { top0 = 10 };

      // More or less, move in the cardinal direction that moves the box the least.
      var r = 0;
      var theta = 0;
      box.style.left = `${left0 + r * Math.cos(theta + Math.PI/2)}px`
      box.style.top  = `${top0  + r * Math.sin(theta + Math.PI/2)}px`
      while (parseInt(box.style.left) < 0 || parseInt(box.style.top) < 0 || boxesToDodge.find(box2 => areOverlapping(box, box2))) {
        r += 10;
        theta = 0;
        while ((parseInt(box.style.left) < 0 || parseInt(box.style.top) < 0 || boxesToDodge.find(box2 => areOverlapping(box, box2))) && theta < 2*Math.PI) {
          box.style.left = `${left0 + r * Math.cos(theta + Math.PI/2)}px`;
          box.style.top  = `${top0  + r * Math.sin(theta + Math.PI/2)}px`;
          theta += Math.PI/2;
        }
      }
    }
  });
}
function initializeLayout() {
  document.querySelectorAll(".vbs").forEach(vbsHolder => {
    const boxes = Array.from(vbsHolder.children).filter(box => box.classList.contains("box")); /* Skip transient textboxes in the vbs elem */
    for (box of boxes) {
      var left0 = parseInt(box.dataset.left);
      var top0  = parseInt(box.dataset.top);
      if (isNaN(left0)) { left0 = 10 };
      if (isNaN(top0) && vbsHolder.classList.contains("top-level")) { top0 = 50 };
      if (isNaN(top0)) { top0 = 10 };
      box.style.left = `${left0}px`
      box.style.top  = `${top0}px`
    }
  });
}
function relayout() {
  removeTreeEdges();
  initializeLayout();
  for (_ of [1,2,3]) {
    resizeVbHolders(document);
    reflow();
  }
  resizeVbHolders(document);
  redrawTreeEdges();
}
// This happens in initFrameNos
// window.addEventListener('DOMContentLoaded', relayout);



//////////////// rec checkboxes /////////////////////////////////

window.addEventListener('DOMContentLoaded', () => {
  // Prevent clicks on label from triggering selection
  document.querySelectorAll(".is-rec").forEach(elem => {
      elem.addEventListener("click", event => event.stopImmediatePropagation());
  })
  document.querySelectorAll(".is-rec input[type=checkbox]").forEach(elem => {
    elem.addEventListener("change", event => {
      setRecFlag(elem.dataset.loc, elem.checked);
      event.stopImmediatePropagation();
    });
  })
});


/////////////////// What Am I ///////////////////

// Self is first, root is last.
// Based on https://developer.mozilla.org/en-US/docs/Web/API/Element/closest#polyfill
function selfAndParents(elem) {
  const out = [];
  while (elem !== null && elem.nodeType === 1) {
    out.push(elem);
    elem = elem.parentElement || elem.parentNode;
  }
  return out;
}

// // .exp .vb and .pat are littered around the HTML
// // Messy because Maniposynth's canvas is deliberately not 1-to-1 with the code.
// function isInPatternPosition(elem) {
//   for (const el of selfAndParents(elem)) {
//     if (el.classList.contains("pat")) {
//       return true;
//     } else if (el.classList.contains("vb")) {
//       return false;
//     } else if (el.classList.contains("exp")) {
//       return false;
//     }
//   }
//   return false;
// }

// function containingVb(elem) {
//   return elem.closest(".vb");
// }

// function childVbsHolder(elem) {

// }


/////////////////// Frame Number Handling ///////////////////

function frameNoForElem(elem) {
  return findFrameNoElem(elem)?.dataset?.activeFrameNo;
}

function findFrameNoElem(elem) {
  return elem.closest(".fun,.top-level");
}

function frameNos(frameRootElem) {
  return Array.from(frameRootElem.querySelectorAll("[data-frame-no]")).map(elem => elem.dataset.frameNo).sort((fn1, fn2) => parseInt(fn1) - parseInt(fn2)).dedup();
}

// keyed by function name, e.g. "/top-level/fold"
function frameRootElemKey(frameRootElem) {
  // Find vb holding the .fun
  const vb = frameRootElem.closest(".vb");
  // Recurse
  const vb_frame_elem = vb && findFrameNoElem(vb);
  const prior_key = (vb_frame_elem && frameRootElemKey(vb_frame_elem)) || "";

  return prior_key + "/" + (vb?.querySelector(".pat")?.innerText || "top-level");
}

function saveFrameNo(frameRootElem) {
  const frameIndex = frameNos(frameRootElem).indexOf(frameRootElem.dataset.activeFrameNo);
  sessionStorage.setItem(frameRootElemKey(frameRootElem), frameIndex);
}

function savedFrameNo(frameRootElem) {
  const frameIndex = sessionStorage.getItem(frameRootElemKey(frameRootElem));
  return frameNos(frameRootElem)[frameIndex];
}

function setFrameNo(frameRootElem, frameNo, skip_relayout) {
  if (autocompleteOpen) { return; } // Don't change frame numbers when an autocomplete is open
  if (frameRootElem.dataset.activeFrameNo === frameNo) { return; } // avoid relayout cost
  frameRootElem.dataset.activeFrameNo = frameNo;
  saveFrameNo(frameRootElem);
  for (child of frameRootElem.children) { updateActiveValues(child, frameNo) }
  if (!skip_relayout) { relayout(); };
}

function initFrameNos() {
  document.querySelectorAll(".fun").forEach(frameNoElem => {
    const priorFrameNo = savedFrameNo(frameNoElem);
    const frameNo = priorFrameNo || frameNoElem.querySelector("[data-frame-no]")?.dataset?.frameNo;
    if (frameNo) { setFrameNo(frameNoElem, frameNo, true); }
  });
  relayout();
}

// Returns whether any any descendent values are active
function updateActiveValues(elem, frameNo) {
  let active = false;

  if (elem.classList.contains("fun")) {
    // Stop recursing, new set of nested lambdas
  } else if ("frameNo" in elem.dataset) {
    if (parseInt(elem.dataset.frameNo) === parseInt(frameNo)) {
      elem.classList.remove("not-in-active-frame");
      active = true;
    } else {
      elem.classList.add("not-in-active-frame");
    }
  } else {
    for (child of elem.children) { active = updateActiveValues(child, frameNo) || active; }

    if (elem.classList.contains("tv")) {
      if (active) {
        elem.classList.remove("not-in-active-frame");
      } else {
        elem.classList.add("not-in-active-frame");
      }
    }
  }

  return active;
}

window.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll("[data-frame-no]").forEach(elem => {
    elem.addEventListener("click", event => {
      const frameNoElem = findFrameNoElem(elem);
      if (frameNoElem) { setFrameNo(frameNoElem, elem.dataset.frameNo); updateTooltip(event); event.stopImmediatePropagation() }
    });
  });

  // Change frame when hovering a tv with no visible values
  document.querySelectorAll(".tv").forEach(elem => {
    elem.addEventListener("click", event => {
      const tvValues = elem.querySelectorAll(":scope > .values > [data-frame-no]");
      const visibleValues = Array.from(tvValues).filter(elem => !elem.classList.contains("not-in-active-frame"));
      if (visibleValues.length == 0 && tvValues.length > 0) {
        let valueToShow = tvValues[0];
        const frameNoElem = findFrameNoElem(valueToShow);
        if (frameNoElem) { setFrameNo(frameNoElem, valueToShow.dataset.frameNo); updateTooltip(event); event.stopImmediatePropagation() }
      }
    });
  });

  initFrameNos();
});



/////////////////// Deletion ///////////////////

function isDeletable(elem) {
  return (elem.classList.contains("vb") || elem.classList.contains("exp")) && (elem.dataset.loc || elem.dataset.inPlaceEditLoc);
}

function deleteElem(elem) {
  deleteLoc(elem.dataset.loc || elem.dataset.inPlaceEditLoc);
}

document.addEventListener("keydown", function(event) {
  if (event.key === "Backspace" || event.key === "Delete") {
    const elem = document.querySelector('.vb.selected,.exp.selected,.scrutinee.selected');
    if (elem) {
      deleteElem(elem);
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



/////////////////// Pretty trees ///////////////////

function removeTreeEdges() {
  document.querySelectorAll(".tree-edge").forEach(svg => svg.remove());
}
// Call removeTreeEdges first.
function redrawTreeEdges() {
  function line(x1, y1, x2, y2) {
    const baseX = Math.min(x1, x2) - 2;
    const baseY = Math.min(y1, y2) - 2;
    const svg  = document.createElementNS("http://www.w3.org/2000/svg", "svg");
    const line = document.createElementNS("http://www.w3.org/2000/svg", "line");
    line.setAttribute("stroke", "black");
    line.setAttribute("stroke-width", "1");
    line.setAttribute("x1", x1 - baseX);
    line.setAttribute("x2", x2 - baseX);
    line.setAttribute("y1", y1 - baseY);
    line.setAttribute("y2", y2 - baseY);
    svg.appendChild(line);
    svg.style.position = "absolute";
    svg.style.left = `${baseX}px`;
    svg.style.top = `${baseY}px`;
    svg.classList.add("tree-edge");
    svg.style.width  = `${Math.max(x1, x2) - baseX + 2}px`;
    svg.style.height = `${Math.max(y1, y2) - baseY + 2}px`;
    return svg;
  }
  // console.log("redraw edges");
  document.querySelectorAll(".tree-kids").forEach(kidsTable => {
    const parent = kidsTable.previousElementSibling;
    const root   = parent.parentElement;
    // const parentRect = parent.getBoundingClientRect();
    const x1 = parent.offsetLeft + parent.offsetWidth/2;
    const y1 = parent.offsetTop + parent.offsetHeight - 1;

    kidsTable.querySelectorAll(":scope > tbody > tr > td").forEach(child => {
      // const childRect = child.getBoundingClientRect();
      const x2 = child.offsetLeft + child.offsetWidth/2;
      const y2 = child.offsetTop + 5;
      // console.log(x1,y1,x2,y2);
      root.insertBefore(line(x1,y1,x2,y2), root.children[0]);
    });
  });
}


/////////////////// Tooltips ///////////////////


tooltipDiv = undefined;
tooltipStack = [];

function updateTooltip(event) {
  if (tooltipStack[0] && !tooltipStack[0].closest(".not-in-active-frame")) { /* Don't show tooltip if the hovered element is no in an active execution frame. */
    tooltipDiv.style.left = `${event.pageX - 10}px`;
    tooltipDiv.style.top  = `${event.pageY - 30}px`;
    tooltipDiv.innerText = tooltipStack[0].dataset.extractionCode.replaceAll(/\s+/g," ");
    show(tooltipDiv);
  } else {
    hide(tooltipDiv);
  }
}

window.addEventListener('DOMContentLoaded', () => {
  tooltipDiv = document.getElementById("tooltip");

  hide(tooltipDiv);

  document.querySelectorAll('[data-extraction-code]:not(.tool):not(.exp)').forEach(elem => {
    // console.log(elem);
    // elem.draggable = true;
    // elem.addEventListener("dragstart", dragstart);
    // elem.addEventListener("dragend", dragend);
    elem.addEventListener("mouseenter", event => {
      tooltipStack.unshift(elem);
      updateTooltip(event);
    });
    elem.addEventListener("mouseleave", event => {
      tooltipStack.removeAsSet(elem);
      updateTooltip(event);
    });
  });
});
