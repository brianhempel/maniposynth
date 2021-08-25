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

function replaceLoc(loc, code) {
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

function insertCode(loc, code) {
  doAction([
    "InsertCode",
    loc,
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
  // console.log(dropTarget, droppedVTrace);
  // if (dropTarget.classList.contains("vbs") && droppedVTrace) {
  //   dropValueIntoVbs(dropTarget.dataset.loc, droppedVTrace);
  // } else if (dropTarget.classList.contains("exp") && droppedVTrace) {
  //   dropValueIntoExp(dropTarget.dataset.inPlaceEditLoc, droppedVTrace);
  if (dropTarget.classList.contains("vbs") && droppedExtractionCode) {
    insertCode(dropTarget.dataset.loc, droppedExtractionCode);
  } else if (dropTarget.classList.contains("exp") && droppedExtractionCode) {
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
  document.querySelectorAll('.vbs,.exp[data-in-place-edit-loc]').forEach(elem => {
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
  selectInspectorTextbox();
}

function deselect(elem) {
  elem.classList.remove("selected");
  saveSelection();
  updateInspector();
}

function deselectAll() {
  selectedElems().forEach(deselect);
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
    if (transientTextboxes().length > 0) {
      transientTextboxes().forEach(abortTextEdit);
    } else if (selectedElems().length > 0) {
      deselectAll();
    } else {
      // document.location.reload();
    }
  }

  document.querySelectorAll('.vbs').forEach(elem => {
    elem.addEventListener("click", globalEscape);
  });
  // Make appropriate items selectable.
  document.querySelectorAll('[data-extraction-code],.vb,.exp[data-in-place-edit-loc],[code-to-assert-on]').forEach(elem => {
    elem.classList.add("selectable");
    elem.addEventListener("click", toggleSelect);
  });
  document.addEventListener("keydown", event => {
    if (event.key === "Esc" || event.key === "Escape") {
      globalEscape();
      event.stopImmediatePropagation();
    }
  });

  // restoreSelection();
});


/////////////////// Suggestions ///////////////////

// The Inspector code later also displays filling suggestions.

function elemSuggestions(elem) {
  return elem.dataset.suggestions?.split("  ") || [];
}

function useSuggestionNumber(elem, i) {
  replaceLoc(elem.dataset.inPlaceEditLoc, elemSuggestions(elem)[i-1]);
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

function textboxKeydownHandler(handleSubmit) {
  return function (event) {
    let textbox = event.currentTarget;
    if (event.key === "Enter" && textbox.value) {
      const elem = selectedElems()[0];
      if (textbox.targetElem) {
        handleSubmit(textbox.targetElem, textbox.value);
      }
    } else if (event.key === "Esc" || event.key === "Escape") {
      textbox.value = textbox.originalValue || "";
      textbox.blur();
      delete textbox.targetElem;
    }
    event.stopImmediatePropagation();
  };
}

window.addEventListener('DOMContentLoaded', () => {
  window.inspector = document.getElementById("inspector");

  document.getElementById("exps-textbox").addEventListener("keydown", textboxKeydownHandler((targetElem, text) => {
    const vis = text;
    addVis(containingLoc(targetElem), vis);
  }));

  document.getElementById("node-textbox").addEventListener("keydown", textboxKeydownHandler((targetElem, text) => {
    replaceLoc(targetElem.dataset.inPlaceEditLoc, text);
  }));

  document.getElementById("root-node-textbox").addEventListener("keydown", textboxKeydownHandler((targetElem, text) => {
    replaceLoc(targetElem.dataset.inPlaceEditLoc, text);
  }));

  document.getElementById("assert-textbox").addEventListener("keydown", textboxKeydownHandler((targetElem, text) => {
    newAssert(containingLoc(targetElem), targetElem.dataset.codeToAssertOn, text);
  }));

  window.addEventListener("resize", updateInspector);
  window.addEventListener("scroll", updateInspector);

  updateInspector();
});

function selectInspectorTextbox() {
  let found = false;
  window.inspector.querySelectorAll("input[type=text]").forEach(textbox => {
    if (!found) {
      if (selfAndParents(textbox).every(isShown)) {
        found = true;
        textbox.select();
      }
    }
  });
}

function updateInspector() {
  const inspector              = window.inspector;
  const textEditPane           = document.getElementById("text-edit-pane");
  const textEditRootStuff      = document.getElementById("text-edit-root-stuff");
  const rootNodeTextbox        = document.getElementById("root-node-textbox");
  const nodeTextbox            = document.getElementById("node-textbox");
  const assertPane             = document.getElementById("assert-pane");
  const assertOn               = document.getElementById("assert-on");
  const assertTextbox          = document.getElementById("assert-textbox");
  const typeOfSelected         = document.getElementById("type-of-selected");
  const expsList               = document.getElementById("exps-list");
  const suggestionsForSelected = document.getElementById("suggestions-for-selected");
  const expsPane               = document.getElementById("exps-pane");
  const suggestionsPane        = document.getElementById("suggestions-pane");
  const addVisTextbox          = document.getElementById("exps-textbox");

  const elem = selectedElems()[0];

  const makeExpRow = (vis, isVised) => {
    const label = document.createElement("label");
    const checkbox = document.createElement("input");
    checkbox.type = "checkbox";
    checkbox.checked = isVised;
    label.appendChild(checkbox);
    label.appendChild(document.createTextNode("Visualize"));
    checkbox.addEventListener("change", ev => {
      const loc = containingLoc(elem);
      if (checkbox.checked) {
        addVis(loc, vis);
      } else {
        removeVis(loc, vis);
      }
    });

    const row = document.createElement("div");
    row.classList.add("exp-row");
    row.appendChild(document.createTextNode(vis));
    row.appendChild(label);
    const addButton = document.createElement("button");
    addButton.innerText = "Add"
    addButton.addEventListener("click", ev => {
      const vbsHolder = vbsHolderForInsert(elem);
      const code = `${vis} (${elem.dataset.extractionCode})`;
      insertCode(vbsHolder.dataset.loc, code);
    });
    row.appendChild(addButton);
    return row;
  }

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

  if (elem && transientTextboxes().length === 0) {
    const rect = elem.getBoundingClientRect();
    const viewWidth =
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
      for (const parent of selfAndParents(elem)) {
        if (parent.dataset.inPlaceEditLoc) {
          rootNodeElem = parent;
        } else {
          break;
        }
      }
      const rootNodeCode            = rootNodeElem?.dataset?.inPlaceEditCode || rootNodeElem?.innerText;
      rootNodeTextbox.value         = rootNodeCode;
      rootNodeTextbox.originalValue = rootNodeCode;
      rootNodeTextbox.targetElem    = rootNodeElem;
      const nodeCode                = elem.dataset.inPlaceEditCode || elem.innerText;
      nodeTextbox.value             = nodeCode;
      nodeTextbox.originalValue     = nodeCode;
      nodeTextbox.targetElem        = elem;
      if (rootNodeElem === elem) { hide(textEditRootStuff); } else { show(textEditRootStuff); }
      show(textEditPane);
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
    suggestionsForSelected.innerHTML = "";
    expsList.innerHTML = "";
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
      addVisTextbox.targetElem = elem;
      show(expsPane);
      const activeVises   = (elem.dataset.activeVises || "").split("  ").removeAsSet("");
      const possibleVises = (elem.dataset.possibleVises || "").split("  ").removeAsSet("");
      activeVises.forEach(vis => expsList.appendChild(makeExpRow(vis, true)));
      possibleVises.forEach(vis => {
        if (!activeVises.includes(vis)) {
          expsList.appendChild(makeExpRow(vis, false));
        }
      });
    } else {
      hide(expsPane);
    }
  } else {
    hide(inspector);
  }
}


/////////////////// Text Editing ///////////////////

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
  textbox.remove();
  textbox.autocompleteDiv?.remove();
  decolorizeSubvalues();
  updateInspector();
}

function colorizeSubvalues() {
  let hue = 30;
  document.querySelectorAll(".value").forEach(elem => {
    elem.style.color = `hsl(${hue}, 90%, 40%)`;
    hue = (hue + 152) % 360;
  });
}
function decolorizeSubvalues() {
  document.querySelectorAll(".value[data-extraction-code]:not(.not-in-active-frame)").forEach(elem => {
    elem.style.color = null;
  });
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

function beginNewCodeEdit(vbsHolder) {
  return function (event) {
    colorizeSubvalues();

    if (event.target !== vbsHolder) { return; }
    event.stopImmediatePropagation();
    const textboxDiv = document.createElement("div");
    textboxDiv.contentEditable = true;
    textboxDiv.classList.add("transient-textbox");
    textboxDiv.classList.add("textbox");
    textboxDiv.style.position = "absolute";
    // textboxDiv.style.backgroundColor = "white";
    const { dx, dy } = topLeftOffsetFromMouse(vbsHolder, event)
    textboxDiv.style.left = `${-dx - 5}px`;
    textboxDiv.style.top  = `${-dy - 10}px`;
    vbsHolder.appendChild(textboxDiv);

    const autocompleteDiv = document.createElement("div");
    autocompleteDiv.classList.add("autocomplete-options");
    autocompleteDiv.style.position = "absolute";
    autocompleteDiv.style.left = textboxDiv.style.left;
    autocompleteDiv.style.top  = `${textboxDiv.offsetTop + textboxDiv.offsetHeight}px`;
    vbsHolder.appendChild(autocompleteDiv);

    textboxDiv.autocompleteDiv = autocompleteDiv;
    textboxDiv.focus();

    // START HERE offer all visible values as autocomplete blobs
    const options = Array.from(document.querySelectorAll(".value[data-extraction-code]:not(.not-in-active-frame)")).filter(isShown);

    // START HERE
    // 1. can't delete in autocomplete
    // 2. autocomplete wraps :( :( :(

    textboxDiv.addEventListener('keydown', event => {
      // console.log(event.key);
      if (event.key === "Enter") {
        if (textboxDiv.innerText.length > 0) {
          let code = "";
          // Convert autocompleted values to code
          for (child of textboxDiv.childNodes) {
            if (child.nodeType === 3) {
              // Text node
              code += child.data;
            } else {
              // value node
              code += `(${child.dataset.extractionCode})`
            }
          }
          insertCode(vbsHolder.dataset.loc, code);
          event.stopImmediatePropagation(); /* does this even do anything? */
          event.preventDefault(); /* Don't insert a newline character */
        }
      } else if (event.key === "Esc" || event.key === "Escape") {
        abortTextEdit(textboxDiv);
      } else if (event.key === "ArrowDown") {
        textboxDiv.blur();
        autocompleteDiv.children[0]?.focus();
        event.preventDefault();
      } else if (event.key === "ArrowUp") {
        textboxDiv.blur();
        autocompleteDiv.children[autocompleteDiv.children.length - 1]?.focus();
        event.preventDefault();
      }
      // event.stopImmediatePropagation();
    }, { capture: true }); /* Run this handler befooooorrre the typing happens */
    textboxDiv.addEventListener('keyup', _ => { updateAutocomplete(textboxDiv, options, autocompleteDiv) });
    // Prevent click on elem from bubbling to the global deselect/abort handler
    textboxDiv.addEventListener('click', event => {
      event.stopPropagation();
    });
  }
}

// https://stackoverflow.com/a/17323608
function mod(n, m) {
  return ((n % m) + m) % m;
}

function updateAutocomplete(textboxDiv, options, optionsDiv) {
  // let options = [text];
  optionsDiv.innerHTML = "";
  for (const option of options) {
    const optionDiv = document.createElement("div");
    // optionDiv.innerText = option;
    const optionClone = option.cloneNode(true);
    optionClone.tabIndex = 0; /* Make element focusable, even though below we override tab */
    optionClone.addEventListener('keydown', event => {
      let focusedOptionIdx = -1;
      for (i in optionsDiv.children) {
        if (document.activeElement === optionsDiv.children[i]) {
          focusedOptionIdx = parseInt(i);
        }
      }
      console.log(optionsDiv.children.length);
      console.log(focusedOptionIdx);
      console.log(focusedOptionIdx + 1);
      console.log(mod(focusedOptionIdx + 1, optionsDiv.children.length));
      if (event.key === "ArrowDown") {
        optionsDiv.children[mod(focusedOptionIdx + 1, optionsDiv.children.length)].focus();
        event.stopImmediatePropagation();
        event.preventDefault();
      } else if (event.key === "ArrowUp") {
        optionsDiv.children[mod(focusedOptionIdx - 1, optionsDiv.children.length)].focus();
        event.stopImmediatePropagation();
        event.preventDefault();
      } else if (event.key === "Enter" || event.key === "Tab") {
        optionClone.remove();
        optionClone.contentEditable = false;
        textboxDiv.appendChild(optionClone);
        optionsDiv.innerHTML = "";
        // label.appendChild(document.createTextNode("Visualize"));
        textboxDiv.focus()
        // Set cursor to end of "input" element
        window.getSelection().selectAllChildren(textboxDiv);
        window.getSelection().collapseToEnd();
        event.stopImmediatePropagation();
        event.preventDefault();
      }
    }, { capture: true }); /* Run handler beefoooore it triggers a scroll */
    optionsDiv.appendChild(optionClone);
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

window.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll("[data-insert-code]").forEach(elem => {
    elem.addEventListener("click", _ => {
      const selected = selectedElems()[0] || document.querySelector(".top-level");
      console.log(selected);
      console.log(vbsHolderForInsert(selected));
      insertCode(vbsHolderForInsert(selected).dataset.loc, elem.dataset.insertCode);
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
  if (dropTarget && isStartingVbs(dropTarget, window.stuffMoving.elem)) {
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
        event.stopImmediatePropagation();
      }
    });
  });
});

// Make sure each vbs holder has place for all the vbs
// Resize deepest first.
const vb_margin_bottom = 20;
function resizeVbHolders(elem) {
  const vbsHolders = elem.querySelectorAll(".vbs");
  const minVbHolderHeight = 70;
  vbsHolders.forEach(vbsHolder => {
    if (vbsHolder.classList.contains("top-level")) { return; }
    // console.log(vbsHolder.children);
    let maxWidth = 0;
    let maxHeight = 0;
    for (box of vbsHolder.children) {
      if (!box.classList.contains("vb")) { continue; } /* Skip transient textboxes in the vbs elem */
      resizeVbHolders(box);
      maxWidth  = Math.max(maxWidth, box.offsetLeft + box.offsetWidth);
      maxHeight = Math.max(maxHeight, box.offsetTop + box.offsetHeight + vb_margin_bottom);
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
function reflowUnpositionedElems(elem) {
  const vbsHolders = elem.querySelectorAll(".vbs");
  function left(box)  { return box.offsetLeft; }
  function top(box)   { return box.offsetTop; }
  function right(box) { return box.offsetLeft + box.offsetWidth; }
  function bot(box)   { return box.offsetTop + box.offsetHeight + vb_margin_bottom; }
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
      if (!box.classList.contains("vb")) { continue; } /* Skip transient textboxes in the vbs elem */
      if (!placedBoxes.includes(box)) {
        box.style.left = `10px`
        let top = 10;
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
function relayout() {
  resizeVbHolders(document);
  reflowUnpositionedElems(document);
}
window.addEventListener('DOMContentLoaded', () => {
  relayout();
  relayout();
  relayout();
  relayout();
});



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


function findFrameNoElem(elem) {
  return elem.closest(".fun");
}

function setFrameNo(frameRootElem, frameNo) {
  frameRootElem.dataset.activeFrameNo = frameNo;
  for (child of frameRootElem.children) { updateActiveValues(child, frameNo) }
}

function initFrameNos() {
  document.querySelectorAll(".fun").forEach(frameNoElem => {
    const frameNo = frameNoElem.querySelector("[data-frame-no]")?.dataset?.frameNo;
    if (frameNo) { setFrameNo(frameNoElem, frameNo); }
  });
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

  relayout();
}

window.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll("[data-frame-no]").forEach(elem => {
    elem.addEventListener("mouseenter", event => {
      const frameNoElem = findFrameNoElem(elem);
      if (frameNoElem) { setFrameNo(frameNoElem, elem.dataset.frameNo); }
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
    const elem = document.querySelector('.vb.selected,.exp.selected')
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
