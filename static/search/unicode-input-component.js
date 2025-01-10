// @ts-check

/**
 * This is copied from `https://github.com/leanprover/vscode-lean4/blob/master/lean4-unicode-input-component/src/index.ts`
 * but modified to work without compilation, and with an input element instead of a contenteditable div. This loses the
 * underlining that the original had, but allows us to keep using an input element.
 */

import {
  AbbreviationProvider,
  AbbreviationRewriter,
  Range,
} from "./unicode-input.min.js";

/**
 * @typedef {any} AbbreviationConfig
 * @typedef {any} SelectionMoveMode
 * @typedef {any} Range
 * @typedef {any} Change
 */

/**
 * @param {Node} searchNode
 * @param {Node} target
 * @param {number} offsetInTarget
 * @returns {number | undefined}
 */
function computeTextOffsetFromNodeOffset(searchNode, target, offsetInTarget) {
  if (searchNode === target) {
    return offsetInTarget;
  }
  if (!searchNode.contains(target)) {
    return undefined;
  }

  let totalOffset = 0;
  for (const childNode of Array.from(searchNode.childNodes)) {
    const childOffset = computeTextOffsetFromNodeOffset(
      childNode,
      target,
      offsetInTarget
    );
    if (childOffset !== undefined) {
      totalOffset += childOffset;
      return totalOffset;
    }
    totalOffset += childNode.textContent?.length ?? 0;
  }
  return undefined;
}

/**
 * @param {Node} searchNode
 * @param {{ node: Node; offset: number } | undefined} rangeStart
 * @param {{ node: Node; offset: number } | undefined} rangeEnd
 * @returns {Range | undefined}
 */
function computeTextRangeFromNodeRange(searchNode, rangeStart, rangeEnd) {
  /** @var {number | undefined} */
  let start;
  /** @var {number | undefined} */
  let end;
  if (rangeStart) {
    start = computeTextOffsetFromNodeOffset(
      searchNode,
      rangeStart.node,
      rangeStart.offset
    );
  }
  if (rangeEnd) {
    end = computeTextOffsetFromNodeOffset(
      searchNode,
      rangeEnd.node,
      rangeEnd.offset
    );
  }

  if (start === undefined) {
    if (end === undefined) {
      return undefined;
    } else {
      return new Range(end, 0);
    }
  } else {
    if (end === undefined) {
      return new Range(start, 0);
    } else {
      if (end < start) {
        [start, end] = [end, start];
      }
      return new Range(start, end - start);
    }
  }
}

/**
 * @param {Node} searchNode
 * @returns {Range | undefined}
 */
function findTextCursorSelection(searchNode) {
  const sel = window.getSelection();
  if (sel === null) {
    return undefined;
  }

  /** @var {{ node: Node; offset: number } | undefined} */
  let rangeStart;
  if (sel.anchorNode) {
    rangeStart = { node: sel.anchorNode, offset: sel.anchorOffset };
  }
  /** @var {{ node: Node; offset: number } | undefined} */
  let rangeEnd;
  if (sel.focusNode) {
    rangeStart = { node: sel.focusNode, offset: sel.focusOffset };
  }

  return computeTextRangeFromNodeRange(searchNode, rangeStart, rangeEnd);
}

/**
 * @param {Node} searchNode
 * @param {number} offset
 * @returns {{ found: true; node: Node; offset: number } | { found: false; remainingOffset: number }}
 */
function computeNodeOffsetFromTextOffset(searchNode, offset) {
  const childNodes = Array.from(searchNode.childNodes);
  if (childNodes.length === 0) {
    const textContentLength = searchNode.textContent?.length ?? 0;
    if (offset > textContentLength) {
      return { found: false, remainingOffset: offset - textContentLength };
    }
    return { found: true, node: searchNode, offset };
  }
  for (const childNode of Array.from(searchNode.childNodes)) {
    const result = computeNodeOffsetFromTextOffset(childNode, offset);
    if (result.found) {
      return result;
    }
    offset = /** @type {any} */ (result).remainingOffset;
  }
  return { found: false, remainingOffset: offset };
}

/**
 *
 * @param {Node} searchNode
 * @param {number} offset
 * @returns {void}
 */
function setTextCursorSelection(searchNode, offset) {
  const result = computeNodeOffsetFromTextOffset(searchNode, offset);
  if (!result.found) {
    return;
  }

  const sel = window.getSelection();
  if (sel === null) {
    return;
  }

  const range = document.createRange();
  range.setStart(result.node, result.offset);
  range.collapse(true);
  sel.removeAllRanges();
  sel.addRange(range);
}

/**
 *
 * @param {string} str
 * @param {{ range: Range; update: (old: string) => string }[]} updates
 * @returns {string}
 */
function replaceAt(str, updates) {
  updates.sort((u1, u2) => u1.range.offset - u2.range.offset);
  let newStr = "";
  let lastUntouchedPos = 0;
  for (const u of updates) {
    newStr += str.slice(lastUntouchedPos, u.range.offset);
    newStr += u.update(str.slice(u.range.offset, u.range.offsetEnd + 1));
    lastUntouchedPos = u.range.offset + u.range.length;
  }
  newStr += str.slice(lastUntouchedPos);
  return newStr;
}

export class InputAbbreviationRewriter {
  /** @type {AbbreviationRewriter} */
  rewriter;

  /** @type {boolean} */
  isInSelectionChange = false;

  /** @type {AbbreviationConfig} */
  config;

  /** @type {HTMLInputElement} */
  textInput;

  /**
   * @param {AbbreviationConfig} config
   * @param {HTMLInputElement} textInput
   */
  constructor(config, textInput) {
    this.config = config;
    this.textInput = textInput;

    const provider = new AbbreviationProvider(config);
    this.rewriter = new AbbreviationRewriter(config, provider, this);

    textInput.addEventListener("beforeinput", async (inputEvent) => {
      const range = new Range(this.getInput().length, 0);
      const newText = inputEvent.data ?? "";
      const change = { range, newText };
      this.rewriter.changeInput([change]);
    });

    textInput.addEventListener("input", async (_) => {
      await this.rewriter.triggerAbbreviationReplacement();
      await this.updateSelection();
      this.updateState();
    });

    document.addEventListener("selectionchange", async () => {
      // This happens when updating the state itself triggers a selection change.
      if (this.isInSelectionChange) {
        return;
      }
      this.isInSelectionChange = true;
      await this.updateSelection();
      this.updateState();
      this.isInSelectionChange = true;
    });

    textInput.addEventListener("keydown", async (ev) => {
      if (ev.key === "Tab") {
        await this.rewriter.replaceAllTrackedAbbreviations();
        this.updateState();
        ev.preventDefault();
      }
    });
  }

  resetAbbreviations() {
    this.rewriter.resetTrackedAbbreviations();
    this.updateState();
  }

  async updateSelection() {
    const selection = this.getSelection();
    if (selection === undefined) {
      return;
    }
    await this.rewriter.changeSelections([selection]);
  }

  /**
   * @returns {Range | undefined}
   */
  getSelection() {
    return findTextCursorSelection(this.textInput);
  }

  updateState() {
    const query = this.getInput();
    const queryHtml = this.textInput.innerHTML;
    const updates = Array.from(this.rewriter.getTrackedAbbreviations()).map(
      (a) => ({
        range: a.range,
        update: (/** @type {string} */ old) => `${old}`,
      })
    );
    const newQueryHtml = replaceAt(query, updates);
    if (queryHtml === newQueryHtml) {
      return;
    }
    const selectionBeforeChange = this.getSelection();
    this.setInputHTML(newQueryHtml);
    if (selectionBeforeChange !== undefined) {
      this.setSelections([selectionBeforeChange]);
    }
  }

  /**
   * @param {Change[]} changes
   * @returns {Promise<boolean>}
   */
  async replaceAbbreviations(changes) {
    /** @type {{ range: Range; update: (old: string) => string }[]} */
    const updates = changes.map((c) => ({
      range: c.range,
      update: (_) => c.newText,
    }));
    this.setInputHTML(replaceAt(this.getInput(), updates));
    return true;
  }

  /**
   * @return {SelectionMoveMode}
   */
  selectionMoveMode() {
    return { kind: "MoveAllSelections" };
  }

  /**
   * @return {Range[]}
   */
  collectSelections() {
    const selection = this.getSelection();
    if (selection === undefined) {
      return [];
    }
    return [selection];
  }

  /**
   *
   * @param {Range[]} selections
   * @returns {void}
   */
  setSelections(selections) {
    const primarySelection = selections[0];
    if (primarySelection === undefined) {
      return;
    }
    setTextCursorSelection(this.textInput, primarySelection.offset);
  }

  /**
   * @param {string} html
   */
  setInputHTML(html) {
    this.textInput.value = html;
  }

  /**
   * @returns {string}
   */
  getInput() {
    return this.textInput.value;
  }
}
