// Enable typescript
// @ts-check

import { InputAbbreviationRewriter } from "./unicode-input-component.js";

// Hacky way to import the fuzzysort library and get the types working. It's just `window.fuzzysort`.
const fuzzysort = /** @type {{fuzzysort: Fuzzysort.Fuzzysort}} */ (
  /** @type {unknown} */ (window)
).fuzzysort;

/**
 * Type definitions to help if you have typescript enabled.
 *
 * @typedef {{searchKey: string, address: string, domainId: string, ref?: any}} Searchable
 * @typedef {(domainData: any) => Searchable[]} DomainDataToSearchables
 * @typedef {{t: 'text', v: string} | {t: 'highlight', v: string}} MatchedPart
 * @typedef {(searchable: Searchable, matchedParts: MatchedPart[], document: Document) => HTMLElement} CustomResultRender
 * @typedef {{dataToSearchables: DomainDataToSearchables, customRender?: CustomResultRender, displayName: string, className: string}} DomainMapper
 * @typedef {Record<string, DomainMapper>} DomainMappers
 * @typedef {{item: Searchable, fuzzysortResult: Fuzzysort.Result, htmlItem: HTMLLIElement}} SearchResult
 */

/**
 * Maps data from Lean to an object with search terms as keys and a list of results as values.
 *
 * @param {any} json
 * @param {DomainMappers} domainMappers
 * @return {Record<string, Searchable[]>}
 */
const dataToSearchableMap = (json, domainMappers) =>
  Object.entries(json)
    .flatMap(([key, value]) =>
      key in domainMappers
        ? domainMappers[key].dataToSearchables(value)
        : undefined
    )
    .reduce((acc, cur) => {
      if (cur == null) {
        return acc;
      }

      if (!acc.hasOwnProperty(cur.searchKey)) {
        acc[cur.searchKey] = [];
      }
      acc[cur.searchKey].push(cur);
      return acc;
    }, {});

/**
 * Maps from a data item to a HTML LI element
 *
 * @param {DomainMappers} domainMappers
 * @param {Searchable} searchable
 * @param {MatchedPart[]} matchedParts
 * @param {Document} document
 * @return {HTMLLIElement}
 */
const searchableToHtml = (
  domainMappers,
  searchable,
  matchedParts,
  document
) => {
  const domainMapper = domainMappers[searchable.domainId];

  const li = document.createElement("li");
  li.role = "option";
  li.className = `search-result ${domainMapper.className}`;
  li.title = `${domainMapper.displayName} ${searchable.searchKey}`;

  if (domainMapper.customRender != null) {
    li.appendChild(
      domainMapper.customRender(searchable, matchedParts, document)
    );
  } else {
    const searchTerm = document.createElement("p");
    for (const { t, v } of matchedParts) {
      if (t === "text") {
        searchTerm.append(v);
      } else {
        const emEl = document.createElement("em");
        searchTerm.append(emEl);
        emEl.textContent = v;
      }
    }
    li.appendChild(searchTerm);
  }

  const domainName = document.createElement("p");
  li.appendChild(domainName);
  domainName.className = "domain";
  domainName.textContent = domainMapper.displayName;

  return li;
};

/**
 * @param {SearchResult} result
 * @returns string
 */
const resultToText = (result) => result.fuzzysortResult.target;

/**
 * @template T
 * @template Y
 * @param {T | null | undefined} v
 * @param {(t: T) => Y} fn
 * @returns Y | undefined
 */
const opt = (v, fn) => (v != null ? fn(v) : undefined);

/**
 * This is a modified version of the combobox at https://www.w3.org/WAI/ARIA/apg/patterns/combobox/examples/combobox-autocomplete-both/
 *
 * More documentation to come!
 */
class SearchBox {
  /**
   * @type {HTMLInputElement}
   */
  comboboxNode;

  /**
   * @type {HTMLButtonElement | null}
   */
  buttonNode;

  /**
   * @type {HTMLElement}
   */
  listboxNode;

  /**
   * @type {boolean}
   */
  comboboxHasVisualFocus;

  /**
   * @type {boolean}
   */
  listboxHasVisualFocus;

  /**
   * @type {boolean}
   */
  hasHover;

  /**
   * @type {boolean}
   */
  isNone;

  /**
   * @type {boolean}
   */
  isList;

  /**
   * @type {boolean}
   */
  isBoth;

  /**
   * @type {SearchResult | null}
   */
  currentOption;

  /**
   * @type {SearchResult | null}
   */
  firstOption;

  /**
   * @type {SearchResult | null}
   */
  lastOption;

  /**
   * @type {SearchResult[]}
   */
  filteredOptions;

  /**
   * @type {string}
   */
  filter;

  /**
   * @type {Fuzzysort.Prepared[]}
   */
  preparedData;

  /**
   * Map from search term to list of results
   *
   * @type {Record<string, Searchable[]>}
   */
  mappedData;

  /** @type {HTMLLIElement} */
  noResultsElement = document.createElement("li");

  /** @type {HTMLLIElement[]} */
  domainFilters;

  /** @type {DomainMappers} */
  domainMappers;

  /**
   * @param {HTMLInputElement} comboboxNode
   * @param {HTMLButtonElement | null} buttonNode
   * @param {HTMLElement} listboxNode
   * @param {DomainMappers} domainMappers
   * @param {Record<string, Searchable[]>} mappedData
   */
  constructor(
    comboboxNode,
    buttonNode,
    listboxNode,
    domainMappers,
    mappedData
  ) {
    this.comboboxNode = comboboxNode;
    this.buttonNode = buttonNode;
    this.listboxNode = listboxNode;
    this.domainMappers = domainMappers;
    this.mappedData = mappedData;
    this.preparedData = Object.keys(this.mappedData).map((name) =>
      fuzzysort.prepare(name)
    );

    // Add IME
    new InputAbbreviationRewriter(
      {
        abbreviationCharacter: "\\",
        customTranslations: [],
        eagerReplacementEnabled: true,
      },
      comboboxNode
    );

    this.comboboxHasVisualFocus = false;
    this.listboxHasVisualFocus = false;

    this.hasHover = false;

    this.isNone = false;
    this.isList = false;
    this.isBoth = false;

    this.currentOption = null;
    this.firstOption = null;
    this.lastOption = null;

    this.filteredOptions = [];
    this.filter = "";

    const autocomplete = this.comboboxNode
      .getAttribute("aria-autocomplete")
      ?.toLowerCase();

    if (typeof autocomplete === "string") {
      this.isNone = autocomplete === "none";
      this.isList = autocomplete === "list";
      this.isBoth = autocomplete === "both";
    } else {
      // default value of autocomplete
      this.isNone = true;
    }

    this.comboboxNode.addEventListener(
      "keydown",
      this.onComboboxKeyDown.bind(this)
    );
    this.comboboxNode.addEventListener(
      "keyup",
      this.onComboboxKeyUp.bind(this)
    );
    this.comboboxNode.addEventListener(
      "click",
      this.onComboboxClick.bind(this)
    );
    this.comboboxNode.addEventListener(
      "focus",
      this.onComboboxFocus.bind(this)
    );
    this.comboboxNode.addEventListener("blur", this.onComboboxBlur.bind(this));

    document.body.addEventListener(
      "pointerup",
      this.onBackgroundPointerUp.bind(this),
      true
    );

    // initialize pop up menu

    this.listboxNode.addEventListener(
      "pointerover",
      this.onListboxPointerover.bind(this)
    );
    this.listboxNode.addEventListener(
      "pointerout",
      this.onListboxPointerout.bind(this)
    );

    this.domainFilters = [];
    const docDomainFilter = document.createElement("li");
    docDomainFilter.innerHTML = `<label><input type="checkbox" checked> Doc domain</label>`;
    docDomainFilter.classList.add("domain-filter");
    // TODO more work on the domain filters
    // this.domainFilters.push(docDomainFilter);

    this.filterOptions();

    // Open Button

    const button = this.comboboxNode.nextElementSibling;

    if (button && button.tagName === "BUTTON") {
      button.addEventListener("click", this.onButtonClick.bind(this));
    }

    this.noResultsElement.textContent = "No results";
  }

  /**
   * @param {Element} element
   */
  isElementInView(element) {
    const bounding = element.getBoundingClientRect();
    return (
      bounding.top >= 0 &&
      bounding.left >= 0 &&
      bounding.bottom <=
        (window.innerHeight || document.documentElement.clientHeight) &&
      bounding.right <=
        (window.innerWidth || document.documentElement.clientWidth)
    );
  }

  /**
   * @param {HTMLLIElement | null | undefined} option
   */
  setActiveDescendant(option) {
    if (option && this.listboxHasVisualFocus) {
      this.comboboxNode.setAttribute("aria-activedescendant", option.id);
      if (!this.isElementInView(option)) {
        option.scrollIntoView({ behavior: "smooth", block: "nearest" });
      }
    } else {
      this.comboboxNode.setAttribute("aria-activedescendant", "");
    }
  }

  /**
   * @param {SearchResult} result
   */
  confirmResult(result) {
    window.location.assign(result.item.address);
  }

  /**
   * @param {string} value
   */
  setValue(value) {
    this.filter = value;
    this.comboboxNode.value = this.filter;
    this.comboboxNode.setSelectionRange(this.filter.length, this.filter.length);
    this.filterOptions();
  }

  /**
   * @param {SearchResult} option
   * @param {boolean} [setSelection]
   */
  setOption(option, setSelection) {
    if (option) {
      this.currentOption = option;
      this.setCurrentOptionStyle(this.currentOption);
      this.setActiveDescendant(this.currentOption.htmlItem);

      if (this.isBoth) {
        this.comboboxNode.value = resultToText(this.currentOption);
        if (setSelection) {
          this.comboboxNode.setSelectionRange(
            resultToText(this.currentOption).length,
            resultToText(this.currentOption).length
          );
        } else {
          this.comboboxNode.setSelectionRange(
            this.filter.length,
            resultToText(this.currentOption).length
          );
        }
      }
    }
  }

  setVisualFocusCombobox() {
    this.listboxNode.classList.remove("focus");
    this.comboboxNode.parentElement?.classList.add("focus"); // set the focus class to the parent for easier styling
    this.comboboxHasVisualFocus = true;
    this.listboxHasVisualFocus = false;
    this.setActiveDescendant(null);
  }

  setVisualFocusListbox() {
    this.comboboxNode.parentElement?.classList.remove("focus");
    this.comboboxHasVisualFocus = false;
    this.listboxHasVisualFocus = true;
    this.listboxNode.classList.add("focus");
    this.setActiveDescendant(this.currentOption?.htmlItem);
  }

  removeVisualFocusAll() {
    this.comboboxNode.parentElement?.classList.remove("focus");
    this.comboboxHasVisualFocus = false;
    this.listboxHasVisualFocus = false;
    this.listboxNode.classList.remove("focus");
    this.currentOption = null;
    this.setActiveDescendant(null);
  }

  // ComboboxAutocomplete Events

  filterOptions() {
    // do not filter any options if autocomplete is none
    if (this.isNone) {
      this.filter = "";
    }

    const currentOptionText = opt(this.currentOption, resultToText);
    const filter = this.filter;

    // Empty the listbox
    this.listboxNode.innerHTML = "";

    this.listboxNode.append(...this.domainFilters);

    if (filter.length === 0) {
      this.filteredOptions = [];
      this.firstOption = null;
      this.lastOption = null;
      this.currentOption = null;
      return null;
    }

    const results = fuzzysort.go(filter, this.preparedData, {
      limit: 20,
      threshold: 0.5,
    });

    if (results.length === 0) {
      this.filteredOptions = [];
      this.firstOption = null;
      this.lastOption = null;
      this.currentOption = null;
      this.listboxNode.appendChild(this.noResultsElement);
      return null;
    }

    /**
     * @type {SearchResult|null}
     */
    let newCurrentOption = null;

    for (let i = 0; i < results.length; i++) {
      const result = results[i];
      const dataItems = this.mappedData[result.target];
      for (let j = 0; j < dataItems.length; j++) {
        const searchable = dataItems[j];
        const option = searchableToHtml(
          this.domainMappers,
          dataItems[j],
          result
            .highlight((v) => ({ v }))
            .map((v) =>
              typeof v === "string"
                ? { t: "text", v }
                : { t: "highlight", v: v.v }
            ),
          document
        );
        /** @type {SearchResult} */
        const searchResult = {
          item: searchable,
          fuzzysortResult: result,
          htmlItem: option,
        };

        option.addEventListener("click", this.onOptionClick(searchResult));
        option.addEventListener(
          "pointerover",
          this.onOptionPointerover.bind(this)
        );
        option.addEventListener(
          "pointerout",
          this.onOptionPointerout.bind(this)
        );
        this.filteredOptions.push(searchResult);
        this.listboxNode.appendChild(option);
        if (i === 0 && j === 0) {
          this.firstOption = searchResult;
        }
        if (i === results.length - 1 && j === dataItems.length - 1) {
          this.lastOption = searchResult;
        }
        if (currentOptionText === resultToText(searchResult)) {
          newCurrentOption = searchResult;
        }
      }
    }

    if (newCurrentOption) {
      this.currentOption = newCurrentOption;
    }

    return newCurrentOption ?? this.firstOption;
  }

  /**
   * @param {SearchResult | null} option
   */
  setCurrentOptionStyle(option) {
    for (const opt of this.filteredOptions) {
      const el = opt.htmlItem;
      if (opt === option) {
        el.setAttribute("aria-selected", "true");
        if (
          this.listboxNode.scrollTop + this.listboxNode.offsetHeight <
          el.offsetTop + el.offsetHeight
        ) {
          this.listboxNode.scrollTop =
            el.offsetTop + el.offsetHeight - this.listboxNode.offsetHeight;
        } else if (this.listboxNode.scrollTop > el.offsetTop + 2) {
          this.listboxNode.scrollTop = el.offsetTop;
        }
      } else {
        el.removeAttribute("aria-selected");
      }
    }
  }

  /**
   * @param {SearchResult} currentOption
   * @param {SearchResult} lastOption
   */
  getPreviousOption(currentOption, lastOption) {
    if (currentOption !== this.firstOption) {
      var index = this.filteredOptions.indexOf(currentOption);
      return this.filteredOptions[index - 1];
    }
    return lastOption;
  }

  /**
   * @param {SearchResult | null} currentOption
   * @param {SearchResult} firstOption
   */
  getNextOption(currentOption, firstOption) {
    if (currentOption != null && currentOption !== this.lastOption) {
      var index = this.filteredOptions.indexOf(currentOption);
      return this.filteredOptions[index + 1];
    }
    return firstOption;
  }

  /* MENU DISPLAY METHODS */

  doesOptionHaveFocus() {
    return this.comboboxNode.getAttribute("aria-activedescendant") !== "";
  }

  isOpen() {
    return this.listboxNode.style.display === "block";
  }

  isClosed() {
    return this.listboxNode.style.display !== "block";
  }

  open() {
    this.listboxNode.style.display = "block";
    this.comboboxNode.setAttribute("aria-expanded", "true");
    this.buttonNode?.setAttribute("aria-expanded", "true");
  }

  /**
   * @param {boolean} [force]
   */
  close(force) {
    if (
      force ||
      (!this.comboboxHasVisualFocus &&
        !this.listboxHasVisualFocus &&
        !this.hasHover)
    ) {
      this.setCurrentOptionStyle(null);
      this.listboxNode.style.display = "none";
      this.comboboxNode.setAttribute("aria-expanded", "false");
      this.buttonNode?.setAttribute("aria-expanded", "false");
      this.setActiveDescendant(null);
    }
  }

  /* combobox Events */

  /**
   * @param {KeyboardEvent} event
   * @returns void
   */
  onComboboxKeyDown(event) {
    let eventHandled = false;
    const altKey = event.altKey;

    if (event.ctrlKey || event.shiftKey) {
      return;
    }

    switch (event.key) {
      case "Enter":
        if (this.listboxHasVisualFocus) {
          this.setValue(opt(this.currentOption, resultToText) ?? "");
          if (this.currentOption) {
            this.confirmResult(this.currentOption);
          }
        }
        this.close(true);
        this.setVisualFocusCombobox();
        eventHandled = true;
        break;

      case "Down":
      case "ArrowDown":
        if (this.filteredOptions.length > 0 && this.firstOption != null) {
          if (altKey) {
            this.open();
          } else {
            this.open();
            if (
              this.listboxHasVisualFocus ||
              (this.isBoth && this.filteredOptions.length > 1)
            ) {
              this.setOption(
                this.getNextOption(this.currentOption, this.firstOption),
                true
              );
              this.setVisualFocusListbox();
            } else {
              this.setOption(this.firstOption, true);
              this.setVisualFocusListbox();
            }
          }
        }
        eventHandled = true;
        break;

      case "Up":
      case "ArrowUp":
        if (
          this.filteredOptions.length > 0 &&
          this.currentOption != null &&
          this.lastOption != null
        ) {
          if (this.listboxHasVisualFocus) {
            this.setOption(
              this.getPreviousOption(this.currentOption, this.lastOption),
              true
            );
          } else {
            this.open();
            if (!altKey) {
              this.setOption(this.lastOption, true);
              this.setVisualFocusListbox();
            }
          }
        }
        eventHandled = true;
        break;

      case "Esc":
      case "Escape":
        if (this.isOpen()) {
          this.close(true);
          this.filter = this.comboboxNode.value;
          this.filterOptions();
          this.setVisualFocusCombobox();
        } else {
          this.setValue("");
          this.comboboxNode.value = "";
        }
        this.option = null;
        eventHandled = true;
        break;

      case "Tab":
        this.close(true);
        break;

      case "Home":
        this.comboboxNode.setSelectionRange(0, 0);
        eventHandled = true;
        break;

      case "End":
        var length = this.comboboxNode.value.length;
        this.comboboxNode.setSelectionRange(length, length);
        eventHandled = true;
        break;

      default:
        break;
    }

    if (eventHandled) {
      event.stopImmediatePropagation();
      event.preventDefault();
    }
  }

  /**
   * @param {string} str
   */
  isPrintableCharacter(str) {
    return str.length === 1 && str.match(/\S| /);
  }

  /**
   * @param {KeyboardEvent} event
   * @returns void
   */
  onComboboxKeyUp(event) {
    let eventHandled = false;
    const char = event.key;

    if (this.isPrintableCharacter(char)) {
      this.filter += char;
    }

    // this is for the case when a selection in the textbox has been deleted
    if (this.comboboxNode.value.length < this.filter.length) {
      this.filter = this.comboboxNode.value;
      this.option = null;
      this.filterOptions();
    }

    if (event.key === "Escape" || event.key === "Esc") {
      return;
    }

    switch (event.key) {
      case "Backspace":
        this.setVisualFocusCombobox();
        this.setCurrentOptionStyle(null);
        this.filter = this.comboboxNode.value;
        this.option = null;
        this.filterOptions();
        eventHandled = true;
        break;

      case "Left":
      case "ArrowLeft":
      case "Right":
      case "ArrowRight":
      case "Home":
      case "End":
        if (this.isBoth) {
          this.filter = this.comboboxNode.value;
        } else {
          this.option = null;
          this.setCurrentOptionStyle(null);
        }
        this.setVisualFocusCombobox();
        eventHandled = true;
        break;

      default:
        if (this.isPrintableCharacter(char)) {
          this.setVisualFocusCombobox();
          this.setCurrentOptionStyle(null);
          eventHandled = true;

          if (this.isList || this.isBoth) {
            const option = this.filterOptions();
            if (option) {
              if (this.isClosed() && this.comboboxNode.value.length) {
                this.open();
              }

              this.option = option;
              if (this.isBoth || this.isList || this.listboxHasVisualFocus) {
                this.setCurrentOptionStyle(option);
                if (this.isBoth || this.isList) {
                  this.setOption(option);
                }
              }
            } else {
              this.close();
              this.option = null;
              this.setActiveDescendant(null);
            }
          } else if (this.comboboxNode.value.length) {
            this.open();
          }
        }

        break;
    }

    if (eventHandled) {
      event.stopPropagation();
      event.preventDefault();
    }
  }

  onComboboxClick() {
    if (this.isOpen()) {
      this.close(true);
    } else {
      this.open();
    }
  }

  onComboboxFocus() {
    this.filter = this.comboboxNode.value;
    this.filterOptions();
    this.setVisualFocusCombobox();
    this.option = null;
    this.setCurrentOptionStyle(null);
  }

  onComboboxBlur() {
    this.removeVisualFocusAll();
  }

  /**
   * @param {PointerEvent} event
   * @returns void
   */
  onBackgroundPointerUp(event) {
    const node = /** @type {Node | null} */ (event.target);
    if (
      !this.comboboxNode.contains(node) &&
      !this.listboxNode.contains(node) &&
      (this.buttonNode == null || !this.buttonNode.contains(node))
    ) {
      this.comboboxHasVisualFocus = false;
      this.setCurrentOptionStyle(null);
      this.removeVisualFocusAll();
      setTimeout(this.close.bind(this, true), 100);
    }
  }

  onButtonClick() {
    if (this.isOpen()) {
      this.close(true);
    } else {
      this.open();
    }
    this.comboboxNode.focus();
    this.setVisualFocusCombobox();
  }

  /* Listbox Events */

  onListboxPointerover() {
    this.hasHover = true;
  }

  onListboxPointerout() {
    this.hasHover = false;
    setTimeout(this.close.bind(this, false), 300);
  }

  // Listbox Option Events

  /**
   * @param {SearchResult} result
   * @returns MouseEventHandler
   */
  onOptionClick(result) {
    /**
     * @returns void
     */
    return () => {
      this.comboboxNode.value = resultToText(result);
      this.confirmResult(result);
      this.close(true);
    };
  }

  onOptionPointerover() {
    this.hasHover = true;
    this.open();
  }

  onOptionPointerout() {
    this.hasHover = false;
    setTimeout(this.close.bind(this, false), 300);
  }
}

/**
 * @typedef {{
 *   searchWrapper: HTMLElement;
 *   data: any;
 *   domainMappers: Record<string, DomainMapper>;
 * }} RegisterSearchArgs
 * @param {RegisterSearchArgs} args
 */
export const registerSearch = ({ searchWrapper, data, domainMappers }) => {
  const comboboxNode = searchWrapper.querySelector("input");

  const buttonNode = searchWrapper.querySelector("button");
  const listboxNode = /** @type {HTMLElement | null} */ (
    searchWrapper.querySelector('[role="listbox"]')
  );
  if (comboboxNode != null && listboxNode != null) {
    new SearchBox(
      comboboxNode,
      buttonNode,
      listboxNode,
      domainMappers,
      dataToSearchableMap(data, domainMappers)
    );
  }
};