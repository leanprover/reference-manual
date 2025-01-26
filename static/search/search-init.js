/**
 * Copyright (c) 2024 Lean FRO LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Author: David Thrane Christiansen
 */

import {domainMappers} from './domain-mappers.js';
import {registerSearch} from './search-box.js';

let siteRoot = typeof __versoSiteRoot !== 'undefined' ? __versoSiteRoot : "";

// The search box itself. TODO: add to template
const searchHTML = `<div id="search-wrapper">
  <div class="combobox combobox-list">
    <div class="group">
      <div
        id="cb1-input"
        class="cb_edit"
        contenteditable="true"
        role="searchbox"
        placeholder="Index"
        aria-autocomplete="list"
        aria-expanded="false"
        aria-controls="cb1-listbox"
      ></div>
    </div>
    <ul id="cb1-listbox" role="listbox" aria-label="Results"></ul>
  </div>
</div>
`;

// Initialize search box
const data = fetch(siteRoot + "/xref.json").then((data) => data.json())
window.addEventListener("load", () => {
  const main = document.querySelector("main");
  main.insertAdjacentHTML("afterbegin", searchHTML);
  const searchWrapper = document.querySelector(".combobox-list");
  data.then((data) => {
    registerSearch({searchWrapper, data, domainMappers});
  });
});
