import {domainMappers} from './domain-mappers.js';
import {registerSearch} from './search-box.js';

let siteRoot = typeof __versoSiteRoot !== 'undefined' ? __versoSiteRoot : "";

// The search box itself. TODO: add to template
const searchHTML = `<div id="search-wrapper">
  <div class="combobox combobox-list">
    <div class="group">
      <input
        id="cb1-input"
        class="cb_edit"
        type="search"
        role="searchbox"
        placeholder="Index"
        aria-autocomplete="list"
        aria-expanded="false"
        aria-controls="cb1-listbox"
      />
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
