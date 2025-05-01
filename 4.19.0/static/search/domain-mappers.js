/**
 * Copyright (c) 2024 Lean FRO LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Author: Jakob Ambeck Vase
 */

/**
 * @import {DomainMapper} from './search-box.js'
 */

/**
 * @type {DomainMapper}
 */
const docDomainMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: key,
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Verso.Genre.Manual.doc",
      ref: value,
    })),
  className: "doc-domain",
  displayName: "Documentation",
};

/**
 * @type {DomainMapper}
 */
const docOptionDomainMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: key,
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Verso.Genre.Manual.doc.option",
      ref: value,
    })),
  className: "doc-option-domain",
  displayName: "Option",
};

/**
 * @type {DomainMapper}
 */
const docTacticDomainMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: value[0].data.userName,
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Verso.Genre.Manual.doc.tactic",
      ref: value,
    })),
  className: "tactic-domain",
  displayName: "Tactic",
};

/**
 * @type {DomainMapper}
 */
const docConvTacticDomainMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: value[0].data.userName,
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Verso.Genre.Manual.doc.tactic.conv",
      ref: value,
    })),
  className: "conv-tactic-domain",
  displayName: "Conv Tactic",
};

/**
 * @type {DomainMapper}
 */
const sectionMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: `${value[0].data.sectionNum} ${value[0].data.title}`,
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Verso.Genre.Manual.section",
      ref: value,
    })),
  className: "section-domain",
  displayName: "Section",
};

/**
 * @type {DomainMapper}
 */
const techTermMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: value[0].data.term,
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Verso.Genre.Manual.doc.tech",
      ref: value,
    })),
  className: "tech-term-domain",
  displayName: "Terminology",
};

/**
 * @type {DomainMapper}
 */
const syntaxMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      // TODO find a way to not include the "meta" parts of the string
      // in the search key here, but still display them
      searchKey: value[0].data.forms.map(v => v.string).join(''),
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Manual.Syntax.production",
      ref: value,
    })),
  className: "syntax-domain",
  displayName: "Syntax",
};

/**
 * @type {DomainMapper}
 */
const lakeCommandMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: `lake ${key}`,
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Manual.lakeCommand",
      ref: value,
    })),
  className: "lake-command-domain",
  displayName: "Lake Command",
};

/**
 * @type {DomainMapper}
 */
const lakeOptMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: key,
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Manual.lakeOpt",
      ref: value,
    })),
  className: "lake-option-domain",
  displayName: "Lake Command-Line Option",
};
/**
 * @type {DomainMapper}
 */
const elanCommandMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: `elan ${key}`,
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Manual.elanCommand",
      ref: value,
    })),
  className: "elan-command-domain",
  displayName: "Elan Command",
};

/**
 * @type {DomainMapper}
 */
const elanOptMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: key,
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Manual.elanOpt",
      ref: value,
    })),
  className: "elan-option-domain",
  displayName: "Elan Command-Line Option",
};

/**
 * @type {DomainMapper}
 */
const envVarMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: key,
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Manual.envVar",
      ref: value,
    })),
  className: "env-var-domain",
  displayName: "Environment Variable",
};

/**
 * @type {DomainMapper}
 */
const lakeTomlFieldMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => {
      let tableArrayKey = value[0].data.tableArrayKey;
      let arr = tableArrayKey ? `[[${tableArrayKey}]]` : "package configuration";
      return {
        searchKey: `${value[0].data.field} in ${arr}`,
        address: `${value[0].address}#${value[0].id}`,
        domainId: "Manual.lakeTomlField",
        ref: value,
      }}),
  className: "lake-toml-field-domain",
  displayName: "Lake TOML Field",
};

/**
 * @type {DomainMapper}
 */
const lakeTomlTableMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => {
      let arrayKey = value[0].data.arrayKey;
      let arr = arrayKey ? `[[${arrayKey}]] — ` : "";
      return {
        searchKey: arr + value[0].data.description,
        address: `${value[0].address}#${value[0].id}`,
        domainId: "Manual.lakeTomlTable",
        ref: value,
      }}),
  className: "lake-toml-table-domain",
  displayName: "Lake TOML Table",
};

export const domainMappers = {
  "Verso.Genre.Manual.doc": docDomainMapper,
  "Verso.Genre.Manual.doc.option": docOptionDomainMapper,
  "Verso.Genre.Manual.doc.tactic": docTacticDomainMapper,
  "Verso.Genre.Manual.doc.tactic.conv": docConvTacticDomainMapper,
  "Verso.Genre.Manual.section": sectionMapper,
  "Verso.Genre.Manual.doc.tech": techTermMapper,
  "Manual.Syntax.production": syntaxMapper,
  "Manual.lakeCommand": lakeCommandMapper,
  "Manual.lakeOpt": lakeOptMapper,
  "Manual.envVar": envVarMapper,
  "Manual.lakeTomlTable": lakeTomlTableMapper,
  "Manual.lakeTomlField": lakeTomlFieldMapper,
  "Manual.elanCommand": elanCommandMapper,
  "Manual.elanOpt": elanOptMapper,
};
