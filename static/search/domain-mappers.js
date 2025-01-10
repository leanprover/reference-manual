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
      searchKey: key,
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Verso.Genre.Manual.doc.tactic",
      ref: value,
    })),
  className: "doc-tactic-domain",
  displayName: "Tactic",
};

/**
 * @type {DomainMapper}
 */
const sectionMapper = {
  dataToSearchables: (domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => ({
      searchKey: value[0].data[value[0].data.length - 1],
      address: `${value[0].address}#${value[0].id}`,
      domainId: "Verso.Genre.Manual.section",
      ref: value,
    })),
  className: "section-domain",
  displayName: "Section",
};

export const domainMappers = {
  "Verso.Genre.Manual.doc": docDomainMapper,
  "Verso.Genre.Manual.doc.option": docOptionDomainMapper,
  "Verso.Genre.Manual.doc.tactic": docTacticDomainMapper,
  "Verso.Genre.Manual.section": sectionMapper,
};
