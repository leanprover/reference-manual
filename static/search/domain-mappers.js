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
  className: "doc-tactic-domain",
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
  className: "doc-tactic-domain",
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

export const domainMappers = {
  "Verso.Genre.Manual.doc": docDomainMapper,
  "Verso.Genre.Manual.doc.option": docOptionDomainMapper,
  "Verso.Genre.Manual.doc.tactic": docTacticDomainMapper,
  "Verso.Genre.Manual.doc.tactic.conv": docConvTacticDomainMapper,
  "Verso.Genre.Manual.section": sectionMapper,
  "Verso.Genre.Manual.doc.tech": techTermMapper,
};