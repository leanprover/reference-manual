

/**
 * @type {DomainMapper}
 */
const Manual_DOT_lakeTomlField = {
    dataToSearchables:
      (domainData) =>
          Object.entries(domainData.contents).map(([key, value]) => {
            let tableArrayKey = value[0].data.tableArrayKey;
            let arr = tableArrayKey ? `[[${tableArrayKey}]]` : 'package configuration';
            return {
              searchKey: `${value[0].data.field} in ${arr}`,
              address: `${value[0].address}#${value[0].id}`,
              domainId: 'Manual.lakeTomlField',
              ref: value,
            }}),
    className: "lake-toml-field-domain",
    displayName: "Lake TOML Field"
    };

/**
 * @type {DomainMapper}
 */
const Manual_DOT_envVar = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: key,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Manual.envVar',
          ref: value,
        })),
    className: "env-var-domain",
    displayName: "Environment Variable"
    };

/**
 * @type {DomainMapper}
 */
const Manual_DOT_lakeOpt = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: key,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Manual.lakeOpt',
          ref: value,
        })),
    className: "lake-option-domain",
    displayName: "Lake Command-Line Option"
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_section = {
    dataToSearchables:
      (domainData) =>
          Object.entries(domainData.contents).map(([key, value]) => ({
            searchKey: `${value[0].data.sectionNum} ${value[0].data.title}`,
            address: `${value[0].address}#${value[0].id}`,
            domainId: 'Verso.Genre.Manual.section',
            ref: value,
          })),
    className: "section-domain",
    displayName: "Section"
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_example = {
    dataToSearchables:
      (domainData) => {
        const byName = Object.entries(domainData.contents).flatMap(([key, value]) =>
          value.map(v => ({
            context: v.data[`${v.address}#${v.id}`].context,
            name: v.data[`${v.address}#${v.id}`].display,
            address: `${v.address}#${v.id}`
          }))).reduce((acc, obj) => {
            const key = obj.name;
            if (!acc.hasOwnProperty(key)) acc[key] = [];
            acc[key].push(obj);
            return acc;
          }, {})
        return Object.entries(byName).flatMap(([key, value]) => {
          if (value.length === 0) { return []; }
          const firstCtxt = value[0].context;
          let prefixLength = 0;
          for (let i = 0; i < firstCtxt.length; i++) {
            if (value.every(v => i < v.context.length && v.context[i] === firstCtxt[i])) {
              prefixLength++;
            } else break;
          }
          return value.map((v) => ({
            searchKey: v.context.slice(prefixLength).concat(v.name).join(' › '),
            address: v.address,
            domainId: 'Verso.Genre.Manual.example',
            ref: value
          }));
        });
      },
    className: "example-def",
    displayName: "Example Definition"
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_tactic = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: value[0].data.userName,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Verso.Genre.Manual.doc.tactic',
          ref: value,
        })),
    className: "tactic-domain",
    displayName: "Tactic"
    };

/**
 * @type {DomainMapper}
 */
const Manual_DOT_lakeTomlTable = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => {
          let arrayKey = value[0].data.arrayKey;
          let arr = arrayKey ? `[[${arrayKey}]] — ` : '';
          return {
            searchKey: arr + value[0].data.description,
            address: `${value[0].address}#${value[0].id}`,
            domainId: 'Manual.lakeTomlTable',
            ref: value,
          }})
      ,
    className: "lake-toml-table-domain",
    displayName: "Lake TOML Table"
    };

/**
 * @type {DomainMapper}
 */
const Manual_DOT_lakeCommand = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: `lake ${key}`,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Manual.lakeCommand',
          ref: value,
        })),
    className: "lake-command-domain",
    displayName: "Lake Command"
    };

/**
 * @type {DomainMapper}
 */
const Manual_DOT_elanOpt = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: key,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Manual.elanOpt',
          ref: value,
        })),
    className: "elan-option-domain",
    displayName: "Elan Command-Line Option"
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_doc = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: key,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Verso.Genre.Manual.doc',
          ref: value,
        })),
    className: "doc-domain",
    displayName: "Documentation"
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_option = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: key,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Verso.Genre.Manual.doc.option',
          ref: value,
        })),
    className: "doc-option-domain",
    displayName: "Compiler Option"
    };

/**
 * @type {DomainMapper}
 */
const Manual_DOT_Syntax_DOT_production = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          // TODO find a way to not include the “meta” parts of the string
          // in the search key here, but still display them
          searchKey: value[0].data.forms.map(v => v.string).join(''),
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Manual.Syntax.production',
          ref: value,
        })),
    className: "syntax-domain",
    displayName: "Syntax"
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_tactic_DOT_conv = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: value[0].data.userName,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Verso.Genre.Manual.doc.tactic.conv',
          ref: value,
        })),
    className: "conv-tactic-domain",
    displayName: "Conv Tactic"
    };

/**
 * @type {DomainMapper}
 */
const Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_tech = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: value[0].data.term,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Verso.Genre.Manual.doc.tech',
          ref: value,
        })),
    className: "tech-term-domain",
    displayName: "Terminology"
    };

/**
 * @type {DomainMapper}
 */
const Manual_DOT_elanCommand = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: `elan ${key}`,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Manual.elanCommand',
          ref: value,
        })),
    className: "elan-command-domain",
    displayName: "Elan Command"
    };

/**
 * @type {DomainMapper}
 */
const Manual_DOT_errorExplanation = {
    dataToSearchables:
      (domainData) =>
        Object.entries(domainData.contents).map(([key, value]) => ({
          searchKey: key,
          address: `${value[0].address}#${value[0].id}`,
          domainId: 'Manual.errorExplanation',
          ref: value,
        })),
    className: "error-explanation-domain",
    displayName: "Error Explanation"
    };

export const domainMappers = {"Manual.lakeTomlField":
    Manual_DOT_lakeTomlField,
  "Manual.envVar": Manual_DOT_envVar,
  "Manual.lakeOpt": Manual_DOT_lakeOpt,
  "Verso.Genre.Manual.section":
    Verso_DOT_Genre_DOT_Manual_DOT_section,
  "Verso.Genre.Manual.example":
    Verso_DOT_Genre_DOT_Manual_DOT_example,
  "Verso.Genre.Manual.doc.tactic":
    Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_tactic,
  "Manual.lakeTomlTable": Manual_DOT_lakeTomlTable,
  "Manual.lakeCommand": Manual_DOT_lakeCommand,
  "Manual.elanOpt": Manual_DOT_elanOpt,
  "Verso.Genre.Manual.doc": Verso_DOT_Genre_DOT_Manual_DOT_doc,
  "Verso.Genre.Manual.doc.option":
    Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_option,
  "Manual.Syntax.production": Manual_DOT_Syntax_DOT_production,
  "Verso.Genre.Manual.doc.tactic.conv":
    Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_tactic_DOT_conv,
  "Verso.Genre.Manual.doc.tech":
    Verso_DOT_Genre_DOT_Manual_DOT_doc_DOT_tech,
  "Manual.elanCommand": Manual_DOT_elanCommand,
  "Manual.errorExplanation": Manual_DOT_errorExplanation
};