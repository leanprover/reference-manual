/**
 * Copyright (c) 2024 Lean FRO LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Author: Jakob Ambeck Vase
 */

/**
 * @import {DomainMapper} from './search-box.js'
 */



export const domainMappers = {
  "Manual.Syntax.production": syntaxMapper,
  "Manual.lakeCommand": lakeCommandMapper,
  "Manual.lakeOpt": lakeOptMapper,
  "Manual.envVar": envVarMapper,
  "Manual.lakeTomlTable": lakeTomlTableMapper,
  "Manual.lakeTomlField": lakeTomlFieldMapper,
  "Manual.elanCommand": elanCommandMapper,
  "Manual.elanOpt": elanOptMapper,
  "Manual.errorExplanation": errorExplanationMapper
};
