/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command
import Lake.Config.Monad
import Lake.DSL

import Manual.Meta
import Manual.BuildTools.Lake.CLI


open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lake.DSL

#doc (Manual) "System Configuration" =>
%%%
tag := "lake-system-config"
%%%

Lake's system configuration file specifies configuration values that are applied in all {tech}[workspaces].
By default, it is loaded from `~/.lake/config.toml`, but this path can be overridden by setting the {envVar}`LAKE_CONFIG` environment variable.
If the file does not exist, default values are used.

The system configuration file is used to configure the {ref "lake-cache-remote"}[Lake artifact cache].
It is loaded before any package configuration, and its settings take precedence over those declared by packages.


::::tomlTableDocs "cache" "Cache Configuration" Lake.CacheConfig +table (skip := services)

:::tomlField Lake.CacheConfig defaultService "Service name" "Service names" String
The cache service used by {lake}`cache get` if {lakeOpt}`--service` is not provided.
It must refer to a service defined in this file.
If unset, the default is Reservoir.
:::

:::tomlField Lake.CacheConfig defaultUploadService "Service name" "Service names" String
The cache service used by {lake}`cache put` if {lakeOpt}`--service` is not provided.
It must refer to a service defined in this file.
If unset, {lake}`cache put` requires a {lakeOpt}`--service` option.
:::

:::tomlField Lake.CacheConfig service "Cache service" "Cache services" Lake.CacheServiceConfig
Cache services are specified using the same format as in a TOML-format {ref "lake-config-cache-services"}[package configuration file].
Cache services defined in the system configuration file may be used for uploads with {lake}`cache put`.
:::

::::

:::lakeToml Lake.LakeConfig _root_ -show +error
```toml
cache.defaultService = "elsewhere"
```
```expected
error: the configured default cache service `elsewhere` is not defined; please add a `cache.service` with that name
```
:::

:::lakeToml Lake.LakeConfig _root_ -show +error
```toml
cache.defaultUploadService = "elsewhere"
```
```expected
error: the configured default cache upload service `elsewhere` is not defined; please add a `cache.service` with that name
```
:::

::::example "System Cache Configuration"
This system configuration file specifies a cache service named `my-service`.
The custom cache service is set to be the default for both {lake}`cache get` and {lake}`cache put`.
Use {lakeOpt}`--service reservoir` to select Reservoir's cache.
Reservoir does not suport {lake}`cache put`.

:::lakeToml Lake.LakeConfig _root_
```toml
cache.defaultService = "my-service"
cache.defaultUploadService = "my-service"

[[cache.service]]
name = "my-service"
kind = "s3"
artifactEndpoint = "https://my-service.example.com/a0"
revisionEndpoint = "https://my-service.example.com/r0"
```
```expected
{cache :=
    {defaultService := "my-service",
      defaultUploadService := "my-service",
      services :=
        {'«my-service»' ↦ {name? := some "my-service",
           kind := s3,
           artifactEndpoint := "https://my-service.example.com/a0",
           revisionEndpoint := "https://my-service.example.com/r0"}}}}
```
:::
::::
