/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/

import VersoManual

import Manual.Meta
import Lean.Widget

open Verso.Genre Manual InlineLean
open Lean Widget

#doc (Manual) "Widgets" =>
%%%
tag := "widgets"
%%%

The widget system enables Lean code to define and render user interface components, loosely referred to as _widgets_.
In graphical development environments such as VS Code with the [official Lean extension](https://github.com/leanprover/vscode-lean4/), widgets are displayed in the [InfoView](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md#infoview) (the editor panel that shows tactic states, messages, and other information relevant to the current cursor position).
Besides communicating additional information or visuals, widgets may manipulate Lean values and run Lean functions, as well as edit source files (for example in response to UI events).
To start using widgets, import {module}`Lean.Widget`.
:::TODO
- When verso#311 lands, note it as another usecase.
:::

# Client-Side JavaScript

In general, widgets combine client-side JavaScript code that executes in the InfoView with server-side Lean code implementing {ref "widgets-remote-procedure-calls"}[RPC method handlers].
However, many widgets don't use RPC methods, so only have a client part.

Client-side code is organized into {deftech (key := "widget module")}_widget modules_.
Any [JavaScript module](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Modules) compatible with the {ref "widgets-javascript-environment"}[InfoView JavaScript environment] can be used as a widget module.
There are no generic requirements on its exports; requirements are imposed when some export is used in a specific way, for example as an {tech}[InfoView panel widget].

To register a widget module in Lean, tag its definition with the {attr}`widget_module` attribute.
The definition must have a type convertible to {name}`Widget.Module`, i.e., a type with a {name}`Widget.ToModule` instance.

:::example "Registering a widget module"
```imports -show
import Lean.Widget.UserWidget
```
```lean -show
open Lean
```
```lean
@[widget_module]
def foo : Widget.Module where
  javascript := r#"
    export default function() { return "Hello, world!" }
  "#
```
:::

{docstring Widget.Module}

{docstring +allowMissing Widget.ToModule}

## InfoView JavaScript Environment
%%%
tag := "widgets-javascript-environment"
%%%

The JavaScript environment in which widget modules execute is a standard browser environment, extended by the following Lean-specific features.

: Preloaded Libraries

  These packages are preloaded.
  Each can be imported by using its name as the module specifier (under the hood, an [import map](https://developer.mozilla.org/en-US/docs/Web/HTML/Reference/Elements/script/type/importmap) is configured).
  For example, `import * as React from 'react'` would work.
  - [`'react'`](https://www.npmjs.com/package/react), [`'react-dom'`](https://www.npmjs.com/package/react-dom), and `'react/jsx-runtime'` provide the [React](https://react.dev/) runtime shared with the InfoView.
  - [`'@leanprover/infoview'`](https://www.npmjs.com/package/@leanprover/infoview) allows widgets to reuse UI components used by the InfoView, as well as to communicate with other parts of the InfoView, with the editor, and with the Lean language server.
    Documentation can be found [here](https://leanprover.github.io/vscode-lean4/infoview).

: Importing by Hash

  A widget module may import another widget module via the module specifier `'widget_module:hash,<hash>'`, where `<hash>` is the dependency's {name}`Widget.Module.javascriptHash`.

## Bundling

A {tech}[widget module] must be a single, self-contained JavaScript module.
In order to compile an [`npm`](https://www.npmjs.com/) package (with dependencies, TypeScript, and so on) into this format, one typically uses a _bundler_.
The following bundler-specific instructions may be useful.

: [Rollup.js](https://rollupjs.org/)

  A working [Rollup.js configuration](https://github.com/leanprover-community/ProofWidgets4/blob/main/widget/rollup.config.js) for widgets can be found in the ProofWidgets package.

  - Set [`output.format`](https://rollupjs.org/guide/en/#outputformat) to `'es'` so that a module is produced.
  - [Externalize](https://rollupjs.org/guide/en/#external) the preloaded libraries—`react`, `react-dom`, `react/jsx-runtime`, and `@leanprover/infoview`—so that their global state is not duplicated in your bundle.

: [esbuild](https://esbuild.github.io/)

  Does not work due to issue [evanw/esbuild#1944](https://github.com/evanw/esbuild/issues/1944).

# Displaying Widgets

Widgets are [React components](https://react.dev/learn/your-first-component) exported from widget modules.
The InfoView is a React application, and is capable of embedding these components.
A widget must be the [`default` export](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Statements/export#using_the_default_export) of its module.

When registering a widget for display in Lean, we provide [props](https://react.dev/learn/passing-props-to-a-component) that it will receive when it is rendered by the InfoView.
In Lean, a {name}`Widget.WidgetInstance` bundles such an assignment of props with a reference to the widget module that exports the component.
The assignment is stored as a {name}`Json` object—later decoded into a JavaScript object—and more generally a {lean}`StateM Server.RpcObjectStore Json` computation, in order to support {tech (key := "RPC reference")}[RPC references].

{docstring Widget.WidgetInstance}

Lean can display widgets in two ways: within messages in the {tech}[message log], or as {tech (key := "InfoView panel widget")}[InfoView panels] associated with a source span.

: Widgets in Messages

  A widget component is displayed inline in a Lean message.

  {docstring MessageData.ofWidget}

: InfoView Panels

  By default, the InfoView conveys information about a given position in a Lean source file by means of three panels: _Tactic state_, _Expected type_, and _Messages_.
  This listing can be extended by user-defined panels (appearing below _Expected type_), for instance to render tactic states in custom proof modes.

  Such an {deftech}_InfoView panel widget_ is associated with a span—a range of characters—in the source code.
  It is drawn whenever the InfoView is describing a position within this span (either because the editor cursor is there, or because that position is [pinned](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md#status-bar)).

  :::sectionNote
  Panel widgets saved by {name}`Widget.savePanelWidgetInfo` are stored in the enclosing command's {tech (key := "info trees")}[info tree], while those saved by {keywordOf Lean.Widget.showPanelWidgetsCmd}`show_panel_widgets` are stored in an environment extension.
  :::

  - To associate a widget instance with the span of a piece of {name}`Lean.Syntax`, use {name}`Widget.savePanelWidgetInfo`.

    {docstring Widget.savePanelWidgetInfo}

  - To associate it with all positions in a Lean module, scope, or set of modules downstream of a given module, use the {keywordOf Lean.Widget.showPanelWidgetsCmd}`show_panel_widgets` command.

  When rendering a panel widget, the InfoView extends the props object obtained from the {name}`Widget.WidgetInstance` with additional, automatically computed properties that reflect the editor state (for instance the current cursor position).
  These additional props are documented as [`PanelWidgetProps`](https://leanprover.github.io/vscode-lean4/infoview/docs/interfaces/index.PanelWidgetProps.html).

  A panel widget should be collapsible (conventionally a [`<details>`](https://developer.mozilla.org/en-US/docs/Web/HTML/Reference/Elements/details) element).

  A panel widget is re-rendered when the source position it describes is re-elaborated.

  Finally, the {keywordOf Lean.Widget.widgetCmd}`#widget` command can be used to quickly render a panel widget.

  :::example "Using the #widget command"
  The panel widget is associated with the source line the command appears on.
  Internally, this command invokes {name}`Widget.savePanelWidgetInfo`.

  ```imports -show
  import Lean.Widget.Commands
  ```
  ```lean -show
  open Lean
  ```
  ```lean
  @[widget_module]
  def helloWidget : Widget.Module where
    javascript := "
      import * as React from 'react';
      export default function(props) {
        const name = props.name || 'world'
        return React.createElement('p', {}, 'Hello, ' + name + '!')
      }"

  #widget helloWidget with json% { name: "Hexapus" }
  ```
  :::

# Remote Procedure Calls
%%%
tag := "widgets-remote-procedure-calls"
%%%

The InfoView—together with any embedded widgets—is a web application running on the same computer as the IDE.
The Lean language server, which {tech (key := "Lean elaborator")}[elaborates] source files and interprets Lean code, is a separate process.
The InfoView and the language server may reside on two different machines, e.g. when using Lean in a server-backed web IDE or over SSH.

It can be useful for widgets to maintain part of their state or input data in the server, as opposed to serializing and transferring it to the client.
Transfer may be impractical due to a slow network, and objects may not be easily serializable (as is the case for closures, {name}`IO.Promise`s, or {name}`Lean.Environment`s).
The Remote Procedure Call (RPC) mechanism allows client-side widget code to manipulate {tech (key := "RPC reference")}[RPC references] to server-side data, and to execute {tech (key := "RPC method")}[RPC methods] in the server.

## Encoding and References

The {name}`Server.RpcEncodable` type class marks client-server transferrable types.
The wire format is JSON, and any type with both {name}`Lean.ToJson` and {name}`Lean.FromJson` instances is encodable.
An instance can be derived automatically, as documented below.

{docstring +allowMissing Server.RpcEncodable}

The main purpose of {name}`Server.RpcEncodable` is to support—in addition to JSON—structures containing {deftech (key := "RPC reference")}[RPC references].
Every reference is marked with the {name}`Server.WithRpcRef` wrapper.
A value wrapped with {name}`Server.WithRpcRef` is not serialized or transferred to the client.
Instead, the client receives an opaque identifier that can later be used to retrieve the value server-side, in an {tech}[RPC method] call.

{docstring +allowMissing Server.WithRpcRef}

::::leanSection
```lean -show
variable (α : Type)
```
The type {lean}`α` must have a {name}`TypeName` instance for {lean}`Server.RpcEncodable (Server.WithRpcRef α)` to be inhabited.

:::example "TypeName and imported constants"
We discourage deriving {lean}`TypeName α` outside of the module where {lean}`α` is defined.
Instead, define a single-field structure (a “newtype”) wrapping {lean}`α`, and derive {lean}`TypeName` for that.
```lean
structure MyNat where
  val : Nat
  deriving TypeName
```
:::
::::

Use {name}`Server.WithRpcRef.mk` to construct RPC references.

{docstring Server.WithRpcRef.mk}

## RPC Methods
### Server

:::leanSection
```lean -show
variable (α β : Type)
```
To register an {deftech}[RPC method], use the {attr}`server_rpc_method` attribute.
The method must be a function of type {lean}`α → Server.RequestM (Server.RequestTask β)`, where `α` and `β` are {name}`Server.RpcEncodable`.

The {name}`Server.RequestM` monad supports IO actions, and provides access to parts of the language server state.

The output is wrapped in {name}`Server.RequestTask` to support asynchronous execution of RPC methods.
Ideally, a method implementation returns immediately, doing most of its work in the returned task.
The {name}`Server.RequestM.asTask` convenience function does exactly this.
:::

:::example "Registering an RPC method"
```imports -show
import Lean.Server.Rpc
```
```lean -show
open Lean
```
```lean
structure Args where
  num : Nat
  deriving TypeName

@[server_rpc_method]
def extractNum (args : Server.WithRpcRef Args) :
    Server.RequestM (Server.RequestTask Nat) :=
  Server.RequestM.asTask <| return args.val.num
```
:::

:::sectionNote
As an alternative to passing {name}`Server.WithRpcRef` values as RPC method arguments, RPC methods may refer to global {name}`IO.Ref`s.
However, these behave differently.
A single copy of the {name}`IO.Ref` resides in server memory and is shared by all widgets that refer to it, whereas distinct RPC references can be created for each widget instance.
Make sure not to accidentally share state that you did not intend to across copies of your UI component.
:::

### Client

:::sectionNote
The RPC system does not depend on JavaScript.
Any LSP client may create RPC sessions and invoke RPC methods.
:::

Any widget React component may invoke RPC methods.
To do so, the component should first obtain an _RPC session_ handle via the [`useRpcSession`](https://leanprover.github.io/vscode-lean4/infoview/docs/functions/index.useRpcSession.html) hook.
The handle may then be used to call RPC methods; see [`RpcSessionAtPos.call`](https://leanprover.github.io/vscode-lean4/infoview/docs/interfaces/index.RpcSessionAtPos.html#call).

