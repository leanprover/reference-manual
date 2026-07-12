# fix_diagnostics

A Python tool to automate fixing Lean diagnostics via LSP code
actions. This is mostly LLM-generated code that hasn't been
extensively tested/checked, so please treat it with due caution.

## Overview

`fix_diagnostics` helps you automatically apply code actions to fix
diagnostics (errors, warnings, info messages) in your Lean projects.
It works by:

1. Running `lake build` to find files with diagnostics
2. Using the Lean LSP server to get structured diagnostic information
3. Querying available code actions for each diagnostic (including
   widget-based "Try this:" suggestions)
4. Applying selected code actions to fix issues

The tool has **no external dependencies** - it uses only Python's
standard library with a manual JSON-RPC implementation for LSP
communication.

**Widget Support**: The tool queries Lean's interactive diagnostics
via the RPC extension to discover code actions embedded in widget
components (like "Try this:" suggestions). These appear as regular
code actions that can be filtered and applied just like standard LSP
code actions.

## Requirements

- Python 3.7+
- Lean 4 with Lake (the `lake serve` command must be available)
- Must be run from a Lake project directory (containing
  `lakefile.lean` or `lakefile.toml`)

## Quick Start

### CLI Usage

**Typical workflow:**

1. List diagnostics and available actions with `--list`
2. Filter by patterns to find the fixes you want
3. Preview with dry-run (default)
4. Apply with `--no-dry-run`

By default, the CLI applies **unique actions per diagnostic**
(deduplicating by edit effect). Use `--minimal` to apply only the
**smallest edit** for each diagnostic.

```bash
# Step 1: RECOMMENDED - List all diagnostics and their available code actions
# (shows edit_size for each action)
python3 -m fix_diagnostics --list

# Filter diagnostics by pattern and list actions
python3 -m fix_diagnostics --diagnostic-pattern "unused variable" --list

# Preview fixes (dry-run, default behavior) - applies unique actions per diagnostic
python3 -m fix_diagnostics --diagnostic-pattern "unused" --action-pattern "Remove"

# Apply only the smallest edit for each diagnostic
python3 -m fix_diagnostics --diagnostic-pattern "unused" --minimal --no-dry-run

# Apply all unique fixes (default deduplication)
python3 -m fix_diagnostics --diagnostic-pattern "unused" --action-pattern "Remove" --no-dry-run

# Filter by severity (1=error, 2=warning, 3=info, 4=hint)
python3 -m fix_diagnostics --severity 2 --action-pattern "Remove"

# Preview ALL available code actions (no filters)
# Warning: This can produce a lot of output!
python3 -m fix_diagnostics
```

### REPL Usage

The tool is designed for interactive exploration in the Python REPL:

```python
from fix_diagnostics import *

# Step 1: Find files with diagnostics
files = get_files()
print(f"Found {len(files)} files with diagnostics")

# Step 2: Get all diagnostics from LSP
diagnostics = get_diagnostics(files)
print(f"Got {len(diagnostics)} diagnostics")

# Inspect diagnostics
for d in diagnostics[:5]:
    print(f"{d.file.name}:{d.line}:{d.col} - {d.message}")

# Step 3: Get code actions for diagnostics
actions = get_code_actions(diagnostics)
print(f"Found {len(actions)} code actions")

# Filter actions
unused_actions = [a for a in actions if 'unused' in a.diagnostic.message]
remove_actions = [a for a in actions if 'Remove' in a.title]
foo_file_actions = [a for a in actions if 'Foo.lean' in str(a.diagnostic.file)]

# Step 4: Apply actions (dry-run by default)
results = apply_code_actions(remove_actions, dry_run=True)

# Review diffs
for result in results:
    if result.success:
        print(f"\n{result.action.title}")
        print(result.diff)

# Apply for real
results = apply_code_actions(remove_actions, dry_run=False)
print(f"Applied {sum(r.success for r in results)} actions")
```

### Defaults

Functions automatically call previous steps if inputs aren't provided:

```python
# Get diagnostics without specifying files (calls get_files() automatically)
diagnostics = get_diagnostics()

# Get actions without specifying diagnostics (calls get_diagnostics() automatically)
actions = get_code_actions()

# This is equivalent to:
# files = get_files()
# diagnostics = get_diagnostics(files)
# actions = get_code_actions(diagnostics)
```

### Working with Single Items

Both `get_code_actions()` and `apply_code_actions()` accept single
items or lists:

```python
from fix_diagnostics import get_diagnostics, get_code_actions, apply_code_actions

diagnostics = get_diagnostics()

# Pass a single diagnostic
single_diag = diagnostics[0]
actions = get_code_actions(single_diag)  # Works!

# Pass a single action
single_action = actions[0]
results = apply_code_actions(single_action, dry_run=True)  # Works!

# Both always return lists
print(f"Got {len(results)} result(s)")  # Always a list, even for single input
```

### Persistent LSP Client for REPL

For interactive work, use `lsp_start()` to create a persistent LSP
client that's automatically reused across function calls. This avoids
repeatedly starting and stopping the Lean server:

```python
from fix_diagnostics import lsp_start, get_diagnostics, get_code_actions, lsp_stop

# Start persistent client (call once)
lsp_start()

# All subsequent calls automatically reuse the global client
diagnostics = get_diagnostics()
actions = get_code_actions(diagnostics)

# Filter and continue working - client is still alive
unused_diags = [d for d in diagnostics if 'unused' in d.message]
more_actions = get_code_actions(unused_diags)

# You can call the same diagnostic multiple times - it works correctly
same_diag_actions = get_code_actions(diagnostics[0])  # Works!
again = get_code_actions(diagnostics[0])  # Still works!

# Optional: manually stop when done (also happens automatically on exit)
lsp_stop()
```

**Without `lsp_start()`**, each function call creates and destroys a
temporary LSP client, which is slower but works fine for scripts.

**With `lsp_start()`**, a single LSP client persists across all calls,
dramatically speeding up interactive exploration. The client tracks
which files are open and avoids reopening them, so repeated calls on
the same diagnostics work correctly.

## API Reference

### Core Functions

#### `get_files(build_cmd="lake build")`

Find files with diagnostics from build output.

**Returns:** `List[Path]` - Files with diagnostics, ordered by
appearance in build output

**Raises:** `FileNotFoundError` if not in a Lake project directory

#### `lsp_start()`

Start a persistent LSP client for REPL use.

Creates a global LSP client that will be automatically reused by
`get_diagnostics()` and `get_code_actions()`. The client is cleaned up
automatically on exit.

**Returns:** `LspClient` - The started global LSP client

**Example:**

```python
from fix_diagnostics import lsp_start, get_diagnostics
lsp_start()
diagnostics = get_diagnostics()  # Reuses the global client
```

#### `lsp_stop()`

Stop the global LSP client.

Shuts down the persistent LSP client created by `lsp_start()`.
Normally not needed as cleanup happens automatically on exit, but
useful for restarting the server.

**Example:**

```python
from fix_diagnostics import lsp_start, lsp_stop
lsp_start()
# ... do work
lsp_stop()  # Explicitly stop
lsp_start()  # Can start again
```

#### `get_diagnostics(files=None, lsp_client=None)`

Get diagnostics from LSP for files.

If `lsp_start()` was called, automatically reuses the global client.
Otherwise, creates a temporary client.

**Args:**

- `files`: `List[Path]` or `None` (calls `get_files()` if not
  provided)
- `lsp_client`: Optional `LspClient` to reuse (overrides global
  client)

**Returns:** `List[Diagnostic]`

#### `get_code_actions(diagnostics=None, lsp_client=None)`

Get code actions for diagnostics.

If `lsp_start()` was called, automatically reuses the global client.
Otherwise, creates a temporary client.

**Args:**

- `diagnostics`: Single `Diagnostic`, `List[Diagnostic]`, or `None`
  (calls `get_diagnostics()` if not provided)
- `lsp_client`: Optional `LspClient` to reuse (overrides global
  client)

**Returns:** `List[CodeAction]` - Each action has a back-pointer to
its diagnostic

#### `apply_code_actions(actions, dry_run=True)`

Apply code actions to files.

**Args:**

- `actions`: Single `CodeAction` or `List[CodeAction]`
- `dry_run`: If `True`, compute diffs but don't modify files (default:
  `True`)

**Returns:** `List[ApplyResult]` - One result per action

### Data Classes

#### `Diagnostic`

```python
@dataclass
class Diagnostic:
    file: Path          # File containing the diagnostic
    line: int           # Line number (0-based, LSP protocol)
    col: int            # Column number (0-based, UTF-16 offset, LSP protocol)
    severity: int       # 1=Error, 2=Warning, 3=Info, 4=Hint
    message: str        # Diagnostic message
    code: Optional[str] # Diagnostic code
    source: Optional[str] # Source (e.g., "Lean", linter name)
    range: LspRange     # Full LSP range structure (with UTF-16 offsets)
    range_size: int     # Size in codepoints (Python characters)
```

#### `CodeAction`

```python
@dataclass
class CodeAction:
    title: str          # Human-readable action title
    kind: Optional[str] # Action kind (e.g., "quickfix")
    edit: dict          # LSP WorkspaceEdit (with UTF-16 offsets)
    diagnostic: Diagnostic # Back-pointer to diagnostic
    edit_size: int      # Magnitude of edit in codepoints (Python characters)
```

#### `ApplyResult`

```python
@dataclass
class ApplyResult:
    success: bool       # Whether action was applied successfully
    action: CodeAction  # The code action that was applied
    diff: str           # Unified diff showing changes
    error: Optional[str] # Error message if success=False
```

### LSP Client

#### `LspClient(server_cmd=None)`

Manual LSP client using JSON-RPC over stdio.

**Args:**

- `server_cmd`: Command to start LSP server (default:
  `['lake', 'serve']`)

**Usage:**

```python
# Context manager (recommended)
with LspClient() as lsp:
    lsp.did_open(file_path, text)
    diagnostics = lsp.get_diagnostics(file_path)
    actions = lsp.code_action(file_path, line, col, [diagnostic])

# Manual lifecycle
lsp = LspClient()
lsp.initialize()
# ... use lsp ...
lsp.shutdown()
```

## CLI Options

```
--diagnostic-pattern PATTERN  Regex to filter diagnostic messages
--action-pattern PATTERN      Regex to filter code action titles
--severity {1,2,3,4}          Filter by severity (can specify multiple)
--list                        List diagnostics and actions without applying
--dry-run                     Show diffs without applying (default)
--no-dry-run                  Actually apply changes
--minimal                     Apply only the smallest edit per diagnostic
--build-cmd CMD               Build command (default: "lake build")
```

**Default behavior (no options):**

- Finds ALL diagnostics in the project
- Gets ALL available code actions
- Deduplicates actions per diagnostic by edit effect
- Previews all unique actions in dry-run mode (shows diffs but doesn't
  modify files)
- Recommended: Use `--list` first to see what actions are available

## Examples

### Fix all unused variable warnings

```bash
python3 -m fix_diagnostics \
  --diagnostic-pattern "unused variable" \
  --action-pattern "Remove" \
  --no-dry-run
```

### Preview all available fixes for a specific file

```python
from fix_diagnostics import get_diagnostics, get_code_actions
from pathlib import Path

# Get diagnostics for specific file
all_diags = get_diagnostics()
my_file_diags = [d for d in all_diags if d.file == Path("Manual/Foo.lean")]

# Get and preview actions
actions = get_code_actions(my_file_diags)
for action in actions:
    print(f"{action.title} at line {action.diagnostic.line}")
```

### Apply specific action to all matching diagnostics

```python
from fix_diagnostics import get_code_actions, apply_code_actions

# Get all actions
actions = get_code_actions()

# Filter to specific action type
rename_actions = [a for a in actions if a.title.startswith("Rename to _")]

# Apply
results = apply_code_actions(rename_actions, dry_run=False)
print(f"Applied {sum(r.success for r in results)}/{len(results)} actions")
```

### Filter by edit size

Each `CodeAction` has an `edit_size` field indicating the magnitude of
the change, and each `Diagnostic` has a `range_size` field indicating
the size of the diagnostic's range. You can use these to filter for
small changes:

```python
from fix_diagnostics import get_code_actions

# Get all actions
actions = get_code_actions()

# Filter to actions that change less than 5 characters
small_edits = [a for a in actions if a.edit_size < 5]

# Filter to actions that change less than 5% of the diagnostic's range
small_percentage_edits = [
    a for a in actions
    if a.diagnostic.range_size > 0 and a.edit_size / a.diagnostic.range_size < 0.05
]

# Sort by edit size to see smallest changes first
sorted_actions = sorted(actions, key=lambda a: a.edit_size)

# Group by diagnostic and keep smallest action for each
from itertools import groupby
from operator import attrgetter

actions_by_diag = {}
for action in actions:
    key = (action.diagnostic.file, action.diagnostic.line, action.diagnostic.col)
    if key not in actions_by_diag or action.edit_size < actions_by_diag[key].edit_size:
        actions_by_diag[key] = action

smallest_per_diag = list(actions_by_diag.values())
```

### Iteratively fix issues

```python
from fix_diagnostics import get_diagnostics, get_code_actions, apply_code_actions

max_iterations = 5
for i in range(max_iterations):
    # Get current diagnostics
    diagnostics = get_diagnostics()
    unused = [d for d in diagnostics if 'unused' in d.message]

    if not unused:
        print(f"All unused variables fixed after {i} iterations!")
        break

    # Get and apply fixes
    actions = get_code_actions(unused)
    remove = [a for a in actions if 'Remove' in a.title]

    if not remove:
        print(f"No more remove actions available")
        break

    results = apply_code_actions(remove, dry_run=False)
    print(f"Iteration {i+1}: applied {sum(r.success for r in results)} fixes")
```

## How It Works

1. **Build Output Parsing**: Runs `lake build` and parses the output
   to identify files with diagnostics. Supports both formats:
    - `warning: path/to/file.lean:123:45: message`
    - `path/to/file.lean:123:45: error: message`

2. **LSP Communication**: Opens each file in the Lean LSP server using
   `textDocument/didOpen` and waits for file processing to complete.
   The tool uses Lean's `$/lean/fileProgress` notifications to know
   when the server has finished analyzing each file, ensuring
   diagnostics are complete before proceeding.

3. **Code Action Query**: For each diagnostic, queries the LSP server
   for available code actions using `textDocument/codeAction` with the
   diagnostic in the context. Additionally, queries Lean's interactive
   diagnostics via `$/lean/rpc/call` with method
   `Lean.Widget.getInteractiveDiagnostics` to extract code actions
   from widget components (like "Try this:" suggestions). The LSP
   client enables widget support by setting
   `initializationOptions.hasWidgets` to `true`.

    **RPC Session Management**: RPC sessions are cached per file URI
    and reused across multiple calls. During long-running operations
    (like waiting for large files to process), the tool automatically
    sends keepalive messages every 2.5 seconds to prevent RPC sessions
    from timing out. This ensures reliable operation on large
    codebases.

4. **Edit Application**: Applies LSP `WorkspaceEdit` changes to files,
   computing unified diffs to show what changed. In dry-run mode,
   computes diffs without modifying files. When running in an
   interactive terminal, diffs are displayed with color and
   token-level highlighting to show exactly which characters changed.

## Limitations

- The tool only handles `WorkspaceEdit` in the `changes` or
  `documentChanges` format.
- Processing time depends on how long the Lean server takes to analyze
  each file (typically 1-3 seconds per file).

## License

This tool is part of the Lean reference manual and shares its license.
