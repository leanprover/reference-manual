"""Core API functions for fix_diagnostics."""

import difflib
import atexit
from pathlib import Path
from typing import Optional, List, Dict, Any, Tuple, Union

from .lsp_client import LspClient
from .parser import run_build, parse_build_output
from .data import Diagnostic, CodeAction, ApplyResult, LspRange
from .diff_formatter import format_colored_diff


# Global LSP client for REPL persistence
_global_lsp_client: Optional[LspClient] = None


def lsp_start() -> LspClient:
    """
    Start a persistent LSP client for REPL use.

    This creates a global LSP client that will be reused across multiple
    function calls, avoiding the overhead of repeatedly starting and stopping
    the Lean server.

    The client will be automatically cleaned up on exit. You can manually
    stop it with lsp_stop() if needed.

    Returns:
        LspClient: The initialized global LSP client

    Example:
        >>> from fix_diagnostics import lsp_start, get_diagnostics, lsp_stop
        >>> lsp_start()
        >>> diagnostics = get_diagnostics()  # Reuses the global client
        >>> # ... more calls that reuse the client
        >>> lsp_stop()  # Optional - cleanup happens automatically on exit
    """
    global _global_lsp_client
    if _global_lsp_client is not None:
        lsp_stop()
    _global_lsp_client = LspClient()
    _global_lsp_client.initialize()
    atexit.register(lsp_stop)
    return _global_lsp_client


def lsp_stop() -> None:
    """
    Stop the global LSP client.

    This shuts down the persistent LSP client created by lsp_start().
    Normally you don't need to call this as cleanup happens automatically
    on exit, but it can be useful to restart the server or free resources.

    Example:
        >>> from fix_diagnostics import lsp_start, lsp_stop
        >>> lsp_start()
        >>> # ... do work
        >>> lsp_stop()  # Explicitly stop
        >>> lsp_start()  # Can start again
    """
    global _global_lsp_client
    if _global_lsp_client is not None:
        _global_lsp_client.shutdown()
        _global_lsp_client = None


def _utf16_offset_to_codepoint(text: str, utf16_offset: int) -> int:
    """
    Convert UTF-16 code unit offset to Python string (codepoint) index.

    LSP uses UTF-16 offsets, but Python strings are indexed by codepoints.
    Characters outside the BMP (like emoji) are 2 UTF-16 units but 1 codepoint.

    Args:
        text: The text string
        utf16_offset: UTF-16 code unit offset

    Returns:
        Codepoint index for Python string operations
    """
    utf16_count = 0
    for i, char in enumerate(text):
        if utf16_count >= utf16_offset:
            return i
        # Characters outside BMP are 2 UTF-16 code units (surrogate pairs)
        utf16_count += 2 if ord(char) > 0xFFFF else 1
    return len(text)


def _codepoint_to_utf16_offset(text: str, codepoint_index: int) -> int:
    """
    Convert Python string (codepoint) index to UTF-16 code unit offset.

    Args:
        text: The text string
        codepoint_index: Python string index

    Returns:
        UTF-16 code unit offset
    """
    utf16_count = 0
    for i, char in enumerate(text):
        if i >= codepoint_index:
            return utf16_count
        utf16_count += 2 if ord(char) > 0xFFFF else 1
    return utf16_count


def _calculate_range_size(lines: List[str], lsp_range: LspRange) -> int:
    """
    Calculate the size in codepoints of an LSP range.

    LSP ranges use UTF-16 offsets, so we convert to codepoints for measurement.

    Args:
        lines: File content split into lines (with line endings)
        lsp_range: LSP range structure (with UTF-16 offsets)

    Returns:
        Number of codepoints (Python characters) in the range
    """
    start_line = lsp_range["start"]["line"]
    start_utf16 = lsp_range["start"]["character"]
    end_line = lsp_range["end"]["line"]
    end_utf16 = lsp_range["end"]["character"]

    if start_line == end_line:
        # Single line range
        if start_line >= len(lines):
            return 0
        line = lines[start_line]
        start_cp = _utf16_offset_to_codepoint(line, start_utf16)
        end_cp = _utf16_offset_to_codepoint(line, end_utf16)
        return end_cp - start_cp
    else:
        # Multi-line range
        total = 0
        for line_num in range(start_line, end_line + 1):
            if line_num >= len(lines):
                break
            line = lines[line_num]

            if line_num == start_line:
                # First line: from start_utf16 to end of line
                start_cp = _utf16_offset_to_codepoint(line, start_utf16)
                total += len(line) - start_cp
            elif line_num == end_line:
                # Last line: from start to end_utf16
                end_cp = _utf16_offset_to_codepoint(line, end_utf16)
                total += end_cp
            else:
                # Middle lines: entire line
                total += len(line)

        return total


def _calculate_edit_magnitude(old_text: str, new_text: str) -> int:
    """
    Calculate magnitude of change between two strings.

    Uses difflib.SequenceMatcher to identify changed regions, and for each
    change (replace/delete/insert), takes the max of the old and new length.

    Args:
        old_text: Original text
        new_text: New text

    Returns:
        Edit magnitude (sum of max(old_len, new_len) for each change)
    """
    matcher = difflib.SequenceMatcher(None, old_text, new_text)
    magnitude = 0

    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag in ('replace', 'delete', 'insert'):
            magnitude += max(i2 - i1, j2 - j1)

    return magnitude


def _extract_text_from_range(lines: List[str], lsp_range: LspRange) -> str:
    """
    Extract text content from an LSP range.

    LSP ranges use UTF-16 offsets, so we convert to codepoints for string slicing.

    Args:
        lines: File content split into lines (with line endings)
        lsp_range: LSP range structure (with UTF-16 offsets)

    Returns:
        Text content in the range
    """
    start_line = lsp_range["start"]["line"]
    start_utf16 = lsp_range["start"]["character"]
    end_line = lsp_range["end"]["line"]
    end_utf16 = lsp_range["end"]["character"]

    if start_line == end_line:
        # Single line range
        if start_line < len(lines):
            line = lines[start_line]
            start_cp = _utf16_offset_to_codepoint(line, start_utf16)
            end_cp = _utf16_offset_to_codepoint(line, end_utf16)
            return line[start_cp:end_cp]
        return ""
    else:
        # Multi-line range
        result_parts = []
        for line_num in range(start_line, end_line + 1):
            if line_num >= len(lines):
                break
            line = lines[line_num]

            if line_num == start_line:
                # First line: from start_utf16 to end
                start_cp = _utf16_offset_to_codepoint(line, start_utf16)
                result_parts.append(line[start_cp:])
            elif line_num == end_line:
                # Last line: from start to end_utf16
                end_cp = _utf16_offset_to_codepoint(line, end_utf16)
                result_parts.append(line[:end_cp])
            else:
                # Middle lines: entire line
                result_parts.append(line)

        return "".join(result_parts)


def _calculate_edit_size(edit: Dict[str, Any], file_path: Path) -> int:
    """
    Calculate the magnitude of a WorkspaceEdit.

    Args:
        edit: LSP WorkspaceEdit
        file_path: Path to the file being edited

    Returns:
        Total edit magnitude across all text edits
    """
    if not edit:
        return 0

    total_magnitude = 0
    file_uri = file_path.absolute().as_uri()

    # Read file content once
    try:
        content = file_path.read_text()
        lines = content.splitlines(keepends=True)
    except Exception:
        return 0

    # Handle workspace edit with changes
    if "changes" in edit:
        if file_uri in edit["changes"]:
            text_edits = edit["changes"][file_uri]

            for text_edit in text_edits:
                # Extract old text from range
                old_text = _extract_text_from_range(lines, text_edit["range"])
                new_text = text_edit["newText"]

                # Calculate magnitude
                total_magnitude += _calculate_edit_magnitude(old_text, new_text)

    # Handle documentChanges
    elif "documentChanges" in edit:
        for change in edit["documentChanges"]:
            if "textDocument" in change and "edits" in change:
                if change["textDocument"]["uri"] == file_uri:
                    text_edits = change["edits"]

                    for text_edit in text_edits:
                        old_text = _extract_text_from_range(lines, text_edit["range"])
                        new_text = text_edit["newText"]
                        total_magnitude += _calculate_edit_magnitude(old_text, new_text)

    return total_magnitude


def get_files(build_cmd: str = "lake build") -> List[Path]:
    """
    Find files with diagnostics from lake build output.

    Args:
        build_cmd: Build command to run (default: "lake build")

    Returns:
        List[Path]: Files with diagnostics, ordered by build output

    Raises:
        FileNotFoundError: If not in a Lake project directory
    """
    exit_code, stdout, stderr = run_build(build_cmd)
    return parse_build_output(stdout, stderr)


def get_diagnostics(
    files: Optional[List[Path]] = None, lsp_client: Optional[LspClient] = None
) -> List[Diagnostic]:
    """
    Get diagnostics from LSP for files.

    If a global LSP client has been started with lsp_start(), it will be
    reused automatically. Otherwise, a temporary client is created.

    Args:
        files: List of Path objects, or None to call get_files()
        lsp_client: Optional LSP client to reuse

    Returns:
        List[Diagnostic]
    """
    if files is None:
        files = get_files()

    if not files:
        return []

    # Check for global client first, then fall back to temporary
    if lsp_client is None:
        if _global_lsp_client is not None:
            lsp_client = _global_lsp_client
            own_client = False
        else:
            # Create temporary client
            lsp_client = LspClient()
            lsp_client.initialize()
            own_client = True
    else:
        own_client = False

    try:
        all_diagnostics = []

        # Open all files first (non-blocking)
        # This allows the Lean server to start processing files in parallel
        opened_files = []
        for file_path in files:
            abs_path = file_path.absolute()

            # Read file content
            try:
                text = abs_path.read_text()
            except Exception as e:
                print(f"Warning: Could not read {abs_path}: {e}")
                continue

            # Open in LSP (non-blocking)
            assert lsp_client is not None
            lsp_client.did_open(abs_path, text)
            opened_files.append(abs_path)

        # Now get diagnostics for each file (blocking)
        for abs_path in opened_files:
            assert lsp_client is not None
            lsp_diagnostics = lsp_client.get_diagnostics(abs_path)

            # Read file content for range size calculation
            try:
                content = abs_path.read_text()
                lines = content.splitlines(keepends=True)
            except Exception:
                lines = []

            # Convert to our Diagnostic model
            for lsp_diag in lsp_diagnostics:
                lsp_range = lsp_diag["range"]

                # Calculate range size
                range_size = _calculate_range_size(lines, lsp_range) if lines else 0

                diag = Diagnostic(
                    file=abs_path,
                    line=lsp_diag["range"]["start"]["line"],
                    col=lsp_diag["range"]["start"]["character"],
                    severity=lsp_diag.get("severity", 1),
                    message=lsp_diag.get("message", ""),
                    code=lsp_diag.get("code"),
                    source=lsp_diag.get("source"),
                    range=lsp_range,
                    range_size=range_size,
                )
                all_diagnostics.append(diag)

        return all_diagnostics

    finally:
        if own_client:
            assert lsp_client is not None
            lsp_client.shutdown()


def _extract_widget_edits(message: Dict[str, Any]) -> List[Dict[str, Any]]:
    """
    Extract code action edits from widget components in interactive diagnostic message.

    Args:
        message: Interactive diagnostic message with widget components

    Returns:
        List of dicts with 'title', 'suggestion', and 'range' for each widget edit
    """
    edits = []
    append_items = message.get('append', [])

    for item in append_items:
        tags = item.get('tag', [])
        for tag in tags:
            if 'widget' not in tag:
                continue

            widget = tag['widget']
            wi = widget.get('wi', {})
            widget_id = wi.get('id')
            props = wi.get('props', {})

            # Handle tryThisDiffWidget - the common "Try this:" suggestion widget
            if widget_id == 'Lean.Meta.Hint.tryThisDiffWidget':
                suggestion = props.get('suggestion')
                edit_range = props.get('range')

                if suggestion is not None and edit_range is not None:
                    # Create a descriptive title
                    if len(suggestion) < 50:
                        title = f"Replace with '{suggestion}'"
                    else:
                        title = f"Replace with suggested text ({len(suggestion)} chars)"

                    edits.append({
                        'title': title,
                        'suggestion': suggestion,
                        'range': edit_range,
                    })

    return edits


def get_code_actions(
    diagnostics: Union[Diagnostic, List[Diagnostic], None] = None,
    lsp_client: Optional[LspClient] = None,
) -> List[CodeAction]:
    """
    Get code actions for diagnostics.

    If a global LSP client has been started with lsp_start(), it will be
    reused automatically. Otherwise, a temporary client is created.

    Args:
        diagnostics: Single Diagnostic, list of Diagnostic objects, or None to call get_diagnostics()
        lsp_client: Optional LSP client to reuse

    Returns:
        List[CodeAction]: Actions with back-pointers to diagnostics
    """
    # Handle single diagnostic case
    if isinstance(diagnostics, Diagnostic):
        diagnostics = [diagnostics]
    elif diagnostics is None:
        diagnostics = get_diagnostics(lsp_client=lsp_client)

    if not diagnostics:
        return []

    # Check for global client first, then fall back to temporary
    if lsp_client is None:
        if _global_lsp_client is not None:
            lsp_client = _global_lsp_client
            own_client = False
        else:
            # Create temporary client
            lsp_client = LspClient()
            lsp_client.initialize()
            own_client = True
    else:
        own_client = False

    try:
        all_actions = []

        # Group diagnostics by file for efficiency
        by_file: Dict[Path, List[Diagnostic]] = {}
        for diag in diagnostics:
            if diag.file not in by_file:
                by_file[diag.file] = []
            by_file[diag.file].append(diag)

        # Open all files first (non-blocking)
        for file_path in by_file.keys():
            try:
                text = file_path.read_text()
            except Exception as e:
                print(f"Warning: Could not read {file_path}: {e}")
                continue

            assert lsp_client is not None
            lsp_client.did_open(file_path, text)

        # Wait for files to be processed and query code actions
        for file_path, file_diags in by_file.items():
            # Ensure file is processed before querying actions
            assert lsp_client is not None
            lsp_client.get_diagnostics(file_path)

            # Query interactive diagnostics to get widget-based code actions
            interactive_diags_by_position: Dict[Tuple[int, int], Dict[str, Any]] = {}
            try:
                assert lsp_client is not None
                interactive_diags = lsp_client.get_interactive_diagnostics(file_path)
                for int_diag in interactive_diags:
                    pos = (
                        int_diag['range']['start']['line'],
                        int_diag['range']['start']['character'],
                    )
                    interactive_diags_by_position[pos] = int_diag
            except Exception as e:
                print(f"Warning: Could not get interactive diagnostics for {file_path}: {e}")

            # Query code actions for each diagnostic
            for diag in file_diags:
                # First, check for widget-based actions from interactive diagnostics
                pos = (diag.line, diag.col)
                if pos in interactive_diags_by_position:
                    int_diag = interactive_diags_by_position[pos]
                    message = int_diag.get('message', {})
                    widget_edits = _extract_widget_edits(message)

                    for widget_edit in widget_edits:
                        # Create WorkspaceEdit from widget suggestion
                        file_uri = file_path.absolute().as_uri()
                        edit = {
                            'changes': {
                                file_uri: [
                                    {
                                        'range': widget_edit['range'],
                                        'newText': widget_edit['suggestion'],
                                    }
                                ]
                            }
                        }

                        # Calculate edit size
                        edit_size = _calculate_edit_size(edit, file_path)

                        action = CodeAction(
                            title=widget_edit['title'],
                            kind='quickfix',
                            edit=edit,
                            diagnostic=diag,
                            edit_size=edit_size,
                        )
                        all_actions.append(action)

                # Also query standard LSP code actions
                # Convert diagnostic to LSP format
                lsp_diag = diag.to_lsp()

                # Request code actions
                try:
                    assert lsp_client is not None
                    lsp_actions = lsp_client.code_action(
                        file_path, diag.line, diag.col, [lsp_diag]
                    )
                except Exception as e:
                    print(
                        f"Warning: Could not get code actions for {file_path}:{diag.line}: {e}"
                    )
                    continue

                # Convert to CodeAction objects
                for lsp_action in lsp_actions:
                    edit = lsp_action.get("edit") or lsp_action.get("command") or {}

                    # Calculate edit size
                    edit_size = _calculate_edit_size(edit, file_path)

                    action = CodeAction(
                        title=lsp_action.get("title", ""),
                        kind=lsp_action.get("kind"),
                        edit=edit,
                        diagnostic=diag,
                        edit_size=edit_size,
                    )
                    all_actions.append(action)

        return all_actions

    finally:
        if own_client:
            assert lsp_client is not None
            lsp_client.shutdown()


def apply_code_actions(
    actions: Union[CodeAction, List[CodeAction]], dry_run: bool = True
) -> List[ApplyResult]:
    """
    Apply code actions to files.

    Args:
        actions: Single CodeAction or list of CodeAction objects
        dry_run: If True, compute diffs but don't modify files (default: True)

    Returns:
        List[ApplyResult]: One result per action
    """
    # Handle single action case
    if isinstance(actions, CodeAction):
        actions = [actions]

    results = []

    for action in actions:
        try:
            file_path = action.diagnostic.file

            # Read original content
            original_content = file_path.read_text()

            # Apply edit to get new content
            new_content = _apply_edit(original_content, action.edit, file_path)

            # Compute diff
            diff = _compute_diff(str(file_path), original_content, new_content)

            if not dry_run:
                # Write new content
                file_path.write_text(new_content)

            results.append(
                ApplyResult(success=True, action=action, diff=diff, error=None)
            )

        except Exception as e:
            results.append(
                ApplyResult(success=False, action=action, diff="", error=str(e))
            )

    return results


def _apply_edit(content: str, edit: Dict[str, Any], file_path: Path) -> str:
    """
    Apply LSP WorkspaceEdit to content.

    Args:
        content: Original file content
        edit: LSP WorkspaceEdit or Command
        file_path: Path to the file being edited

    Returns:
        Modified content
    """
    if not edit:
        return content

    # Handle workspace edit
    if "changes" in edit:
        # Map of file URI → list of TextEdit
        file_uri = file_path.absolute().as_uri()

        if file_uri not in edit["changes"]:
            # No changes for this file
            return content

        text_edits = edit["changes"][file_uri]

        # Sort edits by position (reverse order to apply bottom-up)
        # This ensures that earlier edits don't invalidate later positions
        sorted_edits = sorted(
            text_edits,
            key=lambda e: (
                e["range"]["start"]["line"],
                e["range"]["start"]["character"],
            ),
            reverse=True,
        )

        lines = content.splitlines(keepends=True)

        for text_edit in sorted_edits:
            start_line = text_edit["range"]["start"]["line"]
            start_utf16 = text_edit["range"]["start"]["character"]
            end_line = text_edit["range"]["end"]["line"]
            end_utf16 = text_edit["range"]["end"]["character"]
            new_text = text_edit["newText"]

            # Handle edge case: empty file or lines list
            if not lines:
                return new_text

            # Apply edit (convert UTF-16 offsets to codepoints)
            if start_line == end_line:
                # Single line edit
                if start_line < len(lines):
                    line = lines[start_line]
                    start_cp = _utf16_offset_to_codepoint(line, start_utf16)
                    end_cp = _utf16_offset_to_codepoint(line, end_utf16)
                    lines[start_line] = line[:start_cp] + new_text + line[end_cp:]
            else:
                # Multi-line edit
                if start_line < len(lines) and end_line < len(lines):
                    first_line = lines[start_line]
                    start_cp = _utf16_offset_to_codepoint(first_line, start_utf16)
                    last_line = lines[end_line]
                    end_cp = _utf16_offset_to_codepoint(last_line, end_utf16)
                    lines[start_line : end_line + 1] = [first_line[:start_cp] + new_text + last_line[end_cp:]]

        return "".join(lines)

    # Handle documentChanges (more complex edit format)
    if "documentChanges" in edit:
        # For simplicity, we only handle textDocument/edit changes
        for change in edit["documentChanges"]:
            if "textDocument" in change and "edits" in change:
                file_uri = change["textDocument"]["uri"]
                expected_uri = file_path.absolute().as_uri()

                if file_uri == expected_uri:
                    text_edits = change["edits"]

                    # Sort and apply edits (same logic as above)
                    sorted_edits = sorted(
                        text_edits,
                        key=lambda e: (
                            e["range"]["start"]["line"],
                            e["range"]["start"]["character"],
                        ),
                        reverse=True,
                    )

                    lines = content.splitlines(keepends=True)

                    for text_edit in sorted_edits:
                        start_line = text_edit["range"]["start"]["line"]
                        start_utf16 = text_edit["range"]["start"]["character"]
                        end_line = text_edit["range"]["end"]["line"]
                        end_utf16 = text_edit["range"]["end"]["character"]
                        new_text = text_edit["newText"]

                        if not lines:
                            return new_text

                        # Apply edit (convert UTF-16 offsets to codepoints)
                        if start_line == end_line:
                            if start_line < len(lines):
                                line = lines[start_line]
                                start_cp = _utf16_offset_to_codepoint(line, start_utf16)
                                end_cp = _utf16_offset_to_codepoint(line, end_utf16)
                                lines[start_line] = line[:start_cp] + new_text + line[end_cp:]
                        else:
                            if start_line < len(lines) and end_line < len(lines):
                                first_line = lines[start_line]
                                start_cp = _utf16_offset_to_codepoint(first_line, start_utf16)
                                last_line = lines[end_line]
                                end_cp = _utf16_offset_to_codepoint(last_line, end_utf16)
                                lines[start_line : end_line + 1] = [
                                    first_line[:start_cp] + new_text + last_line[end_cp:]
                                ]

                    return "".join(lines)

    return content


def _compute_diff(filename: str, original: str, new: str) -> str:
    """
    Compute unified diff with color and token-level highlighting.

    If output is to a terminal, uses colored output with token-level
    highlighting. Otherwise, uses plain unified diff.

    Args:
        filename: Name of file for diff header
        original: Original content
        new: New content

    Returns:
        Unified diff string (colored if terminal)
    """
    return format_colored_diff(filename, original, new)
