"""Diff formatting with color and token-level highlighting."""

import difflib
import re
import sys
from typing import List, Tuple


class Colors:
    """ANSI color codes."""

    RESET = "\033[0m"
    RED = "\033[31m"
    GREEN = "\033[32m"
    CYAN = "\033[36m"
    YELLOW = "\033[33m"
    BOLD = "\033[1m"
    DIM = "\033[2m"
    REVERSE = "\033[7m"  # Swap foreground and background colors


def is_terminal() -> bool:
    """Check if output is going to a terminal."""
    return sys.stdout.isatty()


def highlight_inline_diff(old: str, new: str) -> Tuple[str, str]:
    """
    Highlight character-level differences within a line.

    Returns (highlighted_old, highlighted_new) with ANSI color codes
    marking the specific characters that changed.
    """
    # Use SequenceMatcher to find character-level differences
    matcher = difflib.SequenceMatcher(None, old, new)

    old_parts = []
    new_parts = []

    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == "equal":
            # Same in both
            old_parts.append(old[i1:i2])
            new_parts.append(new[j1:j2])
        elif tag == "replace":
            # Changed - use reverse video for visibility (works for all chars including whitespace)
            old_parts.append(f"{Colors.RED}{Colors.REVERSE}{old[i1:i2]}{Colors.RESET}{Colors.RED}")
            new_parts.append(
                f"{Colors.GREEN}{Colors.REVERSE}{new[j1:j2]}{Colors.RESET}{Colors.GREEN}"
            )
        elif tag == "delete":
            # Only in old - use reverse video
            old_parts.append(f"{Colors.RED}{Colors.REVERSE}{old[i1:i2]}{Colors.RESET}{Colors.RED}")
        elif tag == "insert":
            # Only in new - use reverse video
            new_parts.append(
                f"{Colors.GREEN}{Colors.REVERSE}{new[j1:j2]}{Colors.RESET}{Colors.GREEN}"
            )

    return "".join(old_parts), "".join(new_parts)


def format_colored_diff(filename: str, original: str, new: str) -> str:
    """
    Format a colored diff with token-level highlighting.

    Args:
        filename: Name of file for diff header
        original: Original content
        new: New content

    Returns:
        Colored diff string with token-level highlighting
    """
    if not is_terminal():
        # Not a terminal, return plain unified diff
        return _plain_diff(filename, original, new)

    lines_old = original.splitlines(keepends=False)
    lines_new = new.splitlines(keepends=False)

    # Use unified diff to get structure
    differ = difflib.unified_diff(
        lines_old,
        lines_new,
        fromfile=f"a/{filename}",
        tofile=f"b/{filename}",
        lineterm="",
    )

    output = []
    old_line_buffer: List[str] = []
    new_line_buffer: List[str] = []

    for line in differ:
        if line.startswith("---"):
            output.append(f"{Colors.BOLD}{Colors.RED}{line}{Colors.RESET}")
        elif line.startswith("+++"):
            output.append(f"{Colors.BOLD}{Colors.GREEN}{line}{Colors.RESET}")
        elif line.startswith("@@"):
            # Flush any buffered lines first
            if old_line_buffer and new_line_buffer:
                output.extend(_format_inline_changes(old_line_buffer, new_line_buffer))
                old_line_buffer = []
                new_line_buffer = []
            output.append(f"{Colors.CYAN}{line}{Colors.RESET}")
        elif line.startswith("-"):
            # Removed line - buffer it for inline diff
            old_line_buffer.append(line[1:])
        elif line.startswith("+"):
            # Added line - buffer it for inline diff
            new_line_buffer.append(line[1:])
        elif line.startswith(" "):
            # Flush any buffered lines first
            if old_line_buffer or new_line_buffer:
                output.extend(_format_inline_changes(old_line_buffer, new_line_buffer))
                old_line_buffer = []
                new_line_buffer = []
            # Context line
            output.append(f"{Colors.DIM}{line}{Colors.RESET}")
        else:
            output.append(line)

    # Flush any remaining buffered lines
    if old_line_buffer or new_line_buffer:
        output.extend(_format_inline_changes(old_line_buffer, new_line_buffer))

    return "\n".join(output)


def _format_inline_changes(old_lines: List[str], new_lines: List[str]) -> List[str]:
    """
    Format inline changes between old and new lines.

    If there's a 1:1 correspondence, show character-level diffs.
    Otherwise, show full line removals and additions.
    """
    result = []

    if len(old_lines) == 1 and len(new_lines) == 1:
        # Single line change - show inline diff
        old_highlighted, new_highlighted = highlight_inline_diff(
            old_lines[0], new_lines[0]
        )
        result.append(f"{Colors.RED}-{old_highlighted}{Colors.RESET}")
        result.append(f"{Colors.GREEN}+{new_highlighted}{Colors.RESET}")
    else:
        # Multiple lines or unbalanced - show full lines
        for line in old_lines:
            result.append(f"{Colors.RED}-{line}{Colors.RESET}")
        for line in new_lines:
            result.append(f"{Colors.GREEN}+{line}{Colors.RESET}")

    return result


def _plain_diff(filename: str, original: str, new: str) -> str:
    """Generate plain unified diff without colors."""
    diff_lines = difflib.unified_diff(
        original.splitlines(keepends=True),
        new.splitlines(keepends=True),
        fromfile=f"a/{filename}",
        tofile=f"b/{filename}",
        lineterm="",
    )
    return "".join(diff_lines)
