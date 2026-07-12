"""Data models for fix_diagnostics."""

from dataclasses import dataclass
from pathlib import Path
from typing import Optional, TypedDict


class LspPosition(TypedDict):
    """LSP Position structure."""
    line: int
    character: int


class LspRange(TypedDict):
    """LSP Range structure."""
    start: LspPosition
    end: LspPosition


@dataclass
class Diagnostic:
    """A diagnostic from the Lean LSP server."""

    file: Path
    line: int  # 0-based (LSP protocol) - start line for convenience
    col: int  # 0-based (LSP protocol) - start character (UTF-16 offset) for convenience
    severity: int  # LSP DiagnosticSeverity: 1=Error, 2=Warning, 3=Info, 4=Hint
    message: str
    code: Optional[str] = None
    source: Optional[str] = None
    range: LspRange = None  # Full LSP range (with UTF-16 offsets)
    range_size: int = 0  # Size in codepoints (Python characters) of the diagnostic's range

    def to_lsp(self):
        """Convert to LSP diagnostic format for code action request."""
        return {
            "range": self.range if self.range else {
                "start": {"line": self.line, "character": self.col},
                "end": {"line": self.line, "character": self.col},
            },
            "severity": self.severity,
            "message": self.message,
            "code": self.code,
            "source": self.source,
        }

    def __repr__(self):
        severity_names = {1: "error", 2: "warning", 3: "info", 4: "hint"}
        severity_str = severity_names.get(self.severity, str(self.severity))
        return f"Diagnostic({self.file}:{self.line}:{self.col} [{severity_str}] {self.message})"


@dataclass
class CodeAction:
    """A code action from the LSP server."""

    title: str
    kind: Optional[str]
    edit: dict  # LSP WorkspaceEdit or Command (with UTF-16 offsets)
    diagnostic: Diagnostic  # Back-pointer to diagnostic this action addresses
    edit_size: int = 0  # Magnitude of edit in codepoints (sum of max(old, new) for each change)

    def __repr__(self):
        return f"CodeAction({self.title!r} for {self.diagnostic.file}:{self.diagnostic.line}, size={self.edit_size})"


@dataclass
class ApplyResult:
    """Result of applying a single code action."""

    success: bool
    action: CodeAction
    diff: str  # Unified diff for this specific action's changes
    error: Optional[str] = None

    def __repr__(self):
        if self.success:
            return f"ApplyResult(success, {self.action.title!r})"
        else:
            return f"ApplyResult(failed, {self.action.title!r}, error={self.error!r})"
