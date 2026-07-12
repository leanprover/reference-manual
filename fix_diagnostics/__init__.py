"""
Fix Diagnostics Tool

A tool to automate fixing Lean diagnostics via LSP code actions.
"""

from .data import Diagnostic, CodeAction, ApplyResult
from .lsp_client import LspClient
from .core import (
    get_files,
    get_diagnostics,
    get_code_actions,
    apply_code_actions,
    lsp_start,
    lsp_stop,
)

__all__ = [
    "Diagnostic",
    "CodeAction",
    "ApplyResult",
    "LspClient",
    "get_files",
    "get_diagnostics",
    "get_code_actions",
    "apply_code_actions",
    "lsp_start",
    "lsp_stop",
]
