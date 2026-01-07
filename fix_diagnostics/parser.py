"""Parse lake build output to find files with diagnostics."""

import re
import subprocess
from pathlib import Path
from typing import List, Tuple


def run_build(build_cmd: str = "lake build") -> Tuple[int, str, str]:
    """
    Run build command and return output.

    Args:
        build_cmd: Build command to run (default: "lake build")

    Returns:
        Tuple of (exit_code, stdout, stderr)

    Raises:
        FileNotFoundError: If not in a Lake project directory
    """
    # Check we're in a Lake project
    cwd = Path.cwd()
    if not (cwd / "lakefile.toml").exists() and not (cwd / "lakefile.lean").exists():
        raise FileNotFoundError(
            "Not in a Lake project directory. "
            "Current directory must contain lakefile.toml or lakefile.lean"
        )

    result = subprocess.run(
        build_cmd.split(), capture_output=True, text=True, check=False
    )
    return result.returncode, result.stdout, result.stderr


def parse_build_output(stdout: str, stderr: str) -> List[Path]:
    """
    Parse lake build output to find files with diagnostics.

    Returns list of Path objects, ordered by first appearance in build output.

    Expected format: file.lean:line:col: severity: message

    Args:
        stdout: Standard output from build
        stderr: Standard error from build

    Returns:
        List[Path]: Files with diagnostics, in order of appearance
    """
    seen = set()
    files = []

    # Combine stdout and stderr
    output = stdout + "\n" + stderr

    # Regex: capture file paths from diagnostic lines
    # Match lines like: warning: path/to/file.lean:123:45: message
    # or: path/to/file.lean:123:45: error: message
    pattern1 = r"^(?:error|warning|info):\s*([^:]+\.lean):\d+:\d+"
    pattern2 = r"^([^:]+\.lean):\d+:\d+:\s*(?:error|warning|info):"

    for line in output.splitlines():
        match = re.match(pattern1, line)
        if not match:
            match = re.match(pattern2, line)
        if match:
            file_path = Path(match.group(1))
            if file_path not in seen:
                seen.add(file_path)
                files.append(file_path)

    return files
