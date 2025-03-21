#!/usr/bin/env python3
import os
import sys
import shutil
import tempfile
import argparse
import subprocess
import shlex
from pathlib import Path

# This script is for deploying releases of the manual in response to
# pushed tags.

def parse_version(version_str):
    """
    Parse different types of version numbers into a structured format.

    Args:
        version_str (str): Version string like "4.18.0", "4.18.0-rc2", "nightly-2025-03-21"

    Returns:
        dict: Parsed version information
    """
    result = {
        "type": None,
        "major": None,
        "minor": None,
        "patch": None,
        "rc": None,
        "date": None
    }

    # Check for nightly builds (date-based versions)
    if version_str.startswith("nightly-"):
        result["type"] = "nightly"
        date_part = version_str.split("nightly-")[1]
        if len(date_part) == 10 and date_part.count("-") == 2:  # YYYY-MM-DD format
            year, month, day = map(int, date_part.split("-"))
            result["date"] = (year, month, day)
        else:
            return None
        return result

    # Handle semantic versioning (X.Y.Z or X.Y.Z-suffix)
    result["type"] = "semantic"

    # Split prerelease suffix if present
    if "-rc" in version_str:
        main_version, rc = version_str.split("-rc", 1)
        result["rc"] = int(rc)
    else:
        main_version = version_str

    # Parse version numbers
    version_parts = main_version.split(".")
    if len(version_parts) >= 1:
        try:
            result["major"] = int(version_parts[0])
        except ValueError:
            pass

    if len(version_parts) >= 2:
        try:
            result["minor"] = int(version_parts[1])
        except ValueError:
            pass

    if len(version_parts) >= 3:
        try:
            result["patch"] = int(version_parts[2])
        except ValueError:
            pass

    return result

def compare_versions(version1, version2):
    """
    Compare two version objects returned by parse_version.

    Args:
        version1 (dict): First version object
        version2 (dict): Second version object

    Returns:
        int or None: -1 if version1 < version2, 0 if equal, 1 if version1 > version2,
                    None if versions are incomparable

    Notes:
        - Semantic versions are considered greater than all other types
        - For semantic versions, comparison follows major.minor.patch-prerelease order
        - Prereleases are less than their corresponding release (e.g., 1.0.0-rc1 < 1.0.0)
        - For nightlies, more recent dates are greater
        - Returns None if the versions cannot be compared (unknown types)
    """
    # Handle None inputs
    if version1 is None or version2 is None:
        return None

    # Different types - semantic versions are greater than all others
    if version1["type"] == "semantic" and version2["type"] != "semantic":
        return 1
    if version1["type"] != "semantic" and version2["type"] == "semantic":
        return -1

    # Both are semantic versions
    if version1["type"] == "semantic" and version2["type"] == "semantic":
        # Compare major version
        if version1["major"] != version2["major"]:
            return 1 if version1["major"] > version2["major"] else -1

        # Compare minor version
        if version1["minor"] != version2["minor"]:
            return 1 if version1["minor"] > version2["minor"] else -1

        # Compare patch version
        if version1["patch"] != version2["patch"]:
            return 1 if version1["patch"] > version2["patch"] else -1

        # If we get here, base versions are equal, check rcs
        # Non-RC is greater than any RC
        if version1["rc"] is None and version2["rc"] is not None:
            return 1
        if version1["rc"] is not None and version2["rc"] is None:
            return -1
        if version1["rc"] != version2["rc"]:
            return 1 if version1["rc"] > version2["rc"] else -1

        # Versions are completely equal
        return 0

    # Both are nightly builds, compare dates
    if version1["type"] == "nightly" and version2["type"] == "nightly":
        if version1["date"] is None and version2["date"] is not None:
            return -1
        if version1["date"] is not None and version2["date"] is None:
            return 1
        if version1["date"] is None and version2["date"] is None:
            return 0

        # Compare year, month, day in sequence
        if version1["date"][0] != version2["date"][0]:  # year
            return 1 if version1["date"][0] > version2["date"][0] else -1
        if version1["date"][1] != version2["date"][1]:  # month
            return 1 if version1["date"][1] > version2["date"][1] else -1
        if version1["date"][2] != version2["date"][2]:  # day
            return 1 if version1["date"][2] > version2["date"][2] else -1

        # Dates are equal
        return 0

    # If we get here, the types are unknown or incomparable
    return None

#!/usr/bin/env python3
import os
import sys
import shutil
import tempfile
import argparse
import subprocess
from pathlib import Path

def eprint(*args, **kwargs):
    """Print to stderr instead of stdout"""
    print(*args, file=sys.stderr, **kwargs)

def parse_version(version_str):
    """
    Parse different types of version numbers into a structured format.

    Args:
        version_str (str): Version string like "4.18.0", "4.18.0-rc2", "nightly-2025-03-21"

    Returns:
        dict: Parsed version information with date as (year, month, day) tuple if present
    """
    result = {
        "type": None,
        "major": None,
        "minor": None,
        "patch": None,
        "rc": None,
        "date": None
    }

    # Check for nightly builds (date-based versions)
    if version_str.startswith("nightly-"):
        result["type"] = "nightly"
        date_part = version_str.split("nightly-")[1]
        if len(date_part) == 10 and date_part.count("-") == 2:  # YYYY-MM-DD format
            try:
                year, month, day = map(int, date_part.split("-"))
                result["date"] = (year, month, day)
            except ValueError:
                # If conversion fails, keep date as None
                pass
        return result

    # Handle semantic versioning (X.Y.Z or X.Y.Z-suffix)
    result["type"] = "semantic"

    # Split prerelease suffix if present
    if "-rc" in version_str:
        main_version, rc = version_str.split("-rc", 1)
        try:
            result["rc"] = int(rc)
        except ValueError:
            return None
    else:
        main_version = version_str

    # Parse version numbers
    version_parts = main_version.split(".")

    # No semantic versions with 1 component
    if len(version_parts) < 2:
        return None

    try:
        result["major"] = int(version_parts[0])
    except ValueError:
        return None

    if len(version_parts) >= 2:
        try:
            result["minor"] = int(version_parts[1])
        except ValueError:
            return None

    if len(version_parts) >= 3:
        try:
            result["patch"] = int(version_parts[2])
        except ValueError:
            return None

    return result

def compare_versions(version1, version2):
    """
    Compare two version objects returned by parse_version.

    Args:
        version1 (dict): First version object
        version2 (dict): Second version object

    Returns:
        int or None: -1 if version1 < version2, 0 if equal, 1 if version1 > version2,
                    None if versions are incomparable
    """
    # Handle None inputs
    if version1 is None or version2 is None:
        return None

    # Different types - semantic versions are greater than all others
    if version1["type"] == "semantic" and version2["type"] != "semantic":
        return 1
    if version1["type"] != "semantic" and version2["type"] == "semantic":
        return -1

    # Both are semantic versions
    if version1["type"] == "semantic" and version2["type"] == "semantic":
        # Compare major version
        if version1["major"] != version2["major"]:
            return 1 if version1["major"] > version2["major"] else -1

        # Compare minor version
        if version1["minor"] != version2["minor"]:
            return 1 if version1["minor"] > version2["minor"] else -1

        # Compare patch version
        if version1["patch"] != version2["patch"]:
            return 1 if version1["patch"] > version2["patch"] else -1

        # If we get here, base versions are equal, check prereleases
        # No prerelease is greater than any prerelease
        if version1["prerelease"] is None and version2["prerelease"] is not None:
            return 1
        if version1["prerelease"] is not None and version2["prerelease"] is None:
            return -1
        if version1["prerelease"] != version2["prerelease"]:
            # Simple lexicographical comparison for prereleases
            # This is simplified - a more robust implementation would parse rc1, rc2, etc.
            return 1 if version1["prerelease"] > version2["prerelease"] else -1

        # Versions are completely equal
        return 0

    # Both are nightly builds, compare dates
    if version1["type"] == "nightly" and version2["type"] == "nightly":
        if version1["date"] is None and version2["date"] is not None:
            return -1
        if version1["date"] is not None and version2["date"] is None:
            return 1
        if version1["date"] is None and version2["date"] is None:
            return 0

        # Compare year, month, day in sequence
        if version1["date"][0] != version2["date"][0]:  # year
            return 1 if version1["date"][0] > version2["date"][0] else -1
        if version1["date"][1] != version2["date"][1]:  # month
            return 1 if version1["date"][1] > version2["date"][1] else -1
        if version1["date"][2] != version2["date"][2]:  # day
            return 1 if version1["date"][2] > version2["date"][2] else -1

        # Dates are equal
        return 0

    # If we get here, the types are unknown or incomparable
    return None

def find_latest_version(versions_dir):
    """Find the latest version in the versions directory"""
    if not os.path.exists(versions_dir):
        return None

    version_dirs = [d for d in os.listdir(versions_dir)
                   if os.path.isdir(os.path.join(versions_dir, d)) and d != "latest"]

    if not version_dirs:
        return None

    # Parse all version strings
    parsed_versions = [(d, parse_version(d)) for d in version_dirs]

    # Filter out any unparseable versions
    valid_versions = [(d, pv) for d, pv in parsed_versions if pv is not None and pv["type"] is not None]

    if not valid_versions:
        return None

    # Find the latest version
    latest = valid_versions[0]
    for version_str, parsed_version in valid_versions[1:]:
        comparison = compare_versions(parsed_version, latest[1])
        if comparison == 1:  # If current version > latest so far
            latest = (version_str, parsed_version)

    return latest[0]

def run_git_command(command):
    """Run a git command and return the output"""
    print(f"\tRunning {shlex.join(command)}")
    result = subprocess.run(command, capture_output=True, text=True)
    if result.returncode != 0:
        eprint(f"Error executing git command: {shlex.join(command)}")
        eprint(f"Stdout: {result.stdout}\nStderr: {result.stderr}")
        sys.exit(1)
    return result.stdout.strip()

def git_has_changes():
    """Check if the git repository has any changes that could be
    committed, ignoring untracked files.  Returns True if there are
    added changes, False if working tree is clean.
    """
    result = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=no"],
        capture_output=True,
        text=True
    )

    # If successful and output is empty, there are no changes
    if result.returncode == 0 and not result.stdout.strip():
        return False
    return True

def deploy_version(source_dir, version, branch):
    """
    Deploy a version by copying from source directory to versioned directory.

    Args:
        source_dir (str): Source directory to copy content from
        version (str): Version string (will be used as the directory name)
        branch (str): Git branch to checkout
    """
    # Save current git branch to restore later
    current_branch = run_git_command(["git", "rev-parse", "--abbrev-ref", "HEAD"])

    try:
        # Create a temporary directory
        with tempfile.TemporaryDirectory() as temp_dir:
            print(f"Created temporary directory: {temp_dir}")

            # Copy source directory to temporary directory
            temp_source = os.path.join(temp_dir, "source_copy")
            shutil.copytree(source_dir, temp_source)
            print(f"Copied {source_dir} to temporary directory")

            # Checkout the specified branch
            print(f"Checking out branch: {branch}")
            run_git_command(["git", "switch", "-c", branch, "--track", "origin/" + branch])

            # The target directory for this version
            version_dir = version

            # Remove existing version directory if it exists
            if os.path.exists(version_dir):
                print(f"Removing existing version directory: {version_dir}")
                shutil.rmtree(version_dir)

            # Copy from temporary directory to version directory
            print(f"Copying content to version directory: {version_dir}")
            shutil.copytree(temp_source, version_dir)

            run_git_command(["git", "add", version_dir])

            # Update the "latest" symlink if needed
            latest_link = "latest"
            latest_version = find_latest_version(".")

            if latest_version:
                # If a symlink already exists, remove it
                if os.path.islink(latest_link):
                    os.unlink(latest_link)

                # Create relative symlink
                latest_target = latest_version
                os.symlink(latest_version, latest_link, target_is_directory=True)
                print(f"Updated 'latest' symlink to point to: {latest_version}")

                run_git_command(["git", "add", "latest"])

            if git_has_changes():
                run_git_command(["git", "commit", "-m", f"Deploy {version}"])
            else:
                print(f"Nothing changed, so no commit will be made.")

    finally:
        # Restore the original branch
        print(f"Restoring original branch: {current_branch}")
        run_git_command(["git", "switch", current_branch])

    print(f"Deployment of version {version} completed successfully.")

def main():
    parser = argparse.ArgumentParser(description="Deploys a build of the manual to the deployment branch")
    parser.add_argument("source_dir", help="Source directory to copy content from on the current branch")
    parser.add_argument("version", help="Lean version string (will be used as the directory name)")
    parser.add_argument("branch", help="Git branch for deployment (should be an orphan branch a la gh-pages)")

    args = parser.parse_args()

    print(f"Deploying from {args.source_dir} as version {args.version} into {args.branch}")

    deploy_version(args.source_dir, args.version, args.branch)

if __name__ == "__main__":
    main()
