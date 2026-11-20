#!/usr/bin/env python3
import argparse
import json
import os
import re
import urllib.request
from release_utils import (
    run_git_command,
    is_git_ancestor,
    find_latest_version,
    find_latest_stable_version,
)
from pathlib import Path


def add_metadata(directory, version_name, site_dir, extensions=(".html", ".htm")):
    """
    Recursively walk through `directory`, find all HTML files,
    and insert extra elements at the beginning of `<head>`.

    Presently we insert an instruction to robots not to crawl

    Args:
      directory (Path): The directory in which to recursively modify files
      version_name (str): The version name (e.g. "4.25.0-rc2", "latest", "stable")
      site_dir (str): The site directory for canonical URLs ("reference" or "tutorials")
    """
    for root, _, files in os.walk(directory):
        for filename in files:
            if filename.lower().endswith(extensions):
                filepath = os.path.join(root, filename)
                with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
                    content = f.read()

                # Only edit if <head> exists and we haven't already added the meta tag
                if "<head>" in content and 'name="robots"' not in content:
                    href = f"https://lean-lang.org/doc/{site_dir}/{root}/{filename}".removesuffix(
                        "index.html"
                    )
                    noindex = (
                        ""
                        if version_name == "latest"
                        else '\n<meta name="robots" content="noindex">'
                    )
                    new_content = content.replace(
                        "<head>",
                        f'''<head>{noindex}
                        <link rel="canonical" href="{href}" />
                        ''',
                    )

                    # Write back the modified file
                    with open(filepath, "w", encoding="utf-8") as f:
                        f.write(new_content)
                    print(f"Updated: {filepath}")
                else:
                    print(f"Skipped: {filepath}")


def fetch_verso_unicode_js():
    """
    Fetch the latest Unicode input JavaScript files from Verso's main branch.
    Returns a dict mapping filename to bytes content.
    """
    base_url = "https://raw.githubusercontent.com/leanprover/verso/refs/heads/main/static-web/search/"
    filenames = ["unicode-input.min.js", "unicode-input-component.min.js"]
    result = {}
    for filename in filenames:
        url = base_url + filename
        print(f"Fetching {url}")
        with urllib.request.urlopen(url) as response:
            result[filename] = response.read()
    return result


def replace_unicode_js(deploy_dir, verso_js):
    """
    Replace the Unicode input JavaScript files in every version directory with
    the latest versions fetched from Verso's main branch.

    Handles both historical path layouts:
      - static/search/   (versions up to ~4.21)
      - -verso-search/   (versions from ~4.22 onwards)

    Args:
        deploy_dir (str): Directory containing all versions
        verso_js (dict): Mapping from filename to bytes content
    """
    for inner in Path(deploy_dir).iterdir():
        if inner.is_dir() and (inner / "index.html").is_file():
            for search_dir in [inner / "-verso-search", inner / "static" / "search"]:
                if search_dir.is_dir():
                    for filename, content in verso_js.items():
                        filepath = search_dir / filename
                        if filepath.exists():
                            with open(filepath, "wb") as f:
                                f.write(content)
                            print(f"Replaced: {filepath}")
                        else:
                            print(f"Not found, skipping: {filepath}")


# The Verso commit from which the permalink and search scripts are taken.
VERSO_SCRIPTS_REF = "72f606748cc5f4e1ce9f6d0b7abbd37cf767c9fd"


def fetch_verso_scripts():
    """
    Fetch Verso's permalink and search scripts at VERSO_SCRIPTS_REF.
    Returns a dict mapping filename to text content.

    If the environment variable VERSO_SCRIPTS_DIR is set, the files are read from that directory
    instead, laid out as in Verso's static-web/ directory.
    """
    paths = {
        "find.js": "find.js",
        "search-highlight.js": "search/search-highlight.js",
        "search-box.js": "search/search-box.js",
    }
    local_dir = os.environ.get("VERSO_SCRIPTS_DIR")
    result = {}
    for filename, path in paths.items():
        if local_dir:
            result[filename] = Path(local_dir, path).read_text(encoding="utf-8")
        else:
            url = f"https://raw.githubusercontent.com/leanprover/verso/{VERSO_SCRIPTS_REF}/static-web/{path}"
            print(f"Fetching {url}")
            with urllib.request.urlopen(url) as response:
                result[filename] = response.read().decode("utf-8")
    return result


def update_find_page(version_dir, find_js):
    """
    Replace the script in a version's find/index.html with Verso's current find.js.

    The page's cross-reference data is kept. Older pages declare it with `let xref`, and the
    updated page declares it as `window.xref`. Here, we rewrite all to `window.xref`, which
    is where the current script reads it from.

    Args:
        version_dir (Path): The version's directory
        find_js (str): The contents of Verso's find.js
    """
    page = version_dir / "find" / "index.html"
    if not page.is_file():
        return
    content = page.read_text(encoding="utf-8")
    match = re.search(r"(?:let |window\.)xref = ", content)
    if match is None:
        print(f"No cross-reference data, skipping: {page}")
        return
    _, data_end = json.JSONDecoder().raw_decode(content, match.end())
    script_end = content.find("</script>", data_end)
    if script_end < 0:
        print(f"Unexpected find page layout, skipping: {page}")
        return
    new_content = (
        content[: match.start()]
        + "window.xref = "
        + content[match.end() : data_end]
        + ";\n"
        + find_js
        + "\n"
        + content[script_end:]
    )
    page.write_text(new_content, encoding="utf-8")
    print(f"Updated: {page}")


# The search-result snippet rendering in search-box.js: the snippet callback in highlightTextResult.
SNIPPET_START = "const highlightedSnippets = limitedSnippets.map((snippet) => {"
SNIPPET_END = re.compile(r"return elem;\s*\}\);")


def snippet_code(search_box_js):
    """Returns the start and end of the snippet rendering code in search-box.js, if present."""
    start = search_box_js.find(SNIPPET_START)
    if start < 0 or search_box_js.find(SNIPPET_START, start + 1) >= 0:
        return None
    end = SNIPPET_END.search(search_box_js, start)
    if end is None:
        return None
    return start, end.end()


def update_search_scripts(version_dir, verso_scripts):
    """
    Update a version's search scripts to Verso's current versions.

    search-highlight.js is replaced. In search-box.js, the snippet rendering for search results is
    replaced, because the rest of the file depends on the version of the search index.

    Args:
        version_dir (Path): The version's directory
        verso_scripts (dict): Mapping from filename to text content, from fetch_verso_scripts
    """
    search_dir = version_dir / "-verso-search"
    highlight = search_dir / "search-highlight.js"
    if highlight.is_file():
        highlight.write_text(verso_scripts["search-highlight.js"], encoding="utf-8")
        print(f"Replaced: {highlight}")

    box = search_dir / "search-box.js"
    if box.is_file():
        current = verso_scripts["search-box.js"]
        new_range = snippet_code(current)
        if new_range is None:
            raise Exception("Snippet rendering not found in Verso's search-box.js")
        content = box.read_text(encoding="utf-8")
        old_range = snippet_code(content)
        if old_range is None:
            print(f"Snippet rendering not found, skipping: {box}")
            return
        new_content = (
            content[: old_range[0]]
            + current[new_range[0] : new_range[1]]
            + content[old_range[1] :]
        )
        box.write_text(new_content, encoding="utf-8")
        print(f"Updated: {box}")


def update_verso_scripts(deploy_dir, verso_scripts):
    """
    Update the permalink and search scripts in every version directory.

    Args:
        deploy_dir (str): Directory containing all versions
        verso_scripts (dict): Mapping from filename to text content, from fetch_verso_scripts
    """
    for inner in Path(deploy_dir).iterdir():
        if inner.is_dir() and (inner / "index.html").is_file():
            update_find_page(inner, verso_scripts["find.js"])
            update_search_scripts(inner, verso_scripts)


# This function is the right thing to change to change the
# content of the overlays that are applied.
#
# See the README.md in this directory for more about the contract
# that should be satisfied by how overlays change over time.
def apply_overlays(deploy_dir, site_dir):
    """
    Apply desired overlays inside current directory.

    Args:
        deploy_dir (str): Directory containing all versions
        site_dir (str): The site directory for canonical URLs ("reference" or "tutorials")
    """
    latest_version = find_latest_version(deploy_dir)
    latest_stable_version = find_latest_stable_version(deploy_dir)
    print(f"overlay.py: the latest lean version is {latest_version}")
    print(f"overlay.py: the latest stable lean version is {latest_stable_version}")
    verso_js = fetch_verso_unicode_js()
    replace_unicode_js(deploy_dir, verso_js)
    update_verso_scripts(deploy_dir, fetch_verso_scripts())
    header = (
        "// This file was automatically generated by reference-manual/deploy/overlay.py"
    )
    for inner in Path(deploy_dir).iterdir():
        # Check for index.html to identify version directories
        if inner.is_dir() and (inner / "index.html").is_file():
            # Generate metadata.js only for reference manual (it has static/)
            if site_dir == "reference" and (inner / "static").is_dir():
                filename = inner / "static" / "metadata.js"
                content = f'{header}\nwindow.metadata = {{versionString: "{inner}"}};\n'
                if str(inner) == latest_version or str(inner) == "latest":
                    content += f"window.metadata.latest = true;\n"
                if str(inner) == latest_stable_version or str(inner) == "stable":
                    content += f"window.metadata.stable = true;\n"
                with open(filename, "a") as file:
                    file.write(content)

            # Add appropriate metadata to every file at every version
            add_metadata(inner, str(inner), site_dir)


def deploy_overlays(deploy_dir, src_branch, tgt_branch, site_dir):
    """
    Apply desired overlays inside deploy_dir
    Args:
        deploy_dir (str): Directory that contains all versions of the site.
        This is the content we expect to find at branch `src_branch`, and
        this function modifies it in place to produce a repository state
        suitable for committing to branch `tgt_branch`.
        src_branch (str): Git branch to apply overlays to
        tgt_branch (str): Git branch to commit to
        site_dir (str): The site directory for canonical URLs ("reference" or "tutorials")
    """
    os.chdir(deploy_dir)
    # Save current git commit to restore later
    current_branch = run_git_command(["git", "branch", "--show-current"])
    try:
        if is_git_ancestor(tgt_branch, src_branch):
            raise Exception(
                f"Git merge will have bad behavior if {tgt_branch} is an ancestor of {src_branch}, try creating a vacuous commit on {tgt_branch} first."
            )
        run_git_command(["git", "switch", src_branch])

        if find_latest_version(deploy_dir) is None:
            print(f"No version directories found on {src_branch}, nothing to overlay")
            return

        print(f"Applying overlays...")
        apply_overlays(deploy_dir, site_dir)
        print(f"Creating merge commit...")
        # Add version directories and aliases (stable may not exist for RC releases)
        add_paths = ["4*", "latest"]
        if Path("stable").exists():
            add_paths.append("stable")
        run_git_command(["git", "add"] + add_paths)
        # We create the overlay commit based on src_branch...
        run_git_command(["git", "commit", "-m", "overlay.py: apply overlays"])
        # ...but we actually want to add it to the history of
        # tgt_branch. This is the moment when it is problematic
        # for tgt_branch to be an ancestor of src_branch, because then this
        # will be a no-op, despite --no-ff.
        #
        # All of this complication is due to the fact that "-s theirs" doesn't
        # exist and "-X theirs" isn't what we want.
        # (see https://stackoverflow.com/questions/4911794/git-command-for-making-one-branch-like-another/4912267#4912267 for context)
        run_git_command(
            [
                "git",
                "merge",
                "-m",
                "merge overlays",
                "--no-ff",
                "--no-edit",
                "-s",
                "ours",
                tgt_branch,
            ]
        )
        run_git_command(["git", "switch", tgt_branch])
        run_git_command(["git", "reset", "--hard", src_branch, "--"])
        run_git_command(["git", "switch", src_branch])
        # Rewind the src_branch back past the merge commit and the
        # overlay commit. This cleanup probably isn't strictly necessary
        # in prod, since we don't expect our GH Actions caller script to
        # push the src_branch, but it's helpful for testing.
        run_git_command(["git", "reset", "--hard", "HEAD^^"])
    finally:
        run_git_command(["git", "switch", current_branch])


def main():
    parser = argparse.ArgumentParser(
        description="Applies overlays to a site predeployment branch"
    )
    parser.add_argument("deploy_dir", help="Directory to operate on")
    parser.add_argument("src_branch", help="Git branch to apply overlays to")
    parser.add_argument("tgt_branch", help="Git branch to commit to")
    parser.add_argument(
        "--site-dir",
        default="reference",
        choices=["reference", "tutorials"],
        help="Site directory for canonical URLs (default: reference)",
    )

    args = parser.parse_args()

    print(
        f"Applying overlays to directory {args.deploy_dir} branch {args.src_branch} to produce {args.tgt_branch}"
    )

    deploy_overlays(args.deploy_dir, args.src_branch, args.tgt_branch, args.site_dir)


if __name__ == "__main__":
    main()
