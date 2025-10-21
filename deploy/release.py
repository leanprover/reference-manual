#!/usr/bin/env python3
import os
import sys
import shutil
import tempfile
import argparse
from release_utils import run_git_command, find_latest_version,
  find_latest_stable_version, git_has_changes

def deploy_version(source_dir, version, branch):
    """
    Deploy a version by copying from source directory to versioned directory.

    Args:
        source_dir (str): Source directory to copy content from
        version (str): Version string (will be used as the directory name)
        branch (str): Git branch to checkout
    """
    # Save current git commit to restore later
    current_commit = run_git_command(["git", "rev-parse", "HEAD"])

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

            # Update the "latest" pointer if needed
            latest_link = "latest"
            latest_version = find_latest_version(".")

            if latest_version:
                # If a symlink already exists, remove it
                if os.path.islink(latest_link):
                    os.unlink(latest_link)

                # If it's a directory, delete it
                if os.path.isdir(latest_link):
                    shutil.rmtree(latest_link, ignore_errors=True)

                # Copy the latest version (Netlify deploy doesn't work with symlinks)
                shutil.copytree(latest_version, latest_link)
                print(f"Updated 'latest' alias as a copy of: {latest_version}")

                run_git_command(["git", "add", "latest"])


            # Update the "stable" pointer if needed
            stable_link = "stable"
            latest_stable_version = find_latest_stable_version(".")

            if latest_stable_version:
                # If a symlink already exists, remove it
                if os.path.islink(stable_link):
                    os.unlink(stable_link)

                # If it's a directory, delete it
                if os.path.isdir(stable_link):
                    shutil.rmtree(stable_link, ignore_errors=True)

                # Copy the latest version (Netlify deploy doesn't work with symlinks)
                shutil.copytree(latest_stable_version, stable_link)
                print(f"Updated 'stable' alias as a copy of: {latest_stable_version}")

                run_git_command(["git", "add", "stable"])


            if git_has_changes():
                run_git_command(["git", "commit", "-m", f"Deploy {version}"])
            else:
                print(f"Nothing changed, so no commit will be made.")

    finally:
        # Restore the original branch
        print(f"Restoring original commit: {current_commit}")
        run_git_command(["git", "switch", "--detach", current_commit])

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
