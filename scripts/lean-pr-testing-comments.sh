## Create comments and labels on a Lean 4 PR after CI has finished on a `*-pr-testing-NNNN` branch.
## This is based on the identically-named script in the Mathlib repository.

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

# Ensure the first argument is 'lean'
if [ $# -eq 0 ]; then
    echo "No arguments provided"
    exit 1
fi

# Set NIGHTLY_TESTING_REPO for comparison URLs (where the branches and tags actually live)
if [ -z "${NIGHTLY_TESTING_REPO:-}" ]; then
  NIGHTLY_TESTING_REPO="leanprover/reference-manual"
fi

# TODO: The whole script ought to be rewritten in javascript, to avoid having to use curl for API calls.
#
# This is not meant to be run from the command line, only from CI.
# The inputs must be prepared as:
# env:
#   TOKEN: ${{ secrets.LEAN_PR_TESTING }}
#   GITHUB_CONTEXT: ${{ toJson(github) }}
#   WORKFLOW_URL: https://github.com/${{ github.repository }}/actions/runs/${{ github.event.workflow_run.id }}
#   BUILD_OUTCOME: ${{ steps.build.outcome }}
#   GENERATE_OUTCOME: ${{ steps.test.outcome }}

# Adjust the branch pattern and URLs based on the repository.
if [ "$1" == "lean" ]; then
  branch_prefix="lean-pr-testing"
  repo_url="https://api.github.com/repos/leanprover/lean4"
  base_branch="nightly-testing" # This really should be the relevant `nightly-testing-YYYY-MM-DD` tag.
else
  echo "Unknown repository: $1. Must be 'lean'."
  exit 1
fi

# Extract branch name and check if it matches the pattern.
branch_name=$(echo "$GITHUB_CONTEXT" | jq -r .ref | cut -d'/' -f3)
if [[ "$branch_name" =~ ^$branch_prefix-([0-9]+)$ ]]; then
  pr_number="${BASH_REMATCH[1]}"
  current_time=$(date "+%Y-%m-%d %H:%M:%S")

  echo "This is a '$branch_prefix-$pr_number' branch, so we need to adjust labels and write a comment."

  # Check if the PR has an awaiting-manual label
  has_awaiting_label=$(curl -L -s \
    -H "Accept: application/vnd.github+json" \
    -H "Authorization: Bearer $TOKEN" \
    -H "X-GitHub-Api-Version: 2022-11-28" \
    $repo_url/issues/$pr_number/labels | jq 'map(.name) | contains(["awaiting-manual"])')

  # Perform actions based on outcomes
  if [ "$GENERATE_OUTCOME" == "success" ]; then
    echo "Removing label awaiting-manual"
    curl -L -s \
      -X DELETE \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      $repo_url/issues/$pr_number/labels/awaiting-manual
    echo "Removing label breaks-manual"
    curl -L -s \
      -X DELETE \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      $repo_url/issues/$pr_number/labels/breaks-manual
    echo "Adding label builds-manual"
    curl -L -s \
      -X POST \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      $repo_url/issues/$pr_number/labels \
      -d '{"labels":["builds-manual"]}'
  elif [ "$GENERATE_OUTCOME" == "failure" ] || [ "$BUILD_OUTCOME" == "failure" ]; then
    echo "Removing label builds-manual"
    curl -L -s \
      -X DELETE \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      $repo_url/issues/$pr_number/labels/builds-manual
    echo "Adding label breaks-manual"
    curl -L -s \
      -X POST \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      $repo_url/issues/$pr_number/labels \
      -d '{"labels":["breaks-manual"]}'
  fi

  branch="[$branch_prefix-$pr_number](https://github.com/$NIGHTLY_TESTING_REPO/compare/$base_branch...$branch_prefix-$pr_number)"
  # Depending on the success/failure, set the appropriate message
  if [ "GENERATE_OUTCOME" == "cancelled" ] || [ "$BUILD_OUTCOME" == "cancelled" ]; then
    message="- 🟡 Reference manual branch $branch build against this PR was cancelled. ($current_time) [View Log]($WORKFLOW_URL)"
  elif [ "$GENERATE_OUTCOME" == "success" ]; then
    message="- ✅ Reference manual branch $branch has successfully built against this PR. ($current_time) [View Log]($WORKFLOW_URL)"
  elif [ "$BUILD_OUTCOME" == "failure" ]; then
    message="- 💥 Reference manual branch $branch build failed against this PR. ($current_time) [View Log]($WORKFLOW_URL)"
  elif [ "$GENERATE_OUTCOME" == "failure" ]; then
    message="- ❌ Reference manual branch $branch built against this PR, but generating HTML failed. ($current_time) [View Log]($WORKFLOW_URL)"
  else
    message="- 🟡 Reference manual branch $branch build against this PR didn't complete normally. ($current_time) [View Log]($WORKFLOW_URL)"
  fi

  echo "$message"

  # Check if we should post a new comment or append to the existing one
  if [ "$has_awaiting_label" == "true" ]; then
    # Always post as a new comment if awaiting-manual label is present
    intro="Manual CI status:"
    echo "Posting as a separate comment due to awaiting-manual label at $repo_url/issues/$pr_number/comments"
    curl -L -s \
      -X POST \
      -H "Authorization: token $TOKEN" \
      -H "Accept: application/vnd.github.v3+json" \
      -d "$(jq --null-input --arg val "$message" '{"body": $val}')" \
      "$repo_url/issues/$pr_number/comments"
  else
    # Use existing behavior: append to existing comment or post a new one
    # Use GitHub API to check if a comment already exists
    existing_comment=$(curl -L -s -H "Authorization: token $TOKEN" \
                            -H "Accept: application/vnd.github.v3+json" \
                            "$repo_url/issues/$pr_number/comments" \
                            | jq 'first(.[] | select(.body | test("^- . Manual") or startswith("Reference manual")) | select(.user.login == "leanprover-bot"))')
    existing_comment_id=$(echo "$existing_comment" | jq -r .id)
    existing_comment_body=$(echo "$existing_comment" | jq -r .body)

    # Append new result to the existing comment or post a new comment
    if [ -z "$existing_comment_id" ]; then
      # Post new comment with a bullet point
      intro="Reference manual CI status:"
      echo "Posting as new comment at $repo_url/issues/$pr_number/comments"
      curl -L -s \
        -X POST \
        -H "Authorization: token $TOKEN" \
        -H "Accept: application/vnd.github.v3+json" \
        -d "$(jq --null-input --arg intro "$intro" --arg val "$message" '{"body": ($intro + "\n" + $val)}')" \
        "$repo_url/issues/$pr_number/comments"
    else
      # Append new result to the existing comment
      echo "Appending to existing comment at $repo_url/issues/$pr_number/comments"
      curl -L -s \
        -X PATCH \
        -H "Authorization: token $TOKEN" \
        -H "Accept: application/vnd.github.v3+json" \
        -d "$(jq --null-input --arg existing "$existing_comment_body" --arg message "$message" '{"body":($existing + "\n" + $message)}')" \
        "$repo_url/issues/comments/$existing_comment_id"
    fi
  fi
else
    echo "Not reporting status because branch name '$branch_name' doesn't match ^$branch_prefix-([0-9]+)$"
fi
