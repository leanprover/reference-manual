"""CLI interface for fix_diagnostics."""

import argparse
import re
import sys

from . import get_files, get_diagnostics, get_code_actions, apply_code_actions


def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Fix Lean diagnostics via LSP code actions",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # List all diagnostics and their available actions
  python -m fix_diagnostics --list

  # List diagnostics matching a pattern
  python -m fix_diagnostics --diagnostic-pattern "unused" --list

  # Preview fixes (dry run)
  python -m fix_diagnostics --diagnostic-pattern "unused" --action-pattern "Remove"

  # Apply fixes
  python -m fix_diagnostics --diagnostic-pattern "unused" --action-pattern "Remove" --no-dry-run
        """,
    )

    parser.add_argument(
        "--diagnostic-pattern", help="Regex to filter diagnostic messages"
    )
    parser.add_argument("--action-pattern", help="Regex to filter code action titles")
    parser.add_argument(
        "--severity",
        action="append",
        type=int,
        choices=[1, 2, 3, 4],
        help="Filter by severity (1=error, 2=warning, 3=info, 4=hint, can specify multiple)",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="List diagnostics and actions without applying",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        default=True,
        help="Show diffs without applying (default)",
    )
    parser.add_argument(
        "--no-dry-run",
        action="store_false",
        dest="dry_run",
        help="Actually apply changes",
    )
    parser.add_argument(
        "--build-cmd", default="lake build", help="Build command (default: lake build)"
    )

    args = parser.parse_args()

    try:
        # Get diagnostics
        print("Getting diagnostics from LSP...", file=sys.stderr)
        diagnostics = get_diagnostics()

        # Filter by message pattern
        if args.diagnostic_pattern:
            pattern = re.compile(args.diagnostic_pattern)
            diagnostics = [d for d in diagnostics if pattern.search(d.message)]

        # Filter by severity
        if args.severity:
            diagnostics = [d for d in diagnostics if d.severity in args.severity]

        if not diagnostics:
            print("No diagnostics found")
            return 0

        print(f"Found {len(diagnostics)} diagnostics", file=sys.stderr)

        # Get code actions
        print("Getting code actions from LSP...", file=sys.stderr)
        actions = get_code_actions(diagnostics)

        # Filter by action pattern
        if args.action_pattern:
            pattern = re.compile(args.action_pattern)
            actions = [a for a in actions if pattern.search(a.title)]

        if not actions:
            print("No matching code actions found")
            return 0

        print(f"Found {len(actions)} code actions", file=sys.stderr)

        if args.list:
            # Just list them
            print("\nDiagnostics and available actions:\n")
            current_file = None
            for action in actions:
                diag = action.diagnostic
                if diag.file != current_file:
                    current_file = diag.file
                    print(f"\n{diag.file}:")
                severity_names = {1: "error", 2: "warning", 3: "info", 4: "hint"}
                severity_str = severity_names.get(diag.severity, str(diag.severity))
                print(f"  {diag.line}:{diag.col} [{severity_str}] {diag.message}")
                print(f"    → {action.title}")
        else:
            # Apply actions
            print(
                f"{'Previewing' if args.dry_run else 'Applying'} {len(actions)} code actions...",
                file=sys.stderr,
            )
            results = apply_code_actions(actions, dry_run=args.dry_run)

            success_count = sum(r.success for r in results)
            fail_count = sum(not r.success for r in results)

            if args.dry_run:
                print(f"\nDry run: would apply {success_count} actions")
            else:
                print(f"\nApplied {success_count} actions")

            if fail_count > 0:
                print(f"Failed: {fail_count} actions")

            # Show diffs
            for result in results:
                if result.success and result.diff:
                    print(f"\n{'=' * 60}")
                    print(f"Action: {result.action.title}")
                    print(
                        f"Location: {result.action.diagnostic.file}:{result.action.diagnostic.line}"
                    )
                    print(f"{'=' * 60}")
                    print(result.diff)
                elif not result.success:
                    print(f"\nFailed: {result.action.title}")
                    print(f"Error: {result.error}")

            return 0 if fail_count == 0 else 1

        return 0

    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("\nInterrupted", file=sys.stderr)
        return 130
    except Exception as e:
        print(f"Unexpected error: {e}", file=sys.stderr)
        import traceback

        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
