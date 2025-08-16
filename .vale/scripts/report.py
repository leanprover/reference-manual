import sys
import json

def annotate_source(file_path, message, start_line, start_column, end_line=None, end_column=None):
    """Annotates a file with a message, highlighting the specified span."""
    try:
        with open(file_path, 'r') as f:
            lines = f.readlines()
    except FileNotFoundError:
        print(f"Error: File '{file_path}' not found.")
        return

    # Determine if it's a single position or a span
    if end_line is None or end_column is None:
        end_line = start_line
        end_column = start_column

    # Check if the specified line numbers are within the file's range
    if start_line < 1 or end_line > len(lines):
        print("Error: Specified line range is out of bounds.")
        return

    # Display a few lines of context before the highlighted span
    context_lines_before = 2
    context_lines_after = 2
    start_display = max(0, start_line - 1 - context_lines_before)
    end_display = min(len(lines), end_line + context_lines_after)

    print("\nSource annotation:\n")
    for i in range(start_display, end_display):
        line_number = i + 1
        line_content = lines[i].rstrip("\n")

        # Highlight the specified range
        if start_line <= line_number <= end_line:
            if line_number == start_line and line_number == end_line:
                # Single line range
                highlighted = (
                    line_content[:start_column - 1] +
                    "\033[91m" + line_content[start_column - 1:end_column] + "\033[0m" +
                    line_content[end_column:]
                )
            elif line_number == start_line:
                # Start line of multi-line range
                highlighted = (
                    line_content[:start_column - 1] +
                    "\033[91m" + line_content[start_column - 1:] + "\033[0m"
                )
            elif line_number == end_line:
                # End line of multi-line range
                highlighted = (
                    "\033[91m" + line_content[:end_column] + "\033[0m" +
                    line_content[end_column:]
                )
            else:
                # Entire line within the range
                highlighted = "\033[91m" + line_content + "\033[0m"
            print(f"{line_number:4} | {highlighted}")
        else:
            print(f"{line_number:4} | {line_content}")

    # Display the error message below the highlighted span
    print("\n" + " " * (start_column + 6) + "\033[91m^\033[0m")
    print(" " * (start_column + 6) + f"\033[1m{message}\033[0m\n")

# Example usage:
# Single position: annotate_source("example.html", "Syntax error here", 10, 5)
# Span: annotate_source("example.html", "Invalid element here", 10, 5, 12, 8)
if __name__ == "__main__":
    # Example arguments (you could replace these with sys.argv inputs for command-line use)
    decoder = json.JSONDecoder()
    buffer = ""

    input = sys.stdin.read()  # Read in chunks of 1024 bytes
    input = input.lstrip()
    data = json.loads(input)
    # Process only if it's a JSON object (dictionary)
    if isinstance(data, dict):
        for file in data:
            for feedback in data[file]:
                line = feedback['Line']
                (c1, c2) = feedback['Span']
                message = feedback['Message']
                severity = feedback['Severity']
                check = feedback['Check']
                annotate_source(file, f'[{severity}] {check}: {message}', line, c1, line, c2)
    else:
        print(f"Skipping non-object JSON value: {json_obj}", file=sys.stderr)
