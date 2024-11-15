import os
import sys
import re
from bs4 import BeautifulSoup

section_number_pattern = re.compile(r"^\s*(\d+\.)+\s*")

def process_html_file(filepath, output_filepath):
    """Reads an HTML file, removes 'QA' from headers, and writes the result to the output path."""
    with open(filepath, 'r', encoding='utf-8') as file:
        soup = BeautifulSoup(file, 'html.parser')

    # Simplify all header tags
    for header_tag in soup.find_all(['h1', 'h2', 'h3', 'h4', 'h5', 'h6']):
        if header_tag.contents:
            start = header_tag.contents[0]
            if start.string:
                no_num = section_number_pattern.sub("", start.string)
                header_tag.contents[0].replace_with(no_num)
        for other in header_tag.find_all(['span'], class_="permalink-widget"):
            other.decompose()
        header_tag.replace_with(header_tag.get_text())

    # Simplify ordinal idiom
    for code_tag in soup.find_all('code'):
        # Check if the <code> tag is followed directly by 'th'
        if code_tag.next_sibling and code_tag.next_sibling.string and code_tag.next_sibling.string.startswith('th'):
            # Replace <code>XYZ</code>th with '5th'
            code_tag.replace_with("5")
        elif code_tag.attrs and 'class' in code_tag.attrs and 'hl' in code_tag['class'] and 'lean' in code_tag['class']:
            code_tag.decompose()

    # Delete docstring content (for now)
    for element in soup.find_all(class_="namedocs"):
        element.decompose()

    # Delete grammar specifications
    for element in soup.find_all(class_="grammar"):
        element.decompose()

    # Replace citations with their text
    for element in soup.find_all(class_="citation"):
        for inner in element.contents:
            inner.replace_with(inner.get_text())

    # Ensure the output directory exists
    os.makedirs(os.path.dirname(output_filepath), exist_ok=True)

    # Write the modified HTML to the new output location
    with open(output_filepath, 'w', encoding='utf-8') as file:
        file.write(str(soup))

def traverse_directory(source_directory, output_directory):
    """Recursively traverses source directory, processes HTML files, and writes them to output directory."""
    for root, _, files in os.walk(source_directory):
        for filename in files:
            if filename.endswith('.html') or filename.endswith('.htm'):
                filepath = os.path.join(root, filename)
                # Create the equivalent path in the output directory
                relative_path = os.path.relpath(filepath, source_directory)
                output_filepath = os.path.join(output_directory, relative_path)

                print(f"Processing {filepath} -> {output_filepath}")
                process_html_file(filepath, output_filepath)

if __name__ == "__main__":
    # Check for command-line arguments
    if len(sys.argv) != 3:
        print("Usage: python script.py <source_directory> <output_directory>")
        sys.exit(1)

    # Get source and output directories from command-line arguments
    source_directory = sys.argv[1]
    output_directory = sys.argv[2]

    if not os.path.isdir(source_directory):
        print("The provided source path is not a directory or does not exist.")
        sys.exit(1)

    traverse_directory(source_directory, output_directory)
    print("Processing complete.")
