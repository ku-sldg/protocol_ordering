# want parser to start after models header

from bs4 import BeautifulSoup
import xml.etree.ElementTree as ET

def parse_xhtml_to_coq(xhtml_file_path, coq_file_path):
    with open(xhtml_file_path, 'r', encoding='utf-8') as xhtml_file:
        xhtml_content = xhtml_file.read()

    soup = BeautifulSoup(xhtml_content, 'html.parser')

    # Process the SVG elements (optional)
    svg_content = generate_svg_content(soup)

    # Combine text and SVG content into Coq code
    coq_code = "\n" + svg_content

    # Write the Coq code to a file
    with open(coq_file_path, 'w', encoding='utf-8') as coq_file:
        coq_file.write("Module sys1. \n")
        coq_file.write(coq_code)

def generate_svg_content(soup):
    # Extracting information from SVG elements
    svg_elements = soup.find_all('svg')
    coq_code = ""

    for svg_element in svg_elements:
        # Parsing SVG using xml.etree.ElementTree
        svg_tree = ET.fromstring(str(svg_element))
        
        # Extracting specific text content within the SVG
        target_text = extract_target_text(svg_tree)

        # Append the extracted text to the Coq code
        coq_code += f'(* Extracted Text from SVG: {target_text} *)\n'


    return coq_code

def extract_target_text(svg_tree):
    # Find the relevant text element within the SVG
    target_text_elements = svg_tree.findall('.//{http://www.w3.org/2000/svg}text')

    # Extract the text content from the found element
    target_texts = [text_element.text.strip() for text_element in target_text_elements]

    return target_texts

# Example usage
xhtml_file_path = '../chase_analysis/sys1/sys1_chase.xhtml'
coq_file_path = 'output.v'

parse_xhtml_to_coq(xhtml_file_path, coq_file_path)