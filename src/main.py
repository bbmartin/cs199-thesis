import sys

from .parser import get_parser
from .transformer import PythonToCOQ
from .utils import read_file, validate_file


def translate_file(input_filepath, output_filepath):
    validate_file(input_filepath)
    
    parse_tree = get_parser().parse(read_file(input_filepath) + "\n")
    
    theorems, translations = PythonToCOQ().transform(parse_tree)
    
    with open(output_filepath, "w") as output_file:
        for block in translations:
            output_file.write(block)
        output_file.write("\n(* Theorems *)")
        for theorem in theorems:
            output_file.write(str(theorem))

    print(f"Translation completed: {input_filepath} → {output_filepath}")

def main():
    if len(sys.argv) < 3:
        print("Usage: python -m src.main input_file.py output_file.txt")
        return 1
    
    input_filepath = sys.argv[1]
    output_filepath = sys.argv[2]
    
    try:
        translate_file(input_filepath, output_filepath)
        return 0
    except Exception as e:
        print(f"Error: {e}")
        return 1

if __name__ == "__main__":
    sys.exit(main())