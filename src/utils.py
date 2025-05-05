import os
import sys


def read_file(filepath, *args):
    kwargs = {'encoding': 'iso-8859-1'}
    with open(filepath, *args, **kwargs) as f:
        return f.read()

def exit_with_error(message):
    sys.exit(f"Error: {message}")

def validate_file(filepath, check_exists=True):
    if check_exists and not os.path.isfile(filepath):
        exit_with_error(f"'{filepath}' not found.")