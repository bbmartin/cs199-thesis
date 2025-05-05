from lark import Lark
from lark.indenter import PythonIndenter


def get_parser():
    kwargs = dict(postlex=PythonIndenter(), start='file_input', maybe_placeholders=False)
    return Lark.open("python.lark", rel_to=__file__, parser="lalr", **kwargs)