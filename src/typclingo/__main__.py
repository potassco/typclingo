"""
The main entry point for the application.
"""

import sys

from clingo.app import clingo_main
from clingo.core import Library
from clingo.script import enable_python

from .app import TypClingoApp

__all__ = ["typclingo_main"]


def typclingo_main() -> None:
    """
    Run the typclingo application.
    """
    lib = Library()
    enable_python(lib)
    clingo_main(lib, sys.argv[1:], TypClingoApp(lib))


if __name__ == "__main__":
    typclingo_main()
