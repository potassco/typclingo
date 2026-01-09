"""
The main entry point for the application.
"""

import sys

from clingo.app import clingo_main
from clingo.core import Library

from .app import TypClingoApp

__all__ = ["main"]


def main() -> None:
    """
    Run the TypeClingo application.
    """
    lib = Library()
    clingo_main(lib, sys.argv[1:], TypClingoApp(lib))


if __name__ == "__main__":
    main()
