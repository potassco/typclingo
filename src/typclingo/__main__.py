"""
The main entry point for the application.
"""

from .app import TypeClingo

__all__ = ["main"]


def main() -> None:
    """
    Run the TypeClingo application.
    """
    TypeClingo().run()


if __name__ == "__main__":
    main()
