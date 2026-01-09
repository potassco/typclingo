"""
Utlities for logging.
"""

from typing import Any, Callable


class LazyStr:
    """
    Wrapper for lazy string evaluation.
    """

    def __init__(self, func: Callable[[], Any]) -> None:
        self.func = func

    def __str__(self) -> str:
        return str(self.func())
