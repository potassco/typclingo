"""
Utlities for logging.
"""


class LazyStr:
    """
    Wrapper for lazy string evaluation.
    """

    def __init__(self, func):
        self.func = func

    def __str__(self):
        return str(self.func())
