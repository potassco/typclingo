"""
Main application module for TypeClingo.
"""

import logging
from typing import Sequence

from clingo import ast
from clingo.app import App, AppOptions, Flag
from clingo.control import Control
from clingo.core import Library

from .checker.clingo import ParamHolder, check_stm
from .parser import Parser
from .spec import TypeSpec

__all__ = ["TypClingoApp"]
logger = logging.getLogger(__name__)


class ColoredFormatter(logging.Formatter):
    """
    Formatter that adds colors to log messages based on their severity level.
    """

    COLORS = {
        logging.DEBUG: "\033[36m",
        logging.INFO: "\033[32m",
        logging.WARNING: "\033[33m",
        logging.ERROR: "\033[31m",
    }
    RESET = "\033[0m"

    def __init__(self, use_colors=True):
        super().__init__(fmt="%(levelname)s: %(message)s")
        self.use_colors = use_colors

    def format(self, record):
        if not self.use_colors or not record.__dict__.get("_isatty", True):
            return f"{record.levelname}: {record.getMessage()}"

        color = self.COLORS.get(record.levelno, "")
        msg = f"{record.levelname}: {record.getMessage()}"
        return f"{color}{msg}{self.RESET}"


class TypClingoApp(App):
    """
    The main application class for TypeClingo.
    """

    lib: Library

    def __init__(self, lib: Library) -> None:
        super().__init__("typclingo", "1.0.0")
        self.lib = lib
        self.log_level = logging.INFO
        self.enable_type_check = Flag()

    def parse_vebosity(self, value: str):
        """
        Parse and set the verbosity level for type checking logs.
        """
        match value.lower():
            case "info":
                self.log_level = logging.INFO
            case "debug":
                self.log_level = logging.DEBUG
            case "warning" | "warn":
                self.log_level = logging.WARNING
            case "error":
                self.log_level = logging.ERROR
            case _:
                raise ValueError(f"Unknown verbosity level: {value}")

    def register_options(self, options: AppOptions) -> None:
        """
        Register typclingo-specific options.
        """
        group = "TypeClingo Options"
        options.add_flag(group, "type-check", "Enable type checking", self.enable_type_check)
        options.add(
            group,
            "log-level-types",
            "Log level for type checking {error|warn|info|debug}",
            self.parse_vebosity,
        )

    def main(self, control: Control, files: Sequence[str]) -> None:
        """
        Run the main application logic.
        """

        if self.enable_type_check.value:
            handler = logging.StreamHandler()
            handler.setFormatter(ColoredFormatter(handler.stream.isatty()))
            logging.basicConfig(level=self.log_level, handlers=[handler])

            prg = ast.Program(self.lib)
            spec = TypeSpec()
            stms: list[ast.Statement] = []
            consts: list[ast.StatementConst] = []

            def cb(stm: ast.Statement) -> None:
                """
                Callback for processing statements.
                """
                if isinstance(stm, ast.StatementConst):
                    consts.append(stm)
                elif isinstance(stm, ast.StatementComment):
                    if stm.comment_type == ast.CommentType.Block and stm.value.startswith("%*?"):
                        Parser(stm.value).parse(spec)
                else:
                    stms.append(stm)
                prg.add(stm)

            ast.parse_files(self.lib, files, cb)
            spec.check()

            logger.debug("Type Specification")
            if logger.isEnabledFor(logging.DEBUG):
                for line in str(spec).splitlines():
                    logger.debug("  %s", line)

            params = ParamHolder(spec, consts)
            for rule in stms:
                check_stm(spec, params, rule)

            control.join(prg)
        else:
            control.parse_files(files)
        control.main()
