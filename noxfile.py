import os

import nox

nox.options.sessions = "lint_pylint", "typecheck", "test"

PYTHON_VERSIONS = None
if "GITHUB_ACTIONS" in os.environ:
    PYTHON_VERSIONS = ["3.12", "3.14"]


@nox.session
def dev(session):
    """
    Create a development environment in editable mode.

    Activate it by running `source .nox/dev/bin/activate`.
    """
    session.install("--extra-index-url", "https://test.pypi.org/simple/", "-e", ".[dev]")


@nox.session
def lint_pylint(session):
    """
    Run pylint.
    """
    session.install("--extra-index-url", "https://test.pypi.org/simple/", ".[lint_pylint]")
    session.run("pylint", "typclingo", "tests", "--fail-under=0")


@nox.session
def typecheck(session):
    """
    Typecheck the code using mypy.
    """
    session.install("--extra-index-url", "https://test.pypi.org/simple/", ".[typecheck]")
    session.run("mypy", "--strict", "-p", "typclingo", "-p", "tests")


@nox.session(python=PYTHON_VERSIONS)
def test(session):
    """
    Run the tests.

    Accepts an additional arguments which are passed to the unittest module.
    This can for example be used to selectively run test cases.
    """

    args = [".[test]"]
    args.insert(0, "https://test.pypi.org/simple/")
    args.insert(0, "--extra-index-url")
    session.install(*args)
    if session.posargs:
        session.run("coverage", "run", "-m", "unittest", session.posargs[0], "-v")
    else:
        session.run("coverage", "run", "-m", "unittest", "discover", "-v")
        session.run("coverage", "report", "-m", "--fail-under=0")
