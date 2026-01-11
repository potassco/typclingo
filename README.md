# typclingo

This is a prototype implementation of a type checker for logic programs. It
supports type annotations for predicates and functions, and checks whether the
program is well-typed in the sense that the meets of the types involved in
rules are non-empty (Bot).

See the examples folder for some example programs with type annotations.

## Installation

To install the project without checking out the repository, run

```bash
python -m venv potassco
source potassco/bin/activate
pip install --extra-index-url=https://test.pypi.org/simple git+https://github.com/potassco/typclingo.git
```

## Usage

To enable type checking, pass option `--type-check` to `typclingo`:

```bash
typclingo --type-check <options> <files>
```

Instructions to install and use `nox` can be found in
[DEVELOPMENT.md](./DEVELOPMENT.md)

## Examples

```bash
typclingo --type-check examples/queens.lp
typclingo --type-check examples/meta.lp
typclingo --type-check examples/toh.lp
typclingo --type-check examples/sort.lp
typclingo --type-check  --log-level-types=debug test.lp
```

Note that the sort example does not run yet.
