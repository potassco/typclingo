# typclingo

## Installation

To install the project without checking out the repository, run

```bash
python -m venv potassco
source potassco/bin/activate
pip install --extra-index-url=https://test.pypi.org/simple git+https://github.com/potassco/typclingo.git
```

For ssh you can use

```bash
python -m venv potassco
source potassco/bin/activate
pip install --extra-index-url=https://test.pypi.org/simple git+ssh://git@github.com/potassco/typclingo.git
```

Note that the repository is private at the moment, you have to setup some
password or access token to use it.

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
