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

Currently, typclingo has no options and just reads from stdin:

```bash
cat [files] | typclingo
```

Instructions to install and use `nox` can be found in
[DEVELOPMENT.md](./DEVELOPMENT.md)

## Examples

```bash
cat examples/test.lp | typclingo
cat examples/queens.lp | typclingo
cat examples/.lp | typclingo
```
