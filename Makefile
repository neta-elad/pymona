VENV_DIR ?= .venv/
VENV_BIN ?= $(VENV_DIR)bin/

all: format type test

test: $(VENV_DIR).installed-dev
	$(VENV_BIN)pytest tests

type: $(VENV_DIR).installed-dev
	$(VENV_BIN)mypy src tests

format: $(VENV_DIR).installed-dev
	$(VENV_BIN)black src tests

install: $(VENV_DIR).installed-dev

$(VENV_DIR).installed-dev: pyproject.toml src vendor $(VENV_DIR)
	$(VENV_BIN)pip install ".[dev]"
	touch $(VENV_DIR).installed-dev

$(VENV_DIR):
	python3.12 -m venv $(VENV_DIR)
