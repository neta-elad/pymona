VENV_DIR ?= .venv/
VENV_BIN ?= $(VENV_DIR)bin/

.PHONY: all
all: format type test

.PHONY: test
test: $(VENV_DIR).installed-dev
	$(VENV_BIN)pytest tests

.PHONY: type
type: $(VENV_DIR).installed-dev
	$(VENV_BIN)mypy src tests

.PHONY: format
format: $(VENV_DIR).installed-dev
	$(VENV_BIN)black src tests

.PHONY: install
install: $(VENV_DIR).installed-dev

$(VENV_DIR).installed-dev: pyproject.toml src vendor $(VENV_DIR)
	$(VENV_BIN)pip install ".[dev]"
	touch $(VENV_DIR).installed-dev

$(VENV_DIR):
	python3.12 -m venv $(VENV_DIR)

.PHONY: clean
clean:
	rm -rf $(VENV_DIR)
