FROM python:3.12
WORKDIR /usr/src/pymona
ADD src src
ADD tests tests
ADD vendor vendor
ADD CMakeLists.txt .
ADD pyproject.toml .
ADD Makefile .
ADD README.md .
ENV VENV_BIN=
ENV VENV_DIR=.
RUN make test