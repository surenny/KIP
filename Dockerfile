# Stage 1: Build blueprint web output (Alpine + TeXLive)
FROM ghcr.io/xu-cheng/texlive-full:20250401 AS builder

RUN apk update && apk add --update make py3-pip git pkgconfig graphviz graphviz-dev gcc musl-dev

WORKDIR /app

COPY tools/ tools/
COPY blueprint/ blueprint/
COPY lakefile.toml lean-toolchain lake-manifest.json ./

RUN git init && git config --global --add safe.directory /app

RUN python3 -m venv /env && . /env/bin/activate \
    && pip install --upgrade pip requests wheel \
    && pip install pygraphviz \
        --config-settings="--global-option=build_ext" \
        --config-settings="--global-option=-L/usr/lib/graphviz/" \
        --config-settings="--global-option=-R/usr/lib/graphviz/" \
    && pip install -e ./tools/plastexdepgraph \
    && pip install -e ./tools/leanblueprint

RUN . /env/bin/activate && cd blueprint && leanblueprint web

# Stage 2: Lightweight runtime (Debian)
FROM python:3.12-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
    git graphviz libgraphviz-dev gcc pkg-config libc6-dev \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

COPY tools/ tools/
COPY lakefile.toml lean-toolchain lake-manifest.json ./
COPY --from=builder /app/blueprint blueprint/

RUN pip install --no-cache-dir pygraphviz \
    && pip install --no-cache-dir -e ./tools/plastexdepgraph \
    && pip install --no-cache-dir -e ./tools/leanblueprint

RUN git init && git config --global --add safe.directory /app

EXPOSE 8000

CMD ["leanblueprint", "serve"]
