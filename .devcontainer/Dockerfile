FROM mcr.microsoft.com/devcontainers/base:ubuntu-24.04@sha256:d94c97dd9cacf183d0a6fd12a8e87b526e9e928307674ae9c94139139c0c6eae

ARG ELAN_VERSION=4.2.4
ARG ELAN_SHA256_AMD64=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
ARG ELAN_SHA256_ARM64=05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
       build-essential \
       curl \
       latexmk \
       lmodern \
       poppler-utils \
       python3-pip \
       python3-venv \
       texlive-fonts-recommended \
       texlive-latex-extra \
       texlive-pictures \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

USER vscode
RUN set -eu; \
    architecture="$(dpkg --print-architecture)"; \
    case "$architecture" in \
      amd64) elan_target="x86_64-unknown-linux-gnu"; elan_sha256="$ELAN_SHA256_AMD64" ;; \
      arm64) elan_target="aarch64-unknown-linux-gnu"; elan_sha256="$ELAN_SHA256_ARM64" ;; \
      *) echo "Unsupported architecture: $architecture" >&2; exit 1 ;; \
    esac; \
    archive="/tmp/elan-${ELAN_VERSION}.tar.gz"; \
    curl -fsSL \
      "https://github.com/leanprover/elan/releases/download/v${ELAN_VERSION}/elan-${elan_target}.tar.gz" \
      -o "$archive"; \
    echo "$elan_sha256  $archive" | sha256sum -c -; \
    mkdir -p /tmp/elan-install; \
    tar -xzf "$archive" -C /tmp/elan-install; \
    /tmp/elan-install/elan-init -y --default-toolchain none; \
    rm -rf "$archive" /tmp/elan-install
