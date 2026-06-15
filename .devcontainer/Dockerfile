FROM mcr.microsoft.com/devcontainers/base:bookworm

# Install minimal required packages
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    ca-certificates \
    git \
    build-essential \
    sudo \
    python3 \
    && rm -rf /var/lib/apt/lists/* \
    && apt-get clean

# Set environment variables for elan
ENV ELAN_HOME=/usr/local/elan \
    PATH=/usr/local/elan/bin:$PATH

# Create a shared elan directory accessible to all users
RUN mkdir -p $ELAN_HOME && chmod 777 $ELAN_HOME

# Install elan globally (no default toolchain - resolved per-project via lean-toolchain)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
    | sh -s -- -y --no-modify-path --default-toolchain none \
    && chmod -R a+w $ELAN_HOME \
    && elan --version
