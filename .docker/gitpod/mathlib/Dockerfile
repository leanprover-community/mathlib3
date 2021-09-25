# This is the Dockerfile for `leanprovercommunity/mathlib:gitpod`.

# gitpod doesn't support multiple FROM statements, (or rather, you can't copy from one to another)
# so we just install everything in one go
FROM gitpod/workspace-base

USER root

RUN apt-get update && apt-get install curl git python3 python3-pip python3-venv -y

USER gitpod
WORKDIR /home/gitpod

SHELL ["/bin/bash", "-c"]

# install elan
RUN curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh -s -- -y
# install whichever toolchain mathlib is currently using
RUN . ~/.profile && elan toolchain install $(curl https://raw.githubusercontent.com/leanprover-community/mathlib/master/leanpkg.toml | grep lean_version | awk -F'"' '{print $2}')
# install `leanproject` using `pip`
# RUN python3 -m pip install --user mathlibtools
RUN python3 -m pip install --user pipx && python3 -m pipx ensurepath && source ~/.profile && pipx install mathlibtools==1.1.0

ENV PATH="/home/gitpod/.local/bin:/home/gitpod/.elan/bin:${PATH}"

# fix the infoview when the container is used on gitpod:
ENV VSCODE_API_VERSION="1.50.0"

# ssh to github once to bypass the unknown fingerprint warning
RUN ssh -o StrictHostKeyChecking=no github.com || true
