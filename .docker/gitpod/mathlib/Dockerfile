# This is the Dockerfile for `leanprover/mathlib:gitpod`.

# gitpod doesn't support multiple FROM statements, (or rather, you can't copy from one to another)
# so we just install everything in one go
FROM gitpod/workspace-base

USER root

RUN apt-get update && apt-get install curl git python3 python3-pip python3-venv -y

USER gitpod
WORKDIR /home/gitpod

SHELL ["/bin/bash", "-c"]

RUN curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh -s -- -y
# install `leanproject` using `pip`
# RUN python3 -m pip install --user mathlibtools
RUN python3 -m pip install --user pipx && python3 -m pipx ensurepath && source ~/.profile && pipx install mathlibtools

ENV PATH="/home/gitpod/.local/bin:/home/gitpod/.elan/bin:${PATH}"

# fix the infoview when the container is used on gitpod:
ENV VSCODE_API_VERSION="1.50.0"

# suppress an error message in the terminal:
RUN mkdir /home/gitpod/.bashrc.d/

# ssh to github once to bypass the unknown fingerprint warning
RUN ssh -o StrictHostKeyChecking=no github.com || true
# clone a copy of mathlib, and download precompiled oleans
RUN leanproject get mathlib
