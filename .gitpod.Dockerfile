FROM gitpod/workspace-full

USER root

RUN apt-get update && apt-get install curl git python3 python3-pip python3-venv -y

USER gitpod
WORKDIR /home/gitpod

SHELL ["/bin/bash", "-c"]

RUN curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh -s -- -y
RUN python3 -m pip install --user pipx && python3 -m pipx ensurepath && . ~/.profile && pipx install mathlibtools

ENV PATH="/home/gitpod/.elan/bin:${PATH}"
