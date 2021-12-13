# This is the Dockerfile for `leanprovercommunity/lean`.
# It is based on the generic `debian` image, and installs `elan` and `leanproject`.
# See also the image `leanprovercommunity/mathlib` which contains a copy of mathlib.

# NOTE: to run this docker image on macos or windows,
# you will need to increase the allowed memory (in the docker GUI) beyond 2GB

# We start with a temporary `builder` container,
# in which we install `python` and prepare a standalone version of `leanproject`.
FROM debian as leanproject-builder

USER root
# install prerequisites
RUN apt-get update && apt-get install curl git python3 python3-pip python3-venv zlib1g-dev -y && apt-get clean
# create a non-root user
RUN useradd -m lean

USER lean
WORKDIR /home/lean

ENV PATH="/home/lean/.local/bin:$PATH"

# install `leanproject` using `pip`
RUN python3 -m pip install --user mathlibtools

# now install `pyinstaller`, and run it on the installed copy of `leanproject`
RUN python3 -m pip install --user pyinstaller
WORKDIR /home/lean/.local/bin
RUN pyinstaller --onefile --noconfirm leanproject
# this has created `/home/lean/.local/bin/dist/leanproject`,
# which we'll now copy to a fresh container

# We now build the final container.
FROM debian
USER root
# install prerequisites
RUN apt-get update && apt-get install curl git -y && apt-get clean
# create a non-root user
RUN useradd -m lean

USER lean
WORKDIR /home/lean

SHELL ["/bin/bash", "-c"]
# set the entrypoint to be a login shell, so everything is on the PATH
ENTRYPOINT ["/bin/bash", "-l"]

# make sure binaries are available even in non-login shells
ENV PATH="/home/lean/.elan/bin:/home/lean/.local/bin:$PATH"

# install elan
RUN curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh -s -- -y && \
    . ~/.profile && \
    elan toolchain install $(curl https://raw.githubusercontent.com/leanprover-community/mathlib/master/leanpkg.toml | grep lean_version | awk -F'"' '{print $2}') && \
    elan toolchain uninstall stable
# install leanproject
COPY --from=leanproject-builder /home/lean/.local/bin/dist/leanproject /home/lean/.local/bin/
