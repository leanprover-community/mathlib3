# This is an alternative Dockerfile, for `leanprover/lean:alpine`,
# based on `alpine`, and installs `elan` and `leanproject`.
# See also the image `leanprover/mathlib` which contains a copy of mathlib.

# `elan` doesn't include a release for `x86_64-unknown-linux-musl`,
# so we roll our own
FROM clux/muslrust as elan-builder

RUN git clone https://github.com/Kha/elan.git .
RUN cargo build --release

# To save some space, we make another intermediate container in which we install
# elan and whichever toolchain mathlib currently needs.
# We later COPY out just the ~/.elan directory into our final container.
FROM alpine as elan-install

RUN apk update && apk add --no-cache curl

RUN adduser -D lean
USER lean
WORKDIR /home/lean
COPY --from=elan-builder /volume/target/x86_64-unknown-linux-musl/release/elan-init .
RUN ./elan-init -y && rm elan-init && \
    . ~/.profile && \
    elan toolchain install $(curl https://raw.githubusercontent.com/leanprover-community/mathlib/master/leanpkg.toml | grep lean_version | awk -F'"' '{print $2}') && \
    elan toolchain uninstall stable

# We make another temporary `builder` container, from https://github.com/six8/pyinstaller-alpine
# in which we install `python` and prepare a standalone version of `leanproject`.
# This saves including a huge layer containing a python environment.
FROM six8/pyinstaller-alpine:alpine-3.6-pyinstaller-v3.4 as leanproject-builder

USER root
# install prerequisites
RUN apk update && apk add --no-cache python3 py3-pip py3-virtualenv
# create a non-root user
RUN adduser -D lean

USER lean
WORKDIR /home/lean

ENV PATH="/home/lean/.local/bin:$PATH"

# install `leanproject` using `pip`
RUN python3 -m pip install --user mathlibtools

# run `pyinstaller` on the installed copy of `leanproject`
WORKDIR /home/lean/.local/bin
RUN /pyinstaller/pyinstaller.sh --onefile --noconfirm leanproject
# this has created `/home/lean/.local/bin/dist/leanproject`,
# which we'll now copy to a fresh container

# Now we start the `alpine` build.
FROM alpine

USER root
# install prerequisites
# (leanpkg assumes bash)
RUN apk update && apk add --no-cache bash curl git openssh
# create a non-root user
RUN adduser -D lean

USER lean
WORKDIR /home/lean

SHELL ["/bin/ash", "-c"]
# set the entrypoint to be a login shell, so everything is on the PATH
ENTRYPOINT ["/bin/ash", "-l"]

# install elan
COPY --from=elan-install /home/lean/.elan /home/lean/.elan

COPY .profile .

# install leanproject
COPY --from=leanproject-builder /home/lean/.local/bin/dist/leanproject /home/lean/.local/bin/

# make sure binaries are available even in non-login shells
ENV PATH="/home/lean/.elan/bin:/home/lean/.local/bin:$PATH"
