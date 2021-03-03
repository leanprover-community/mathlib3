# This is an alternative Dockerfile for `leanprover/lean`,
# based on `alpine`, and installs `elan` and `leanproject`.
# See also the image `leanprover/mathlib` which contains a copy of mathlib.

# `elan` doesn't include a release for `x86_64-unknown-linux-musl`,
# so we roll our own
FROM clux/muslrust as elan-builder

RUN git clone https://github.com/Kha/elan.git .
RUN cargo build

FROM alpine as elan-install

RUN adduser -D lean
USER lean
WORKDIR /home/lean
COPY --from=elan-builder /volume/target/x86_64-unknown-linux-musl/debug/elan-init .
RUN ./elan-init -y && rm elan-init

# We start with a temporary `builder` container, from https://github.com/six8/pyinstaller-alpine
# in which we install `python` and prepare a standalone version of `leanproject`.
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
# (leanproject assumes bash)
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
