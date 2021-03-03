# This is the Dockerfile for `leanprover/mathlib:gitpod`.
FROM leanprover/lean:debian

USER root

RUN useradd -m gitpod

RUN rm -rf /home/gitpod && mv /home/lean /home/gitpod && chown -R gitpod:gitpod /home/gitpod

USER gitpod
WORKDIR /home/gitpod

SHELL ["/bin/bash", "-c"]
# set the entrypoint to be a login shell, so everything is on the PATH
ENTRYPOINT ["/bin/bash", "-l"]

ENV PATH="/home/gitpod/.local/bin:/home/gitpod/.elan/bin:${PATH}"

# fix the infoview when the container is used on gitpod:
ENV VSCODE_API_VERSION="1.50.0"

# ssh to github once to bypass the unknown fingerprint warning
RUN ssh -o StrictHostKeyChecking=no github.com || true
