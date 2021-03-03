# Docker containers

The `.docker` directory contains instructions for building Docker containers
with Lean and mathlib.

## Build

You can build these containers using `scripts/docker_build.sh`.
This will result in the creation of two containers:

* `leanprover/lean` - contains elan, lean, and leanproject
* `leanprover/mathlib` - additionally contains a copy of mathlib, with oleans

In fact, for each container you'll get three different tags, `:debian`, `:alpine` and `:latest`.
`:debian` and `:alpine` use those respective distributions, and `:latest` just points at `:debian`.
Finally, there is also a `leanprover/mathlib:gitpod` for use at `https://gitpod.io/`.

## Usage

### gitpod.io

There is a container based on `gitpod/workspace-base`
enabling `https://gitpod.io/` to create in-browser VSCode sessions
with elan/lean/leanproject/mathlib already set up.

Either prepend `https://gitpod.io/#` to basically any URL at github, e.g.
`https://gitpod.io/#https://github.com/leanprover-community/mathlib/tree/docker`,
or install a [gitpod browser extension](https://www.gitpod.io/docs/browser-extension/)
which will add buttons directly on github.

(If people like gitpod we can add links in the PR template.)

### Command line

You can use these containers as virtual machines:

```sh
docker run -it leanprover/mathlib
```

### Docker registry

These containers are deployed to the Docker registry, so anyone can just
`docker run -it leanprover/mathlib` to get a local lean+mathlib environment.

TODO: automate deployment via `scripts/docker_push.sh`,
or by having `hub.docker.com` watch the repository.

### Remote containers for VSCode

Installing the `Remote - Containers` VSCode extension
will allow you to open a project inside the `leanprover/mathlib` container
(meaning you don't even need a local copy of lean installed).

The file `/.devcontainer/devcontainer.json` sets this up:
if you have the extension installed, you'll be prompted to ask if you'd like to run inside the
container, no configuration necessary.
