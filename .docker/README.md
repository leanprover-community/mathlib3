# Docker containers

The `.docker` directory contains instructions for building Docker containers
with Lean and mathlib.

## Build

You can build these containers using `scripts/docker_build.sh`.
This will result in the creation of two containers:

* `leanprovercommunity/lean` - contains elan, lean, and leanproject
* `leanprovercommunity/mathlib` - additionally contains a copy of mathlib, with oleans

In fact, for each container you'll get two different tags, `:debian` and `:latest`,
which are just synonyms.
(We used to have an `alpine` distribution, but it wasn't robust enough to warrant maintenance.)
There is also a `leanprovercommunity/mathlib:gitpod` for use at
[https://gitpod.io/](https://gitpod.io/).

## Usage

### gitpod.io

There is a container based on `gitpod/workspace-base`
enabling [https://gitpod.io/](https://gitpod.io/) to create in-browser VSCode sessions
with elan/lean/leanproject/mathlib already set up.

Either prepend `https://gitpod.io/#` to basically any URL at github, e.g.
[https://gitpod.io/#https://github.com/leanprover-community/mathlib/tree/docker](https://gitpod.io/#https://github.com/leanprover-community/mathlib/tree/docker),
or install a [gitpod browser extension](https://www.gitpod.io/docs/browser-extension/)
which will add buttons directly on github.

You can enable gitpod for repositories importing mathlib as a dependency simply by creating
the file `/.gitpod.yml` containing:

```yml
image: leanprovercommunity/mathlib:gitpod

vscode:
  extensions:
    - jroesch.lean

tasks:
  - command: . /home/gitpod/.profile && leanproject get-mathlib-cache
```

### Command line

You can use these containers as virtual machines:

```sh
docker run -it leanprovercommunity/mathlib
```

### Docker registry

These containers are deployed to the Docker registry, so anyone can just
`docker run -it leanprovercommunity/mathlib` to get a local lean+mathlib environment.

There is a local script in `scripts/docker_push.sh` for deployment,
but I have also set up `hub.docker.com` to watch the `docker` branch for updates
and automatically rebuild.

If this PR is merged to master we should change that to watch `master`.

### Remote containers for VSCode

See `/.devcontainer/README.md`.
