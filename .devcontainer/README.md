# Remote containers for VSCode

Installing the `Remote - Containers` VSCode extension
will allow you to open a project inside the `leanprover/mathlib` container
(meaning you don't even need a local copy of lean installed).

The file `/.devcontainer/devcontainer.json` sets this up:
if you have the extension installed, you'll be prompted to ask if you'd like to run inside the
container, no configuration necessary.

See `/.github/README.md` for a description of the `leanprover/mathlib` container.
