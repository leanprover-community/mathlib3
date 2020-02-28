# Hole commands

Both VS Code and emacs support integration for 'hole commands'.

In VS Code, if you enter `{! !}`, a small light bulb symbol will appear, and
clicking on it gives a drop down menu of available hole commands. Running one
of these will replace the `{! !}` with whatever text that hole command provides.

In emacs, you can do something similar with `C-c SPC`.

Many of these commands are available whenever `tactic.core` is imported.
Commands that require additional imports are noted below.
All should be available with `import tactic`.
