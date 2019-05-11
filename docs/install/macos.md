# How to install Lean and mathlib on MacOS

This document explains how to get started with Lean and mathlib.

If you get stuck, please come to [the chat room](https://leanprover.zulipchat.com/) to ask for
assistance.

If you prefer, you can watch a [short video tutorial](https://www.youtube.com/watch?v=k8U6YOK7c0M)

We'll need to set up Lean, an editor that knows about Lean, and `mathlib` (the standard library).

Rather than installing Lean directly, we'll install a small program called `elan` which
automatically provides the correct version of Lean on a per-project basis. This is recommended for
all users.

### Installing `elan`

1. We'll need a terminal, along with some basic prerequisites.
  Install [homebrew](https://brew.sh/), then run `brew install gmp coreutils` in a terminal
    (`gmp` is required by `lean`, `coreutils` by `leanpkg`).

2. At a terminal, run the command

   `curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh`

   and hit enter when a question is asked.
   
   It is recommended that you re-login, so that your environment knows about `elan`.
   (Alternatively, type `source $HOME/.elan/env` to update the current terminal.)

### Installing mathlib supporting tools

In order to use mathlib supporting tools, you need to [get python](https://www.python.org/downloads/) first.
Then, at a terminal, run the command
  ```bash
  curl https://raw.githubusercontent.com/leanprover-community/mathlib/master/scripts/remote-install-update-mathlib.sh -sSf | bash
  ```

### Installing and configuring an editor

There are two Lean-aware editors, VS Code and emacs.
This document describes using VS Code (for emacs, look at https://github.com/leanprover/lean-mode).

1. Install [VS Code](https://code.visualstudio.com/).
2. Launch VS Code.
3. Click on the extension icon in the view bar at the left
   and search for `leanprover`.
4. Click "install", and then "reload" to restart VS Code.
5. Verify Lean is working, for example by saving a file `test.lean` and entering `#eval 1+1`.
   A green line should appear under this, and hovering the mouse over it you should see `2`
   displayed.

You can now read instructions about creating and working on [Lean projects](project.md)
