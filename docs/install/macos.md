How to install Lean and mathlib on MacOS
===

This document explains how to get started with Lean and mathlib.

If you get stuck, please come to [the chat room](https://leanprover.zulipchat.com/) to ask for
assistance.

If you prefer, you can watch a [short video tutorial](https://www.youtube.com/watch?v=k8U6YOK7c0M)

We'll need to set up Lean, an editor that knows about Lean, and `mathlib` (the standard library).

Rather than installing Lean directly, we'll install a small program called `elan` which
automatically provides the correct version of Lean on a per-project basis. This is recommended for
all users.

Installing `elan`
---

1. We'll need a terminal, along with some basic prerequisites.
  Install [homebrew](https://brew.sh/), then run `brew install gmp coreutils` in a terminal
    (`gmp` is required by `lean`, `coreutils` by `leanpkg`).

2. At a terminal, run the command

   `curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh`

   and hit enter when a question is asked.

   It is recommended that you re-login, so that your environment knows about `elan`.
   (Alternatively, type `source $HOME/.elan/env` to update the current terminal.)


Installing mathlib supporting tools
---

At a terminal, run the command
  ```bash
  curl https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/remote-install-update-mathlib.sh -sSf | bash
  ```
If the script asks you whether you want to install `python3` and `pip3`, type `y`.

This will install tools that, amongst other things, let you download compiled binaries for mathlib.

Then run `source ~/.profile`, so that your environment knows about `update-mathlib`.

Installing and configuring an editor
---

There are two editors you can use with Lean, VS Code and emacs.
This document describes using VS Code (for emacs, look at https://github.com/leanprover/lean-mode).

1. Install [VS Code](https://code.visualstudio.com/).
2. Launch VS Code.
3. Click on the extension icon ![(image of icon)](new-extensions-icon.png)
   (or ![(image of icon)](extensions-icon.png) in older versions) in the side bar on the left edge of
   the screen (or press <kbd>⇧ Shift</kbd><kbd>⌘ Command</kbd><kbd>X</kbd>) and search for `leanprover`.
4. Click "install" (In old versions of VSCode, you might need to click "reload" afterwards)
5. Verify Lean is working, for example by saving a file `test.lean` and entering `#eval 1+1`.
   A green line should appear underneath `#eval 1+1`, and hovering the mouse over it you should see `2`
   displayed.

You can now read instructions about creating and working on [Lean projects](project.md)
