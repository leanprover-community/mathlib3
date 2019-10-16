# Installing Lean and mathlib on Linux

This document explains how to get started with Lean and mathlib on a generic Linux distribution (there is a [specific page](debian.md) for Debian and derived distribtions such as Ubuntu).

All commands below should be typed inside a terminal.

* Lean itself doesn't depend on much infrastructure, but supporting tools
  needed by most users require `git`, `curl`, and `python`. So the first step is to get those.

* You will also need a code editor that has a Lean plugin. The
  recommended choice is [Visual Studio Code](https://code.visualstudio.com/).
  The alternative is to use Emacs, and its [lean-mode](https://github.com/leanprover/lean-mode).

  1. Install [VS Code](https://code.visualstudio.com/).
  2. Launch VS Code.
  3. Click on the extension icon ![(image of icon)](new-extensions-icon.png)
     (or ![(image of icon)](extensions-icon.png) in older versions) in the side bar on the left edge of
     the screen (or press <kbd>Shift</kbd><kbd>Ctrl</kbd><kbd>X</kbd>) and search for `leanprover`.
  4. Click "install" (In old versions of VSCode, you might need to click "reload" afterwards)
  5. Verify Lean is working, for example by saving a file `test.lean` and entering `#eval 1+1`.
    A green line should appear underneath `#eval 1+1`, and hovering the mouse over it you should see `2`
    displayed.

* The next step installs a small tool called `elan` which will handle
  updating Lean according to the needs of your current project (hit Enter
  when a question is asked). It will live in `$HOME/.elan` and add a
  line to `$HOME/.profile`.
  ```bash
  curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh
  ```

* Then we install a small tool called `update-mathlib` that which will handle
  updating mathlib according to the needs of your current project.
  It will live in `$HOME/.mathlib` and add a line to `$HOME/.profile`.
  ```bash
  curl https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/remote-install-update-mathlib.sh -sSf | bash
  ```

You can now read instructions about creating and working on [Lean projects](project.md)
