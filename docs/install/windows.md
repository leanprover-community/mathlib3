# Installing Lean and mathlib on Windows

This document explains how to get started with Lean and mathlib.

If you get stuck, please come to [the chat room](https://leanprover.zulipchat.com/) to ask for
assistance.
If you prefer, you can watch a [short video tutorial](https://www.youtube.com/watch?v=2f_9Zetekd8)

We'll need to set up Lean, an editor that knows about Lean, and `mathlib` (the standard library).
Rather than installing Lean directly, we'll install a small program called `elan` which
automatically provides the correct version of Lean on a per-project basis. This is recommended for
all users.

### Installing `elan`

1. We'll need a terminal, along with some basic prerequisites.
   * Either (recommended): install [Git for Windows](https://gitforwindows.org/), after which you
     can open a terminal by typing "git bash" in the Windows search bar (you can accept all default answers during installation).
   * Or: install [Msys2](https://www.msys2.org/), after which you can open a terminal by
     typing "msys2" in the Windows search bar. You'll also need to run `pacman -S unzip git` in
     an msys2 terminal.

2. At a terminal, run the command

   `curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh`

   and hit enter when a question is asked. Then we need to make sure the terminal will find the installed files:
   * With Git for Windows you'll need to run `echo 'PATH="$HOME/.elan/bin:$PATH"' >> $HOME/.profile` in the terminal.
   * With MSYS2 you'll need to run `echo 'PATH="/c/Users/$USERNAME/.elan/bin:$PATH"' >> $HOME/.bashrc`.

   It is recommended that you re-login,
   so that your environment knows about `elan`.
   (Alternatively, type `source $HOME/.elan/env` to update the current terminal.)

### Installing mathlib supporting tools

In order to use mathlib supporting tools, you need to [get python](https://www.python.org/downloads/) first.
Then, at a terminal, run the command
  ```bash
  curl https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/remote-install-update-mathlib.sh -sSf | bash
  ```

### Installing and configuring an editor

There are two Lean-aware editors, VS Code and emacs.
This document describes using VS Code (for emacs, look at https://github.com/leanprover/lean-mode).

1. Install [VS Code](https://code.visualstudio.com/).
2. Launch VS Code.
3. Click on the extension icon ![(image of icon)](extensions-icon.png) in the side bar on the left
  edge of the screen and search for `lean prover`.
4. Click "install", and then "reload" to restart VS Code.
5. Setup the default shell:
  * If you're using `git bash`, press `ctrl-shift-p` to open the command palette, and type
    `Select Default Shell`, then select `git bash` from the menu.
  * If you're using `msys2`, press `ctrl-comma` again to open the settings, and add two settings:
  ```
  "terminal.integrated.shell.windows": "C:\\msys64\\usr\\bin\\bash.exe",
  "terminal.integrated.shellArgs.windows": ["--login", "-i"]
  ```
6. Verify Lean is working, for example by saving a file `test.lean` and entering `#eval 1+1`.
   A green line should appear under this, and hovering the mouse over it you should see `2`
   displayed.

You can now read instructions about creating and working on [Lean projects](project.md)
