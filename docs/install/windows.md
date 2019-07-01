Installing Lean and mathlib on Windows
===

This document explains how to get started with Lean and mathlib.

If you get stuck, please come to [the chat room](https://leanprover.zulipchat.com/) to ask for
assistance.
If you prefer, you can watch a [short video tutorial](https://www.youtube.com/watch?v=2f_9Zetekd8)

We'll need to set up Lean, an editor that knows about Lean, and `mathlib` (the standard library).
Rather than installing Lean directly, we'll install a small program called `elan` which
automatically provides the correct version of Lean on a per-project basis. This is recommended for
all users.

Installing `elan`
---

1. We'll need a terminal, along with some basic prerequisites.

   Install [Git for Windows](https://gitforwindows.org/), after which you
   can open a terminal by typing "git bash" in the Windows search bar (you can accept all default answers during installation).

2. At a terminal, run the command

   `curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh`

   and hit enter when a question is asked. Then we need to make sure the terminal will find the installed files:
   * With Git for Windows you'll need to run `echo 'PATH="$HOME/.elan/bin:$PATH"' >> $HOME/.profile` in the terminal.
   * With MSYS2 you'll need to run `echo 'PATH="/c/Users/$USERNAME/.elan/bin:$PATH"' >> $HOME/.bashrc`.

   It is recommended that you re-login,
   so that your environment knows about `elan`.
   (Alternatively, type `source $HOME/.elan/env` to update the current terminal.)


Installing mathlib supporting tools
---

In order to use mathlib supporting tools, you need to [get python](https://www.python.org/downloads/) first.

### Get Python

* Download the latest version of python [here](https://www.python.org/downloads/).
* Run the downloaded file (`python-3.x.x.exe`)
* Check `Add Python 3.x to PATH`.
* Choose the default installation.
* Navigate to the folder where Python was installed. A reliable way to do this is to search for `python` in the Start Menu -> right click `Python 3.x (xx-bit)` -> open file location -> right click `Python 3.x (xx-bit)` -> open file location. The default location is something like `C:\Users\<user>\AppData\Local\Programs\Python\Python37-32`.
* Copy the file `python.exe` to `python3.exe`.
* Open Git bash (type `git bash` is the Start Menu)
* Test whether everthing is working by typing `python3 --version` and `pip3 --version`. If both commands give a short output and no error, everything is set-up correctly.
* If `pip3 --version` doesn't give any output, run the command `python3 -m pip install --upgrade pip`, which should fix it.


### Configure Git

* Run `git config --global core.autocrlf input` in Git bash
  * Alternatively, you can set it to `false`. If it is set to `true`, you might run into issues when running `update-mathlib` or `cache-olean --fetch`.

### Get Scripts

Then, at a terminal, run the command
  ```bash
  curl https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/remote-install-update-mathlib.sh -sSf | bash
  ```

Installing and configuring an editor
---

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
   A green line should appear underneath `#eval 1+1`, and hovering the mouse over it you should see `2`
   displayed.

You can now read instructions about creating and working on [Lean projects](project.md)
