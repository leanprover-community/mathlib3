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

   We recommend that you use `git bash` and not `msys2`, since installing the supporting tools (below) causes issues in `msys2`.

   Install [Git for Windows](https://gitforwindows.org/) (you can accept all default answers during installation).
   Then open a terminal by typing `git bash` in the Windows search bar.

2. In terminal, run the command

   `curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh`

   and hit enter when a question is asked.
   To make sure the terminal will find the installed files, run `echo 'PATH="$HOME/.elan/bin:$PATH"' >> $HOME/.profile`.

  Then close and reopen Git Bash.

Installing mathlib supporting tools
---

In order to use mathlib supporting tools, you need to [get python](https://www.python.org/downloads/) first.

### Get Python

* Download the latest version of python [here](https://www.python.org/downloads/).
* Run the downloaded file (`python-3.x.x.exe`)
* Check `Add Python 3.x to PATH`.
* Choose the default installation.
* Open Git Bash (type `git bash` in the Start Menu)
* Run `which python`
  * The expected output is something like `/c/Users/<user>/AppData/Local/Programs/Python/Pythonxx-xx/python`. In this case, proceed to the next step.
  * If it's something like `/c/Users/<user>/AppData/Local/Microsoft/WindowsApps/python`, then you need to disable a Windows setting.
    * Type `manage app execution aliases` into the Windows search prompt (start menu) and open the corresponding System Settings page.
    * There should be two entries `App Installer python.exe` and `App Installer python3.exe`. Ensure that both of these are set to `Off`.
    * Close and reopen Git Bash and restart this step.
  * If it is any other directory, you might have an existing version of Python. Ask for help in the Zulip chat room (linked above).
  * If you get `command not found`, you should add the Python directory to your path. Google how to do this, or ask on Zulip.
* Run `cp "$(which python)" "$(which python)"3`. This ensures that we can use the command `python3` to call Python.
* Test whether everything is working by typing `python3 --version` and `pip3 --version`. If both commands give a short output and no error, everything is set up correctly.
  * If `pip3 --version` doesn't give any output, run the command `python3 -m pip install --upgrade pip`, which should fix it.


### Configure Git

* Run `git config --global core.autocrlf input` in Git Bash
  * Alternatively, you can set it to `false`. If it is set to `true`, you might run into issues when running `update-mathlib` or `cache-olean --fetch`.

### Get Scripts

Then, at a terminal, run the command
  ```bash
  curl https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/remote-install-update-mathlib.sh -sSf | bash
  ```
Run `source ~/.profile` or close and reopen Git Bash.

Installing and configuring an editor
---

There are two Lean-aware editors, VS Code and emacs.
This document describes using VS Code (for emacs, look at https://github.com/leanprover/lean-mode).

1. Install [VS Code](https://code.visualstudio.com/).
2. Launch VS Code.
3. Click on the extension icon ![(image of icon)](new-extensions-icon.png)
   (or ![(image of icon)](extensions-icon.png) in older versions) in the side bar on the left edge of
   the screen (or press <kbd>Shift</kbd><kbd>Ctrl</kbd><kbd>X</kbd>) and search for `leanprover`.
4. Click "install" (In old versions of VSCode, you might need to click "reload" afterwards)
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
