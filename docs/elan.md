# How to install Lean using `elan`

This document explains how to get started with Lean and mathlib.

If you get stuck, please come to [the chat room](https://leanprover.zulipchat.com/) to ask for
assistance.

If you'd prefer to watch a short video tutorial, try:
* [Installation instructions for Windows 10](https://www.youtube.com/watch?v=2f_9Zetekd8)
* [Installation instructions for macOS](https://www.youtube.com/watch?v=k8U6YOK7c0M)

## Preliminaries

We'll need to set up Lean, an editor that knows about Lean, and `mathlib` (the standard library).

Rather than installing Lean directly, we'll install a small program called `elan` which
automatically provides the correct version of Lean on a per-project basis. This is recommended for
all users.

### Installing `elan`

1. We'll need a terminal, along with some basic prerequisites.
  * Ubuntu: `sudo apt install git curl` if you don't already have these.
  * macOS: Install [homebrew](https://brew.sh/), then run `brew install gmp coreutils` in a terminal
    (`gmp` is required by `lean`, `coreutils` by `leanpkg`).
  * Windows 10:
    * Either (recommended): install [Git for Windows](https://gitforwindows.org/), after which you
      can open a terminal by typing "git bash" in the Windows search bar.
    * Or: install [Msys2](https://www.msys2.org/), after which you can open a terminal by
      typing "msys2" in the Windows search bar. You'll also need to run `pacman -S unzip git` in
      an msys2 terminal.

2. (This step can be skipped: VS Code will prompt you to install `elan` if it can't find a
   usable copy of Lean.)

   At a terminal, run the command

   `curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh`

   and hit enter when a question is asked.

   On Linux and on macOS, this automatically appends a line to your `$HOME/.profile`
   which prepends `$HOME/.elan/bin` to your `$PATH`.

   On Windows, this doesn't happen automatically. 
   * With Git for Windows you'll need to run `echo 'PATH="$HOME/.elan/bin:$PATH"' >> $HOME/.profile` in the terminal.
   * With MSYS2 you'll need to run `echo 'PATH="/c/Users/$USERNAME/.elan/bin:$PATH"' >> $HOME/.bashrc`.

   It is recommended that you re-login,
   so that your environment knows about `elan`.

   (Alternatively, type `source $HOME/.elan/env` to update the current terminal.)

### Installing and configuring an editor

There are two Lean-aware editors, VS Code and emacs.
This document describes using VS Code (for emacs, look at https://github.com/leanprover/lean-mode).

1. Install [VS Code](https://code.visualstudio.com/).
2. Launch VS Code.
3. Click on the extension icon in the view bar at the left
   and search for `lean`.
4. Click "install", and then "reload" to restart VS Code.
5. If you're running Windows, you've got one more step:
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

## Scenario 1: Start a new package

When you installed `elan`, it downloaded the latest stable release of Lean.
That may be too recent or too old for mathlib, and you really want mathlib.

1. Decide on a name for your package. We will use `my_playground`.
2. Run `leanpkg +nightly new my_playground`.
   This will create a `my_playground` directory with a Lean project layout.
3. Run `cd my_playground`.
4. Run `leanpkg add leanprover/mathlib`.
   This will download mathlib and put it inside `my_playground/_target/deps/mathlib/`.

That's it.
At this point you can already create some Lean file in `my_playground/src`:
say `test.lean`.

1. Now launch VS Code.
2. On Windows: Click "File -> Open folder" (Ctrl-K Ctrl-O) and open `my_playground`.
   On macOS: Click "File -> Open..." and open `my_playground`. It is essential that you open the *folder*, rather than a file inside it.
3. Open the file `test.lean`, from the 'Explorer' view on the left edge of VS Code.
4. Type Ctrl-Shift-Enter (Cmd-Shift-Enter on macOS) to open the Lean message window.
5. Type, say `#check 1` to see the result.

You can also use `import group_theory.subgroup` and then `#check is_subgroup`.
This will use the uncompiled version of mathlib, which is very inefficient.
But if you run `leanpkg build` from inside `my_playground`,
then it will compile only those files that are dependencies of
mathlib `group_theory/subgroup.lean`.

If you want to play more, it's better to compile all of mathlib
once and for all.
You can do this by going into `my_playground`
and running `lean --make _target/deps/mathlib`. (Don't actually go into the mathlib directory and
run `lean --make` there!)

Now go and get some coffee.

## Scenario 2: Work on an existing package

Suppose you want to work on an existing project.
As example, we will take https://github.com/kbuzzard/lean-stacks-project.

1. Go the the directory where you would like this package to live.
2. Run `git clone https://github.com/kbuzzard/lean-stacks-project`.
3. This gives you a directory named `lean-stacks-project`. Enter it.
4. Inside this directory is a file named `leanpkg.toml`.
   `elan` uses this file to determine which version of Lean you need.
   You don't have to worry about this!
5. Run `leanpkg build` to compile everything.
6. Now is a good time to get yourself some tea and relax.

Once the compile is over, you can start working.

1. Now launch VS Code.
   (If you did not re-login after installing `elan`,
   then you may have to launch VS Code from a terminal that has
   sourced `$HOME/.elan/env`.)
2. On Windowds: Click "File -> Open folder" (Ctrl-K Ctrl-O) and open `lean-stacks-project`.
   On macOS: Check "File -> Open..." and open `lean-stacks-project`.
3. Type Ctrl-Shift-Enter (Cmd-Shift-Enter on macOS) to open the Lean message window.
