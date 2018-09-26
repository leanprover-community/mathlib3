# How to install Lean using elan

This document explains how to get started with Lean and mathlib.

## Preliminaries

We'll need to set up Lean, an editor that know about Lean, and `mathlib` (the standard library).

Rather than installing Lean ourselves, we'll install a small program called Elan
which automatically provides the correct version of Lean on a per-project basis. This is very
helpful and recommended for all users.

### Installing Elan

1. We'll need a terminal along with some basic prerequisites.
  * Ubuntu: Probably you have everything already, but `sudo apt-get install git curl` should be enough.
  * macOS: We need `libgmp`, which isn't available by default. The recommended course is to
    install [homebrew](https://brew.sh/), then run `brew install libgmp` in a terminal. 
  * Windows 10: 
    * Install the [Visual C++ redistributable](https://www.microsoft.com/en-au/download/details.aspx?id=48145).
    * Install [Git for Windows](https://gitforwindows.org/).
    * In the following instructions, you'll use a "git bash" terminal, which you can start by
      typing "git bash" in the Windows search bar.

2. At a terminal, run the command

   `curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh`

   and hit enter when a question is asked.
   This automatically appends a line to your `$HOME/.profile`
   which prepends `$HOME/.elan/bin` to your `$PATH`.

   It is recommended that you re-login,
   so that your environment knows about Elan.
   
   (Alternatively, type `source $HOME/.elan/env` into your terminal.
   Now this terminal session knows about Elan.)

### Installing and configuring an editor

Currently, there are two Lean-aware editors:
VS Code and emacs.
This document describes using VS Code (for emacs, look at https://github.com/leanprover/lean-mode).

1. Install [VS Code](https://code.visualstudio.com/).
2. Launch VScode.
3. Click on the extension icon in the view bar at the left
   and search for `lean`.
4. Click "install", and then "reload" to restart VS Code.

## Scenario 1: Start a new package

When you installed Elan, it downloaded the latest stable release of Lean.
That may be too recent or too old for mathlib, and you really want mathlib.
Have a look at
https://github.com/leanprover/mathlib/blob/master/leanpkg.toml#L4 to see what
is the nightly that mathlib currently wants.
Say you see `nightly-2018-04-06`.

1. Decide on a name for your package. We will use `my_playground`.
2. Run `elan run --install nightly-2018-04-06 leanpkg new my_playground`.
   This will create a `my_playground` directory with a Lean project layout.
3. Run `cd my_playground`.
4. Run `leanpkg add leanprover/mathlib`.
   This will download mathlib and put it inside `my_playground/_target/deps`.

That's it.
At this point you can already create some Lean file in `my_playground/src`:
say `test.lean`.

1. Now launch VS Code.
2. Click "File -> Open folder" (Ctrl-K Ctrl-O) and open `my_plaground`.
3. Open the file `test.lean`.
4. Type Ctrl-Shift-Enter to open the Lean message window.
5. Type, say `#check 1` to see the result.

You can also use `import group_theory.subgroup` and then `#check is_subgroup`.
This will use the uncompiled version of mathlib, which is very inefficient.
But if you run `leanpkg build` from inside `my_playground`,
then it will compile only those files that are dependencies of
mathlib `group_theory/subgroup.lean`.

If you want to play more, it's better to compile all your dependencies
once and for all.
You can do this by going into `my_playground`
and running `leanpkg build`.

Now go and get some coffee.

## Scenario 2: Work on an existing package

Suppose you want to work on an existing project.
As example, we will take https://github.com/kbuzzard/lean-stacks-project.

1. Go the the directory where you would like this package to live.
2. Run `git clone https://github.com/kbuzzard/lean-stacks-project`.
3. This gives you a directory named `lean-stacks-project`. Enter it.
4. Inside this directory is a file named `leanpkg.toml`.
   Elan uses this file to determine which version of Lean you need.
   You don't have to worry about this!
5. Run `leanpkg build` to compile everything.
6. Now is a good time to get yourself some tea and relax.

Once the compile is over, you can start working.

1. Now launch VS Code.
   (If you did not re-login after installing Elan,
   then you have to launch VS Code from a terminal that has
   sourced `$HOME/.elan/env`.)
2. Click "File -> Open folder" (Ctrl-K Ctrl-O) and open `lean-stacks-project`.
2. Type Ctrl-Shift-Enter to open the Lean message window.
