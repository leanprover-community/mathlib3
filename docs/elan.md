# How to lean with elan

    Assumptions:
    You are working on a Linux system, or something similar.
    You can use a terminal.

This document explains how to get started with Lean and mathlib.
There are two scenarios:

1. Start a new package (= 'project')
2. Work on an existing package

We will dive into these scenarios after we have covered some preliminaries.

## Preliminaries

You need to install Lean, and you need an editor that knows about Lean.
(If your editor does not know about Lean,
then you will hit a wall very soon.)

But do not install Lean immediately. Here is why:
Different packages (think, 'projects')
might need different versions of Lean.
Therefore it is recommended to install Elan.
Elan is a small program that looks at a special filein your package
to determine which version of Lean (and mathlib) you need.
It will then automagically make sure that you use
this correct version of Lean (and mathlib).

### Installing Elan

1. Make sure `git` and `curl` are installed.
   For example, use your distributions package manager.
2. Run the command

   `curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh`

   and type enter when a question is asked.
   This automatically appends a line to your `$HOME/.profile`
   which prepends `$HOME/.elan/bin` to your `$PATH`.
   It is recommended that you re-login,
   so that your environment knows about Elan.
   
   (Alternatively, type `source $HOME/.elan/env` into your terminal.
   Now this terminal session knows about Elan.)

### Installing and configuring an editor

Currently, there are two Lean-aware editors:
VScode and emacs.
This document only covers VScode.
(If you want to know how to make emacs Lean-aware,
take a look at https://github.com/leanprover/lean-mode
and its README.)

1. Install VScode (https://code.visualstudio.com/).
   For example, use your distributions package manager.
2. Launch VScode and install the Lean extension:
   click on the extension icon in the view bar at the left
   and search for `lean`.
3. Quit VScode for now

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

1. Now launch VScode.
   (If you did not re-login after installing Elan,
   then you have to launch VScode from a terminal that has
   sourced `$HOME/.elan/env`.)
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

1. Now launch VScode.
   (If you did not re-login after installing Elan,
   then you have to launch VScode from a terminal that has
   sourced `$HOME/.elan/env`.)
2. Click "File -> Open folder" (Ctrl-K Ctrl-O) and open `lean-stacks-project`.
2. Type Ctrl-Shift-Enter to open the Lean message window.
