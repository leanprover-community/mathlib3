# How to install Lean and mathlib on Debian/Ubuntu

This document explains how to get started with Lean and mathlib if you
are using a Linux distribution derived from Debian (Debian itself,
Ubuntu, LMDE,...). All commands below should be typed inside a terminal.
This document has three parts: installing Lean, creating a new project,
and working on an existing project.

If you get stuck, please come to [the chat room](https://leanprover.zulipchat.com/) to ask for
assistance.

## Installing Lean

* Lean itself doesn't depend on much infrastructure, but supporting tools
  needed by most users require `git`, `curl`, and `python`. So the first step is:
  ```bash
  sudo apt install git curl python3 python3-pip
  ```

* You will also new a code editor that has a Lean plugin. The
  recommended choice for is [Visual Studio Code](https://code.visualstudio.com/).
  The alternative is to use Emacs, see https://github.com/leanprover/lean-mode.
  ```bash
  curl https://go.microsoft.com/fwlink/?LinkID=760868
  sudo apt install ./code_*.deb
  code --install-extension jroesch.lean
  ```
  Everything else will be installed in user-space (no sudo required).

* The next step installs a small tool called `elan` which will handle
  updating Lean according to the need of your current project (hit Enter
  when a question is asked). It will live in `$HOME/.elan` and add a
  line to `$HOME/.profile`.
  ```bash
  curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh
  ```

* Then we install a small tool called `update-mathlib` that which will handle
  updating mathlib according to the need of your current project.
  It will live in `$HOME/.mathlib` and add a line to `$HOME/.profile`.
  ```bash
  curl https://raw.githubusercontent.com/leanprover-community/mathlib/master/scripts/remote-install-update-mathlib.sh -sSf | bash
  ```

## Creating a Lean project

Lean files are organized in projects called packages. The tool `leanpkg`
manages project creation and dependencies. We will now create a new
project depending on mathlib. The following commands should be type in a
terminal.

* If you have not logged in since you installed Lean and mathlib, then
  you need to first type `source ~/.profile`. 

* Then go to a folder where you want to create a project in a subfolder
  `my_project`, and type:
	```bash
	leanpkg new my_project
	cd my_project
	leanpkg add leanprover-community/mathlib
	update-mathlib
	```

* launch VScode, either through your application menu or by typing
  `code`

* On the main screen, or in the File menu, click "Open folder", and
  choose the folder `my_project` (*not* one of its subfolders).

* Your Lean code should now be put inside files with extension `.lean`
  living in `my_project/src/` or a subfolder thereof.

If you want to make sure everything is working, you can start my
creating, say `my_project/src/test.lean` containing:
```lean
import topology.basic

#check topological_space
```
When the cursor is on the last line, the right hand part of VScode
should display a "Lean messages" area saying: 
`topological_space : Type u_1 → Type u_1`

If, for some reason, you happen to loose the "Lean messages" area, you
can get it back with "Ctrl-Shift-Enter". Also, you can get the Lean
documentation inside VScode using "Ctrl-Shift-p" and then, inside the
text field that appeared, type "lean doc" and hit Enter.

## Working on an existing package

Suppose you want to work on an existing project.
As example, we will take [Perfectoid spaces](https://github.com/leanprover-community/lean-perfectoid-spaces).

* If you have not logged in since you installed Lean and mathlib, then
  you need to first type `source ~/.profile`. 

* Go the the directory where you would like this package to live.

* Run `git clone https://github.com/leanprover-community/lean-perfectoid-spaces.git`.

* This gives you a directory named `lean-perfectoid-spaces`. Enter it.

* Type `update-mathlib` to get mathlib ready for use in this project.

* Type `leanpkg build` to compile everything, this will take some time.

* launch VScode, either through your application menu or by typing
  `code`

* On the main screen, or in the File menu, click "Open folder", and
  choose the folder `lean-perfectoid-spaces` (*not* one of its subfolders).

* Using the file explorer on the left-hand side, explore everthing you want in 
  `lean-perfectoid-spaces/src`
