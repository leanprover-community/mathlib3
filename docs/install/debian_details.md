# Controlled installation of Lean and mathlib on Debian/Ubuntu

This document explains a more controlled installation procedure
for Lean and mathlib on Linux distributions derived from Debian (Debian itself,
Ubuntu, LMDE,...). There is a quicker way described in the main
[install page](install_debian.md) but it requires more trust.
Of course you can get even more details about what is going on by
reading the bash script that will be downloaded below:
[elan_init](https://github.com/Kha/elan/blob/master/elan-init.sh).

* Lean itself doesn't depend on much infrastructure, but supporting tools
  needed by most users require `git`, `curl`, and `python`. So the first step is:
  ```bash
  sudo apt install git curl python3 python3-pip
  ```

* The next step installs a small tool called `elan` which will handle
  updating Lean according to the needs of your current project (hit Enter
  when a question is asked). It will live in `$HOME/.elan` and adds a
  line to `$HOME/.profile`.
  ```bash
  curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh
  ```

* There are two editors you can use with Lean, VS Code and emacs. The
  recommended choice is [Visual Studio Code](https://code.visualstudio.com/).
  ```bash
  wget -O code.deb https://go.microsoft.com/fwlink/?LinkID=760868
  sudo apt install ./code.deb
  rm code.deb
  code --install-extension jroesch.lean
  ```

  Now open VS Code, and verify Lean is working, for example by saving a file `test.lean` and entering `#eval 1+1`.
   A green line should appear underneath `#eval 1+1`, and hovering the mouse over it you should see `2`
   displayed.

  The alternative is to use Emacs, and its [lean-mode](https://github.com/leanprover/lean-mode).

* Then we install a small tool called `leanproject` that will handle
  updating mathlib according to the needs of your current project.
  ```bash
  sudo pip3 install mathlibtools
  ```

Note however that you cannot use mathlib, and in particular any imports,
in the file `test.lean` created above.

## You're not done yet!

👉 If you want to use mathlib, you should now read the instructions about creating and working on [Lean projects](project.md).
