# Controlled installation of Lean and mathlib on Debian/Ubuntu

This document explains a more controlled installation procedure 
for Lean and mathlib on Linux distributions derived from Debian (Debian itself,
Ubuntu, LMDE,...). There is a quicker way described in the main
[install page](install_debian.md) but it requires more trust.
Of course you can get even more details about what is going on by
reading the bash scripts that will be downloaded below:
[elan_init](https://github.com/Kha/elan/blob/master/elan-init.sh) and
[remote-install-update-mathlib](https://github.com/leanprover-community/mathlib/blob/master/scripts/remote-install-update-mathlib.sh).
All commands below should be typed inside a terminal.

* Lean itself doesn't depend on much infrastructure, but supporting tools
  needed by most users require `git`, `curl`, and `python`. So the first step is:
  ```bash
  sudo apt install git curl python3 python3-pip
  ```

* You will also need a code editor that has a Lean plugin. The
  recommended choice is [Visual Studio Code](https://code.visualstudio.com/).
  The alternative is to use Emacs, and its [lean-mode](https://github.com/leanprover/lean-mode).
  ```bash
  wget -O code.deb https://go.microsoft.com/fwlink/?LinkID=760868
  sudo apt install ./code.deb
  rm code.deb
  code --install-extension jroesch.lean
  ```
  Everything else will be installed in user-space (no sudo required).

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
  curl https://raw.githubusercontent.com/leanprover-community/mathlib/master/scripts/remote-install-update-mathlib.sh -sSf | bash
  ```

You can now read instructions about creating and working on [Lean projects](project.md)
