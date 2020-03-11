# Creating a Lean project

Lean files are organized in projects called packages. The tool `leanproject`
manages project creation and dependencies. We will now create a new
project depending on mathlib. The following commands should be typed in a
terminal.

* If you have not logged in since you installed Lean and mathlib, then
  you need to first type `source ~/.profile`.

* Then go to a folder where you want to create a project in a subfolder
  `my_project`, and type:
        ```bash
        leanproject new my_project
        ```

* launch VScode, either through your application menu or by typing
  `code my_project`

* If you launched VScode through a menu: on the main screen, or in the
  File menu, click "Open folder" (on a Mac, just "Open"), and
  choose the folder `my_project` (*not* one of its subfolders).

* Your Lean code should now be put inside files with extension `.lean` living in `my_project/src/` or a subfolder thereof. In the file explorer on the left-hand side of VScode, you can right-click on `src`, choose `New file`, and type a filename to create a file there.

If you want to make sure everything is working, you can start by
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
text field that appeared, type "lean doc" and hit Enter. Then click
"Theorem proving in Lean" and enjoy.

# Working on an existing package

Suppose you want to work on an existing project.
As example, we will take [the tutorial project](https://github.com/leanprover-community/tutorials). Open a terminal.

* If you have not logged in since you installed Lean and mathlib, then
  you need to first type `source ~/.profile`.

* Go the the directory where you would like this package to live.

* Run `leanproject get tutorials`

* launch VScode, either through your application menu or by typing
  `code tutorials` (MacOS users need to take a one-off
  [extra step](https://code.visualstudio.com/docs/setup/mac#_launching-from-the-command-line)
   to be able to launch VScode from the command line)

* If you launched VScode from a menu, on the main screen, or in the File menu, click "Open folder" (just "Open" on
a Mac), and choose the folder `tutorials` (*not* one of its subfolders).

* Using the file explorer on the left-hand side, explore everthing you want in
  `tutorials/src`
