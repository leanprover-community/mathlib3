# The Lean tool chain

## Introduction

In this document we explain how all the various pieces of the Lean tools ecosystem fit together. 
Understanding this precisely is not required, but it will help if you decide to explore non-recommended setups.
In particular we will gradually introduce new pieces in the story, starting with a bare bone Lean. 
This is *not* the recommended setup.
Also this document is long, that's the price for not wanting to blindly follow the recommended setup instructions.

## Installing Lean and checking files

### Installing Lean

Of course the main piece is Lean itself. You can download Lean binaries for your OS [here](https://github.com/leanprover-community/lean/releases). 
This contains folders `bin`, `include` and `lib`.
The `bin` folder contains a `lean` executable which you can run.

That's all, Lean is installed!

You can make it slightly more convenient to use by ensuring this `bin` folder is in your path, or maybe by creating a link to 
`lean` from a folder which is in your path.

### Proving stuff

You can now check your first proof.
In a file called `test.lean`, type:
```lean
lemma zero_max (m : ℕ) : max 0 m = m :=
max_eq_right (nat.zero_le m)
```
Then you can ask Lean to check this proof by running `lean test.lean`. 
Lean will think for a second (most of it spent in intialization) and return control to you, without outputing anything.
That's Lean's idea of a dignified triumph.
If you start messing up with the file, say deleting the final `m` on the last line,
Lean will output an error message.
That's 99.9% of what Lean and its supporting tool do,
but the remaining 0.1% will make your life much easier. 

Before turning to that, you need to understand why Lean didn't ask for the definition of `ℕ`, `max`, `max_eq_right` and `nat.zero_le`.
That's because all those are defined in the part of Lean's core library that is automatically loaded by default.
This default library lives in the `lib` folder you saw after downloading Lean, 
precisely in `lib/lean/library/init/`.
You can prevent loading it by starting your `test.lean` with the line `prelude`.
Then everything will fall apart. 
Lean will not know about `ℕ`, `max`, or even the equality sign!
And it won't attempt to read the proof of a statement it couldn't understand.
So you should not keep that `prelude` line.


###  Working with several files

Your Lean work has grown quite a bit since you installed Lean,
so let's start a second file, `test2.lean` that should build on the knowledge gathered in `test.lean`.
In `test2.lean`, put an important special case of our `zero_max` lemma:
```lean
lemma zero_max_one : max 0 1 = 1 :=
zero_max 1
```
Trying to compile it with `lean test2.lean` fails: Lean complains it doesn't know about
our `zero_max` lemma.
You need to tell Lean that `test2.lean` relies on `test.lean`. 
So add at the top of `test2.lean` the line `import test`.
Now Lean complains it cannot find the file `test` in `LEAN_PATH`.
You can ask Lean where it searches for files by running `lean --path`, and paying attention
to the lines in the "path" list.
Notice this list does not contain the folder where `test.lean` is sitting.
That all caps name in the error message suggests setting an environment variable called `LEAN_PATH` could help.
Indeed you can run:
```bash
LEAN_PATH=path_to_our_lean_install_folder/lib/lean/library/:path_to_folder_containing_test lean test2.lean 
```
and this succeeds.
Note that omitting the first part would have brought you to the prelude situation where Lean does not know
about natural numbers or equality.

Setting this `LEAN_PATH` variable is clearly annoying.
There is a much better way, and actually you should *never* set this environment variable.
Now create, next to `test.lean` and `test2.lean`, a file `leanpkg.path` containing:
```
builtin_path
path .
```
That's it, each time you'll invoke Lean from within this folder or one of its subfolders,
it will look for files in the default places and in the folder containing your new `leanpkg.path`
(the path mentioned in the second line is relative to the folder containing `leanpkg.path`, and `.` means current folder).
Now check `lean --path` from outside or inside the folder containing `leanpkg.path` to see the difference.

### Keeping compiled versions

Note that `lean` rechecks `test.lean` each time you ask it to check `test2.lean`, 
even if `test.lean` was not modified since it was last checked. 
This is clearly a waste of CPU.
You can ask Lean to remember its work by running `lean --make test.lean`.
This will create `test.olean` containing all the relevant information from `test.lean` you need in
`test2.lean`.
The source file `test.lean` won't be checked again while checking `test2.lean` as long as you don't modify its content.

## Interactive theorem proving

Lean is branded as an *interactive* theorem prover.
Writing files and asking Lean to check them is not very interactive.
For instance, you should be able to interactively ask Lean where `max` is defined.
Remember you typed that `max` name on the first line of `test.lean`, in columns 26 to 28.
You can run Lean is interactive mode, also known as server mode, using `lean --server`.
Again not much happens.
Lean is waiting for instructions or questions on the standard input pipe.
You can ask it to have a look at `test.lean` by typing:
```
{ "command": "sync", "file_name": "test.lean", "seq_num": 1 }
```
It will answer a couple of messages, claiming to start working, and then be to done before returning to silence.
You can then ask for information about what's at column 27 of line 1 of `test.lean` by typing:
```
{ "command": "info", "file_name": "test.lean", "line": 1, "column": 27, "seq_num": 2 } 
```
Lean's answer will include the location of the file defining `max` as well as the type of
`max`.

Now tell Lean you want to modify the file `test.lean` to remove the final `m` at the end (you're only pretending to do this modification, nothing will be written in the file here):
```
{ "command": "sync", "file_name": "test.lean", "content": "lemma zero_max (m : ℕ) : max 0 m = m :=\nmax_eq_right (nat.zero_le)", "seq_num": 3 }
```
Lean will immediately reply with the error message we saw earlier,
complaining that `nat.zero_le` has type `∀ (n : ℕ), 0 ≤ n` but is expected to have type `0 ≤ m`.

By now you should be tired of interacting directly with Lean's interactive mode.
It's time to install an editor having some plugin that will do the talking with
`lean --server`.
Currently you get to choose between emacs and VS code.
That editor plugin will also be in charge of finding the `lean` executable and starting `lean --server`
inside the directory containing the `leanpkg.path` that you carefully crafted in the previous section.


##  Handling dependencies

Your current project only has two files, `test.lean` and `test2.lean` which
both depend on part of Lean's core library.
But you want to start using what other people did, so you'll need other Lean files,
for instance from [mathlib](https://github.com/leanprover-community/mathlib).
You could download mathlib, and add a line to your `leanpkg.path` pointing to 
`mathlib/src`.
But of course you'll want to put your project under version control without versioning mathlib,
which is already versioned somewhere else.
And you want to update mathlib regularly to enjoy all the latest goodies.
And mathlib is very long to compile (ie. making olean files), so you'd like to get a precompiled version.

All this means you need a Lean project manager.
Your download at the very beginning does include such a tool, at
`bin/leanpkg`.
That one is written in Lean (you can see all the code in `lib/lean/leanpkg/`), so you already have all
the required dependencies.
However Lean, at least in its current series Lean 3.X.X, is not convenient at all to build a *powerful*
project manager.
So the Lean user community has built a more powerful project manager written in python: `leanproject`.
The downside is you need to have a sane python3 environment to use it, so that you can
run something like `pip install mathlibtools` to get it,
see [mathlib-tools' webpage](https://github.com/leanprover-community/mathlib-tools/blob/master/README.md) for more information.

For historical reasons, `leanproject` still calls `leanpkg` for some simple operations.
Because of this and for compatibility reasons,
both managers use the same configuration file for your project,
called `leanpkg.toml`.
This file should be at the root of your project.
It is written in the config file language [TOML](https://en.wikipedia.org/wiki/TOML) (which has nothing to do with [ML](https://en.wikipedia.org/wiki/ML_(programming_language)) or [ML](https://en.wikipedia.org/wiki/Machine_learning)).
You don't need to know anything about the required fields of this configuation file, because the package manager
will write everything there for you.
It will also handle writing the `leanpkg.path` file for you,
and download and update a compiled mathlib for you.

## Handling Lean versions

Lean is a very active project.
The core team around Leonardo de Moura at Microsoft research is developing Lean 4, 
which is not yet ready for end users,
while the user community still develops Lean 3.
So you'll want to frequently update Lean itself.
Again you don't want to think about this, so [elan](https://github.com/Kha/elan) will handle it.
This version manager also reads your project `leanpkg.toml`, 
and uses it to decide which version of Lean you want to run,
and download it if needed.
This is completely transparent. 
You can continue to run `lean`,
directly or through your editor plugin or through `leanproject`, 
and `elan` will call the appropriate Lean version.

This is why the first step in the recommended installation procedure is to install `elan`.
Then the second step is to install `leanproject` (in `mathlib-tools`), 
and the third step is to install a compatible editor and its Lean plugin.
And then `leanproject` and the editor plugin handle everything.
