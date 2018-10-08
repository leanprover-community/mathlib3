# How to contribute to mathlib

Principally mathlib uses the fork-and-branch workflow. See
https://blog.scottlowe.org/2015/01/27/using-fork-branch-git-workflow/
for a good introduction. Additionally, instead of merging, the mathlib
community uses rebase to rewrite history and add users commits at the
very end of the master branch. See
https://www.atlassian.com/git/tutorials/rewriting-history/git-rebase
for an introduction to rebasing.

Here are some tips and tricks
to make the process of contributing as smooth as possible.

1. Use Zulip: https://leanprover.zulipchat.com/#
   Discuss your contribution while you are working on it.
2. Adhere to the guidelines:
   - The [style guide](/docs/style.md) for contributors.
   - The explanation of [naming conventions](/docs/naming.md).
   - The [git commit conventions](https://github.com/leanprover/lean/blob/master/doc/commit_convention.md).
3. Create a pull request from a feature branch on your personal fork,
   as explained in the link above.

## The community fork and the nursery

The community also uses https://github.com/leanprover-community/mathlib
for collaborative contributions: ask on Zulip if you'd like commit access.

Finally, https://github.com/leanprover-community/mathlib-nursery
makes it possible to have early access to work in progress.
See [its README](https://github.com/leanprover-community/mathlib-nursery/blob/master/README.md)
for more details.

## Caching .olean files

Contributing to mathlib often involves working on multiple branches in
alternation. Every switch often involves recompiling a fair portion of
the mathlib proofs. To reduce the recompilation, mathlib has scripts
setting up git to automatically backup to the .olean files produced by
processing .lean files. The setup script can be called as:

```shell
tools/install-hooks.sh
```

The script sets up git hooks that are executed whenever:

    1. a branch is checked out
    2. branches are rebased
    3. code is committed

.olean files can also manually cached and restored with:

    * `tools/cache_olean.sh`
    * `tools/restore_olean.sh`
