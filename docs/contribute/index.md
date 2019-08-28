# How to contribute to mathlib

Principally mathlib uses the fork-and-branch workflow. See
https://blog.scottlowe.org/2015/01/27/using-fork-branch-git-workflow/
for a good introduction.

Here are some tips and tricks
to make the process of contributing as smooth as possible.

1. Use [Zulip](https://leanprover.zulipchat.com/) to
   discuss your contribution before and while you are working on it.
2. Adhere to the guidelines:
   - The [style guide](style.md) for contributors.
   - The explanation of [naming conventions](naming.md).
   - The [documentation guidelines](doc.md).
   - The [git commit conventions](https://github.com/leanprover/lean/blob/master/doc/commit_convention.md).
3. Create a pull request from a feature branch on your personal fork,
   as explained in the link above, or from a branch of the main repository if you have commit access (you can ask for access on Zulip).
4. If you've made a lot of changes/additions, try to make many PRs containing small, self-contained pieces. This helps you get feedback as you go along, and it is much easier to review. This is especially important for new contributors.
5. If you checkout the remote branch `lean-3.4.2` you can fetch the `.olean` binaries using the command
   ```
   cache-olean --fetch
   ```
   - You can do this by running the following commands (anywhere in the `mathlib` repository).
   ```
   git fetch --all
   git checkout origin/lean-3.4.2
   cache-olean --fetch
   git checkout -b my_new_feature
   ```
   - Some users have reported that Lean will recompile the library even after the `.olean` files have been downloaded correctly. This happens because the timestamps of the binaries are older than the timestamps of the `.lean` files. If this happens, you can run the following command to update the timestamps (in the `mathlib` directory):
   ```
   find src/ -name '*.olean' -exec touch {} +
   ```
   - See [Caching compilation](#caching-compilation) for commands to do this automatically.

## The nursery

Finally, https://github.com/leanprover-community/mathlib-nursery
makes it possible to have early access to work in progress.
See [its README](https://github.com/leanprover-community/mathlib-nursery/blob/master/README.md)
for more details.

## Caching compilation

In the `mathlib` git repository, you can run the following in a terminal:

```sh
$ curl https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/remote-install-update-mathlib.sh -sSf | bash
$ source ~/.profile
$ setup-lean-git-hooks
```

It will install scripts including `update-mathlib` and `cache-olean`
and setup git hooks that will call `cache-olean` when making a commit
and `cache-olean --fetch` and `update-mathlib` when checking out a
branch. `update-mathlib` will fetch a compiled version of `mathlib`
and `cache-olean` will store and fetch the compiled binaries of the
branches you work.
