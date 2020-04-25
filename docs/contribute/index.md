# How to contribute to mathlib

Principally mathlib uses the fork-and-branch workflow. See
https://blog.scottlowe.org/2015/01/27/using-fork-branch-git-workflow/
for a good introduction.

Here are some tips and tricks to make the process of contributing as smooth as possible.

1. Use [Zulip](https://leanprover.zulipchat.com/) to
   discuss your contribution before and while you are working on it.
2. Adhere to the guidelines:
   - The [style guide](style.md) for contributors.
   - The explanation of [naming conventions](naming.md).
   - The [documentation guidelines](doc.md).
   - The [git commit conventions](https://github.com/leanprover-community/lean/blob/master/doc/commit_convention.md).
3. Create a pull request from a feature branch on your personal fork,
   as explained in the link above, or from a branch of the main repository if you have commit access (you can ask for access on Zulip).
   If you use an external repository, please make sure that repository has GitHub Actions enabled.
4. If you've made a lot of changes/additions, try to make many PRs containing small, self-contained
   pieces. This helps you get feedback as you go along, and it is much easier to review. This is
   especially important for new contributors.
5. You can use `leanproject get-cache` to fetch `.olean` binaries.
   ```
   leanproject get-cache
   git checkout -b my_new_feature
   ```
   - See [Caching compilation](#caching-compilation) for commands to automatically call `leanproject get-cache`.
6. We are using [bors](https://bors.tech/) to merge PRs. See [these notes](bors.md) for more details.

## The nursery

Finally, https://github.com/leanprover-community/mathlib-nursery
makes it possible to have early access to work in progress.
See [its README](https://github.com/leanprover-community/mathlib-nursery/blob/master/README.md)
for more details.

## Caching compilation

In the `mathlib` git repository, you can run the following in a terminal:

```sh
sudo pip3 install mathlibtools
leanproject hooks
```

This will install the `leanproject` tool.  The call to `leanproject hooks`
sets up git hooks that will call cache the olean files when making a commit
and fetching the olean files when checking out a branch.
See the [mathlib-tools documentation](https://github.com/leanprover-community/mathlib-tools/blob/master/README.md)
for more information.
