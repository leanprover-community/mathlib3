# bors for mathlib!

[![Bors enabled](https://bors.tech/images/badge_small.svg)](https://app.bors.tech/repositories/24316)

In early April 2020, we had a stretch where the mergify queue was constantly 4-5 PRs deep, which
meant that the time between setting a PR as "ready-to-merge" and its landing in `master` was 12+
hours. With mergify, the amount of time it takes to finish merging `N` "ready-to-merge" PRs is
`O(N)`, since every PR is tested against the current master in a serial fashion. This will only get
worse as both build times and the rate of contributions increase.

To address this, we decided to switch from our previous mergify-based workflow to one using
[bors-ng](https://bors.tech/). `bors` is a free service that is able to batch multiple PRs together
in a "`staging`" branch, run the CI scripts on that branch, and then fast-forward `master` if CI
passes.

For PRs with no CI failures, the time from approval to merging should be at most 2*`T`, where `T` is
the amount of time to run CI on a commit. One `T` is for the `staging` build already in progress
when the PR is approved (if any), and one `T` is needed for the batch that the PR is added to.

If CI on `staging` fails (e.g. due to a merge conflict), bors will split the batch in two and try to
merge each of those separately, so that the time to merge is `O(E log N)` where `E` is the error
rate. (See [here](https://github.com/bors-ng/bors-ng/blob/master/README.md#how-it-works) for a few
more details.)

## What has changed?

*[See also bors-ng "Getting Started"](https://bors.tech/documentation/getting-started/) and
["Reference"](https://bors.tech/documentation/)*.

- Using bors is very similar to the previous mergify-based workflow, except that instead of
  approving and adding the "ready-to-merge" label, maintainers just need to remove any "blocked
  labels" ("not-ready-to-merge", "WIP", "blocked-by-other-PR", "merge-conflict", "awaiting-CI")
  and then add a comment to the PR containing "`bors r+`" (or "`bors merge`") on its own line.
  This will add the PR to the last batch in the bors queue. This can be cancelled by commenting with
  "`bors r-`" / "`bors merge-`".

- We have a Github Actions workflow which will try to label approved PRs with
  "ready-to-merge" so that we can see at a glance which open PRs are in the queue. It's not perfect,
  so if you notice a PR that's approved but missing the label, feel free to add the label manually.

- Usually the queue will consist of at most two batches, the batch whose build is in progress and
  one batch that is "Waiting to run", but if errors have occurred, the queue may get longer.
  (Compare this to the mergify queue, whose length is equal to the number of approved PRs.)

- One significant change is that pushing new commits to a PR branch after it's marked "`bors r+`"
  will cancel it (remove it from its queue), and a maintainer will have to write "`bors r+`" again.

- Maintainers can also write "`bors d+`" (short for "`bors delegate+`") to allow the PR author to
  add "`bors r+`". This can be customized with a list of users, see the bors-ng Reference.

- While we still get a nice linear git history like we're used to (see below), PRs squashed and
  merged by bors will no longer display as "Merged" on Github with the purple icon. Instead, bors
  will Close the PR (red icon) and prepend "**[Merged By Bors] -**" to the title. This is a Github
  API limitation, [see the discussion in this thread](https://forum.bors.tech/t/use-a-squash-merge-in-bors/349/19).

- Pushing commits directly to `master` will cause any currently running bors batch to fail and get
  (automatically) retried (see [the notes here](https://github.com/bors-ng/bors-ng/pull/859)). We've
  changed leanprover-community-bot so that it will create its own "update nolints.txt" PRs and also
  add `bors r+` to them.

- Commit messages are taken from the first post of the PR. This is much nicer than mergify /
  Github's default which just combines all commit subject lines into one. We have set things
  up so that the text after the first occurrence of "`---`" is automatically ignored. Contributions
  from other users should be automatically added as [co-authors](https://github.blog/2018-01-29-commit-together-with-co-authors/),
  like how mergify and Github previously did. For PRs with a lot of commits (30+) they
  might be missed; in such cases (or other cases where you want to acknowledge someone who didn't actually
  commit), you can add them with the template `Co-authored-by: Firstname Lastname <email>`.

- Even if the usual "push" build succeeds on a PR branch that is up-to-date with master, `bors r+`
  will not instantly merge it into `master` the way mergify used to; instead, bors will run the CI
  again on the staging branch. [See related issue](https://github.com/bors-ng/bors-ng/issues/852).

- `bors r+` on a PR from an external fork will crash if there are any changes to the Github Actions
  config; [see here](https://github.com/bors-ng/bors-ng/issues/806). PRs that propose such changes
  will have to be merged manually or transferred to the community repo.

  Note that approving PRs from external forks which *don't* propose changes to Github Actions can
  still cause bors to crash if the Github Actions config in `master` is changed before the PR is
  merged. Asking the PR author to merge `master` into their branch should get things working again.

- There is a `bors try` option which can be useful for running CI and getting oleans for PRs from
  external forks.

- Github Actions has a UI bug which shows pushed commits as being built from the `staging` branch.
  However, if we check the actual head refs, the commits are actually pushed to `staging`, then
  `master`, then `staging.tmp*` (and we've set things up so only the first two are run).

## Git history

We're using an option `with_squash_merge = true` which makes the git history look the same as it did
with mergify.

Here is a pretty ASCII diagram ([source](https://github.com/bors-ng/bors-ng/issues/194#issuecomment-361011427)):

**6. squash and rebase, fast-forward merge**

Rough git command equivalent:

```
for pr in pr1 pr2 pr3; do
  git checkout $pr
  git rebase --interactive staging.tmp
  git checkout staging.tmp
  git merge --ff-only $pr
done
```

What it looks like:

```
            --E---F---G  PR1
           /
          /
         /    H---I---J  PR2
        /    /
       /    |
      /     | K---L---M  PR3
     /      |/
A---B---C---D  master

                  |
                  |
                  v

A---B---C---D---[EFG]---[HIJ]---[KLM]  master
```
