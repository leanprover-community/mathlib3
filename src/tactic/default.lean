/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison

This file imports many useful tactics ("the kitchen sink").

You can use `import tactic` at the beginning of your file to get everything.
(Although you may want to strip things down when you're polishing.)

Because this file imports some complicated tactics, it has many transitive dependencies
(which of course may not use `import tactic`, and must import selectively).

As (non-exhaustive) examples, these includes things like:
* algebra.group_power
* data.rat
* data.nat.gcd
* data.nat.prime
* data.list.basic
* data.list.perm
* data.set.basic
-/
import
  tactic.basic
  tactic.mk_iff_of_inductive_prop
  tactic.generalize_proofs
  tactic.alias
  tactic.replacer
  tactic.interactive
  tactic.monotonicity.interactive
  tactic.library_search
  tactic.where
  tactic.simpa
  tactic.squeeze
  tactic.finish
  tactic.tauto
  tactic.tidy
  tactic.abel tactic.ring
  tactic.linarith tactic.omega
  tactic.wlog
  tactic.split_ifs
  tactic.ext
  tactic.tfae
  tactic.rcases
