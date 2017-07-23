/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Some useful tactics.
-/
open expr tactic

namespace tactic

/- call (assert n t) with a fresh name n. -/
meta def assert_fresh (t : expr) : tactic expr :=
do n ← get_unused_name `h none,
   assert n t

/- call (assertv n t v) with a fresh name n. -/
meta def assertv_fresh (t : expr) (v : expr) : tactic expr :=
do h ← get_unused_name `h none,
   assertv h t v

-- returns the number of hypotheses reverted
meta def revert_all : tactic ℕ :=
do ctx ← local_context,
   revert_lst ctx

namespace interactive

meta def revert_all := tactic.revert_all

end interactive

end tactic
