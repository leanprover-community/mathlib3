/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import algebra.group.pi

/-!
Test if `simp` can use a lemma about `pi.has_one` to simplify `1` coming from `pi.group`
-/

variables {I : Type*} {f : Π i : I, Type*}

namespace test

def eval_default [inhabited I] (F : Π i, f i) : f (default I) := F (default I)

@[simp] lemma eval_default_one [inhabited I] [Π i, has_one (f i)] :
  eval_default (1 : Π i, f i) = 1 := rfl

example [inhabited I] [Π i, group (f i)] (F : Π i, f i) : eval_default (F⁻¹ * F) = 1 := by simp

end test
