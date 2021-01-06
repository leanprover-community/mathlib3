/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.real.sqrt
import data.zsqrtd.basic

/-!
# Image of `zsqrtd` in `ℝ`

This file defines `zsqrtd.to_real` and related lemmas.
It is in a separate file to avoid pulling in all of `data.real` into `data.zsqrtd`.
-/

namespace zsqrtd

/-- The image of `zsqrtd` in `ℝ`, using `real.sqrt` which takes the positive root of `d`.

If the negative root is desired, use `to_real h a.conj`. -/
@[simps]
noncomputable def to_real {d : ℤ} (h : 0 ≤ d) : ℤ√d →+* ℝ :=
lift (real.sqrt d) (real.mul_self_sqrt (int.cast_nonneg.mpr h))

lemma to_real_injective {d : ℤ} (h : 0 ≤ d) (h_nonsquare : ∀ n : ℤ, d ≠ n*n) :
  function.injective (to_real h) :=
lift_injective _ _ h_nonsquare ((ring_hom.injective_iff _).mpr $ λ a, by simp)

end zsqrtd
