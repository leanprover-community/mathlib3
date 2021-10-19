/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.real.sqrt
import number_theory.zsqrtd.basic

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
lift ⟨real.sqrt d, real.mul_self_sqrt (int.cast_nonneg.mpr h)⟩

lemma to_real_injective {d : ℤ} (h0d : 0 ≤ d) (hd : ∀ n : ℤ, d ≠ n*n) :
  function.injective (to_real h0d) :=
lift_injective _ hd

end zsqrtd
