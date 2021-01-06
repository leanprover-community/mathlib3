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
(to_real h).injective_iff.mpr $ λ a ha, (norm_eq_zero h_nonsquare a).mp begin
  replace ha := congr_arg (λ x, x * to_real h a.conj) ha,
  have : to_real h (a.norm : ℤ√d) = 0,
  { simpa only [zero_mul, ←ring_hom.map_mul, ←norm_eq_mul_conj] using ha },
  have : (a.norm : ℤ√d) = 0,
  { simpa using this },
  exact_mod_cast this,
end

end zsqrtd
