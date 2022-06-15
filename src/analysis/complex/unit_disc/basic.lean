/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.complex.basic
import analysis.normed.field.unit_ball

/-!
-/
open set function

namespace complex

@[derive [comm_semigroup, λ α, has_coe α ℂ]]
def unit_disc : Type := metric.ball (0 : ℂ) 1

localized "notation `𝔻` := complex.unit_disc" in unit_disc

namespace unit_disc

lemma coe_injective : injective (coe : 𝔻 → ℂ) := subtype.coe_injective

lemma abs_lt_one (z : 𝔻) : abs (z : ℂ) < 1 := mem_ball_zero_iff.1 z.2

def mk (z : ℂ) (hz : abs z < 1) : 𝔻 := ⟨z, mem_ball_zero_iff.2 hz⟩

@[simp] lemma coe_mk (z : ℂ) (hz : abs z < 1) : (mk z hz : ℂ) = z := rfl

@[simp] lemma mk_coe (z : 𝔻) (hz : abs (z : ℂ) < 1 := z.abs_lt_one) :
  mk z hz = z :=
subtype.eta _ _

def re (z : 𝔻) : ℝ := re z

def im (z : 𝔻) : ℝ := im z



end unit_disc

end complex
