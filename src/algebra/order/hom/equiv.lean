/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Jiale Miao
-/
import algebra.order.hom.basic
import analysis.special_functions.pow

/-!
# `equiv` on nonnegative morphisms

This file defines the equivalence of two nonnegative morphisms.

Two nonnegative morphisms `f, g` on `R` are equivalent if there exists a positive constant
`c` such that for all `x ∈ R`, `(f x) ^ c = g x`.
-/

namespace nonneg_hom

/-- Two nonnegative morphisms `f, g` on `R` are equivalent if there exists a positive constant
  `c` such that for all `x ∈ R`, `(f x) ^ c = g x`. -/
def equiv {R F : Type*} [nonneg_hom_class F R ℝ] (f g : F) :=
∃ c : ℝ, 0 < c ∧ (λ x : R, (f x) ^ c) = g

lemma equiv.refl {R F : Type*} [nonneg_hom_class F R ℝ] (f : F) :
  equiv f f := by refine ⟨1, by linarith, by simp only [real.rpow_one]⟩

lemma equiv.symm {R F : Type*} [nonneg_hom_class F R ℝ] {f g : F} (hfg : equiv f g) :
  equiv g f :=
begin
  obtain ⟨c, hc, hfg⟩ := hfg,
  refine ⟨c⁻¹, inv_pos.mpr hc, funext $ λ x, _⟩,
  rw [← hfg, ← real.rpow_mul (map_nonneg f x), mul_inv_cancel hc.ne', real.rpow_one],
end

lemma equiv.trans {R F : Type*} [nonneg_hom_class F R ℝ] (f g k : F)
  (hfg : equiv f g) (hgk : equiv g k) : equiv f k :=
begin
  rcases hfg with ⟨c, hfg1, hfg2⟩,
  rcases hgk with ⟨d, hgk1, hgk2⟩,
  refine ⟨c * d, by simp only [hfg1, hgk1, zero_lt_mul_right], _⟩,
  rw [← hgk2, ← hfg2],
  ext,
  exact real.rpow_mul (map_nonneg f x) c d,
end

end nonneg_hom
