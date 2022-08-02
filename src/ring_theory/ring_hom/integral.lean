/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.local_properties
import ring_theory.localization.integral

/-!

# The meta properties of integral ring homomorphisms.

-/

namespace ring_hom

open_locale tensor_product

open tensor_product algebra.tensor_product

lemma is_integral_stable_under_composition :
  stable_under_composition (λ R S _ _ f, by exactI f.is_integral) :=
by { introv R hf hg, exactI ring_hom.is_integral_trans _ _ hf hg }

lemma is_integral_respects_iso :
  respects_iso (λ R S _ _ f, by exactI f.is_integral) :=
begin
  apply is_integral_stable_under_composition.respects_iso,
  introv x,
  resetI,
  rw ← e.apply_symm_apply x,
  apply ring_hom.is_integral_map
end

lemma is_integral_stable_under_base_change :
  stable_under_base_change (λ R S _ _ f, by exactI f.is_integral) :=
begin
  classical,
  introv R h x,
  resetI,
  apply tensor_product.induction_on x,
  { apply is_integral_zero },
  { intros x y,
    obtain ⟨p, hp, hp'⟩ := h y,
    refine ⟨(p.map (algebra_map R S)).scale_roots x, _, _⟩,
    { rw polynomial.monic_scale_roots_iff, exact hp.map _ },
    convert @polynomial.scale_roots_eval₂_mul (S ⊗[R] T) S _ _ _ include_left.to_ring_hom
      (1 ⊗ₜ y) x using 2,
    { simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, include_left_apply,
        tmul_mul_tmul, _root_.mul_one, _root_.one_mul] },
    convert (mul_zero _).symm,
    rw [polynomial.eval₂_map, include_left_comp_algebra_map, ← polynomial.eval₂_map],
    convert polynomial.eval₂_at_apply include_right.to_ring_hom y,
    rw [polynomial.eval_map, hp', map_zero] },
  { intros x y hx hy,
    exact is_integral_add _ hx hy }
end

end ring_hom
