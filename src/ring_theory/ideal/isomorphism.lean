/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
/-
import ring_theory.ideal.operations

/-!
# Isomorphism theorems for ideals.

* Noether's third isomorphism theorem for ideals is `ideal.quotient_quotient_equiv_quotient`.

-/

universes u v

variables {R : Type*} [ring R]

/-! The third isomorphism theorem for ideals. -/
namespace ideal

variables (I J : ideal R) (h : I ≤ J)

/-- The map from the third isomorphism theorem for ideals: `(R / I) / (J / I) → R / J`. -/
def quotient_quotient_equiv_quotient_aux :
  (R ⧸ I) ⧸ (J.map (ideal.quotient.mk I)) →ₗ[R] R ⧸ J :=
quotient.lift _ (ideal.quotient.map S T ring_hom.id h)
  (by { rintro _ ⟨x, hx, rfl⟩, rw [linear_map.mem_ker, mkq_apply, mapq_apply],
        exact (quotient.mk_eq_zero _).mpr hx })

@[simp] lemma quotient_quotient_equiv_quotient_aux_mk (x : M ⧸ S) :
  quotient_quotient_equiv_quotient_aux S T h (quotient.mk x) = mapq S T linear_map.id h x :=
liftq_apply _ _ _

@[simp] lemma quotient_quotient_equiv_quotient_aux_mk_mk (x : M) :
  quotient_quotient_equiv_quotient_aux S T h (quotient.mk (quotient.mk x)) = quotient.mk x :=
by rw [quotient_quotient_equiv_quotient_aux_mk, mapq_apply, linear_map.id_apply]

/-- **Noether's third isomorphism theorem** for modules: `(M / S) / (T / S) ≃ M / T`. -/
def quotient_quotient_equiv_quotient :
  ((M ⧸ S) ⧸ (T.map S.mkq)) ≃ₗ[R] M ⧸ T :=
{ to_fun := quotient_quotient_equiv_quotient_aux S T h,
  inv_fun := mapq _ _ (mkq S) (le_comap_map _ _),
  left_inv := λ x, quotient.induction_on' x $ λ x, quotient.induction_on' x $ λ x, by simp,
  right_inv := λ x, quotient.induction_on' x $ λ x, by simp,
  .. quotient_quotient_equiv_quotient_aux S T h }

end submodule

 -/
