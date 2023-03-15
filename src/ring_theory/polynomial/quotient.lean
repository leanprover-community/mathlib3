/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, David Kurniadi Angdinata, Devon Tuma, Riccardo Brasca
-/

import data.polynomial.div
import ring_theory.polynomial.basic
import ring_theory.ideal.quotient_operations

/-!
# Quotients of polynomial rings
-/

open_locale polynomial

namespace polynomial

variables {R : Type*} [comm_ring R]

/-- For a commutative ring $R$, evaluating a polynomial at an element $x \in R$ induces an
isomorphism of $R$-algebras $R[X] / \langle X - x \rangle \cong R$. -/
noncomputable def quotient_span_X_sub_C_alg_equiv (x : R) :
  (R[X] ⧸ ideal.span ({X - C x} : set R[X])) ≃ₐ[R] R :=
(alg_equiv.restrict_scalars R $ ideal.quotient_equiv_alg_of_eq R
  (by exact ker_eval_ring_hom x : ring_hom.ker (aeval x).to_ring_hom = _)).symm.trans $
  ideal.quotient_ker_alg_equiv_of_right_inverse $ λ _, eval_C

@[simp] lemma quotient_span_X_sub_C_alg_equiv_mk (x : R) (p : R[X]) :
  quotient_span_X_sub_C_alg_equiv x (ideal.quotient.mk _ p) = p.eval x :=
rfl

@[simp] lemma quotient_span_X_sub_C_alg_equiv_symm_apply (x : R) (y : R) :
  (quotient_span_X_sub_C_alg_equiv x).symm y = algebra_map R _ y :=
rfl

end polynomial

namespace ideal
noncomputable theory
open polynomial

variables {R : Type*} [comm_ring R]

lemma quotient_map_C_eq_zero {I : ideal R} :
  ∀ a ∈ I, ((quotient.mk (map (C : R →+* R[X]) I : ideal R[X])).comp C) a = 0 :=
begin
  intros a ha,
  rw [ring_hom.comp_apply, quotient.eq_zero_iff_mem],
  exact mem_map_of_mem _ ha,
end

lemma eval₂_C_mk_eq_zero {I : ideal R} :
  ∀ f ∈ (map (C : R →+* R[X]) I : ideal R[X]), eval₂_ring_hom (C.comp (quotient.mk I)) X f = 0 :=
begin
  intros a ha,
  rw ← sum_monomial_eq a,
  dsimp,
  rw eval₂_sum,
  refine finset.sum_eq_zero (λ n hn, _),
  dsimp,
  rw eval₂_monomial (C.comp (quotient.mk I)) X,
  refine mul_eq_zero_of_left (polynomial.ext (λ m, _)) (X ^ n),
  erw coeff_C,
  by_cases h : m = 0,
  { simpa [h] using quotient.eq_zero_iff_mem.2 ((mem_map_C_iff.1 ha) n) },
  { simp [h] }
end

/-- If `I` is an ideal of `R`, then the ring polynomials over the quotient ring `I.quotient` is
isomorphic to the quotient of `R[X]` by the ideal `map C I`,
where `map C I` contains exactly the polynomials whose coefficients all lie in `I` -/
def polynomial_quotient_equiv_quotient_polynomial (I : ideal R) :
  (R ⧸ I)[X] ≃+* R[X] ⧸ (map C I : ideal R[X]) :=
{ to_fun := eval₂_ring_hom
    (quotient.lift I ((quotient.mk (map C I : ideal R[X])).comp C) quotient_map_C_eq_zero)
    ((quotient.mk (map C I : ideal R[X]) X)),
  inv_fun := quotient.lift (map C I : ideal R[X])
    (eval₂_ring_hom (C.comp (quotient.mk I)) X) eval₂_C_mk_eq_zero,
  map_mul' := λ f g, by simp only [coe_eval₂_ring_hom, eval₂_mul],
  map_add' := λ f g, by simp only [eval₂_add, coe_eval₂_ring_hom],
  left_inv := begin
    intro f,
    apply polynomial.induction_on' f,
    { intros p q hp hq,
      simp only [coe_eval₂_ring_hom] at hp,
      simp only [coe_eval₂_ring_hom] at hq,
      simp only [coe_eval₂_ring_hom, hp, hq, ring_hom.map_add] },
    { rintros n ⟨x⟩,
      simp only [← smul_X_eq_monomial, C_mul', quotient.lift_mk, submodule.quotient.quot_mk_eq_mk,
        quotient.mk_eq_mk, eval₂_X_pow, eval₂_smul, coe_eval₂_ring_hom, ring_hom.map_pow,
        eval₂_C, ring_hom.coe_comp, ring_hom.map_mul, eval₂_X] }
  end,
  right_inv := begin
    rintro ⟨f⟩,
    apply polynomial.induction_on' f,
    { simp_intros p q hp hq,
      rw [hp, hq] },
    { intros n a,
      simp only [← smul_X_eq_monomial, ← C_mul' a (X ^ n), quotient.lift_mk,
        submodule.quotient.quot_mk_eq_mk, quotient.mk_eq_mk, eval₂_X_pow,
        eval₂_smul, coe_eval₂_ring_hom, ring_hom.map_pow, eval₂_C, ring_hom.coe_comp,
        ring_hom.map_mul, eval₂_X] },
  end, }

@[simp]
lemma polynomial_quotient_equiv_quotient_polynomial_symm_mk (I : ideal R) (f : R[X]) :
  I.polynomial_quotient_equiv_quotient_polynomial.symm (quotient.mk _ f) = f.map (quotient.mk I) :=
by rw [polynomial_quotient_equiv_quotient_polynomial, ring_equiv.symm_mk, ring_equiv.coe_mk,
  ideal.quotient.lift_mk, coe_eval₂_ring_hom, eval₂_eq_eval_map, ←polynomial.map_map,
  ←eval₂_eq_eval_map, polynomial.eval₂_C_X]

@[simp]
lemma polynomial_quotient_equiv_quotient_polynomial_map_mk (I : ideal R) (f : R[X]) :
  I.polynomial_quotient_equiv_quotient_polynomial (f.map I^.quotient.mk) = quotient.mk _ f :=
begin
  apply (polynomial_quotient_equiv_quotient_polynomial I).symm.injective,
  rw [ring_equiv.symm_apply_apply, polynomial_quotient_equiv_quotient_polynomial_symm_mk],
end

/-- If `P` is a prime ideal of `R`, then `R[x]/(P)` is an integral domain. -/
lemma is_domain_map_C_quotient {P : ideal R} (H : is_prime P) :
  is_domain (R[X] ⧸ (map (C : R →+* R[X]) P : ideal R[X])) :=
ring_equiv.is_domain (polynomial (R ⧸ P))
  (polynomial_quotient_equiv_quotient_polynomial P).symm

/-- Given any ring `R` and an ideal `I` of `R[X]`, we get a map `R → R[x] → R[x]/I`.
  If we let `R` be the image of `R` in `R[x]/I` then we also have a map `R[x] → R'[x]`.
  In particular we can map `I` across this map, to get `I'` and a new map `R' → R'[x] → R'[x]/I`.
  This theorem shows `I'` will not contain any non-zero constant polynomials
  -/
lemma eq_zero_of_polynomial_mem_map_range (I : ideal R[X])
  (x : ((quotient.mk I).comp C).range)
  (hx : C x ∈ (I.map (polynomial.map_ring_hom ((quotient.mk I).comp C).range_restrict))) :
  x = 0 :=
begin
  let i := ((quotient.mk I).comp C).range_restrict,
  have hi' : (polynomial.map_ring_hom i).ker ≤ I,
  { refine λ f hf, polynomial_mem_ideal_of_coeff_mem_ideal I f (λ n, _),
    rw [mem_comap, ← quotient.eq_zero_iff_mem, ← ring_hom.comp_apply],
    rw [ring_hom.mem_ker, coe_map_ring_hom] at hf,
    replace hf := congr_arg (λ (f : polynomial _), f.coeff n) hf,
    simp only [coeff_map, coeff_zero] at hf,
    rwa [subtype.ext_iff, ring_hom.coe_range_restrict] at hf },
  obtain ⟨x, hx'⟩ := x,
  obtain ⟨y, rfl⟩ := (ring_hom.mem_range).1 hx',
  refine subtype.eq _,
  simp only [ring_hom.comp_apply, quotient.eq_zero_iff_mem, zero_mem_class.coe_zero,
    subtype.val_eq_coe],
  suffices : C (i y) ∈ (I.map (polynomial.map_ring_hom i)),
  { obtain ⟨f, hf⟩ := mem_image_of_mem_map_of_surjective (polynomial.map_ring_hom i)
      (polynomial.map_surjective _ (((quotient.mk I).comp C).range_restrict_surjective)) this,
    refine sub_add_cancel (C y) f ▸ I.add_mem (hi' _ : (C y - f) ∈ I) hf.1,
    rw [ring_hom.mem_ker, ring_hom.map_sub, hf.2, sub_eq_zero, coe_map_ring_hom, map_C] },
  exact hx,
end

end ideal

namespace mv_polynomial

variables {R : Type*} {σ : Type*} [comm_ring R] {r : R}

lemma quotient_map_C_eq_zero {I : ideal R} {i : R} (hi : i ∈ I) :
  (ideal.quotient.mk (ideal.map (C : R →+* mv_polynomial σ R) I :
  ideal (mv_polynomial σ R))).comp C i = 0 :=
begin
  simp only [function.comp_app, ring_hom.coe_comp, ideal.quotient.eq_zero_iff_mem],
  exact ideal.mem_map_of_mem _ hi
end

lemma eval₂_C_mk_eq_zero {I : ideal R} {a : mv_polynomial σ R}
  (ha : a ∈ (ideal.map (C : R →+* mv_polynomial σ R) I : ideal (mv_polynomial σ R))) :
  eval₂_hom (C.comp (ideal.quotient.mk I)) X a = 0 :=
begin
  rw as_sum a,
  rw [coe_eval₂_hom, eval₂_sum],
  refine finset.sum_eq_zero (λ n hn, _),
  simp only [eval₂_monomial, function.comp_app, ring_hom.coe_comp],
  refine mul_eq_zero_of_left _ _,
  suffices : coeff n a ∈ I,
  { rw [← @ideal.mk_ker R _ I, ring_hom.mem_ker] at this,
    simp only [this, C_0] },
  exact mem_map_C_iff.1 ha n
end

/-- If `I` is an ideal of `R`, then the ring `mv_polynomial σ I.quotient` is isomorphic as an
`R`-algebra to the quotient of `mv_polynomial σ R` by the ideal generated by `I`. -/
def quotient_equiv_quotient_mv_polynomial (I : ideal R) :
  mv_polynomial σ (R ⧸ I) ≃ₐ[R]
    mv_polynomial σ R ⧸ (ideal.map C I : ideal (mv_polynomial σ R)) :=
{ to_fun := eval₂_hom (ideal.quotient.lift I ((ideal.quotient.mk (ideal.map C I : ideal
    (mv_polynomial σ R))).comp C) (λ i hi, quotient_map_C_eq_zero hi))
    (λ i, ideal.quotient.mk (ideal.map C I : ideal (mv_polynomial σ R)) (X i)),
  inv_fun := ideal.quotient.lift (ideal.map C I : ideal (mv_polynomial σ R))
    (eval₂_hom (C.comp (ideal.quotient.mk I)) X) (λ a ha, eval₂_C_mk_eq_zero ha),
  map_mul' := ring_hom.map_mul _,
  map_add' := ring_hom.map_add _,
  left_inv := begin
    intro f,
    apply induction_on f,
    { rintro ⟨r⟩,
      rw [coe_eval₂_hom, eval₂_C],
      simp only [eval₂_hom_eq_bind₂, submodule.quotient.quot_mk_eq_mk, ideal.quotient.lift_mk,
        ideal.quotient.mk_eq_mk, bind₂_C_right, ring_hom.coe_comp] },
    { simp_intros p q hp hq only [ring_hom.map_add, mv_polynomial.coe_eval₂_hom, coe_eval₂_hom,
        mv_polynomial.eval₂_add, mv_polynomial.eval₂_hom_eq_bind₂, eval₂_hom_eq_bind₂],
      rw [hp, hq] },
    { simp_intros p i hp only [eval₂_hom_eq_bind₂, coe_eval₂_hom],
      simp only [hp, eval₂_hom_eq_bind₂, coe_eval₂_hom, ideal.quotient.lift_mk, bind₂_X_right,
        eval₂_mul, ring_hom.map_mul, eval₂_X] }
  end,
  right_inv := begin
    rintro ⟨f⟩,
    apply induction_on f,
    { intros r,
      simp only [submodule.quotient.quot_mk_eq_mk, ideal.quotient.lift_mk, ideal.quotient.mk_eq_mk,
        ring_hom.coe_comp, eval₂_hom_C] },
    { simp_intros p q hp hq only [eval₂_hom_eq_bind₂, submodule.quotient.quot_mk_eq_mk, eval₂_add,
        ring_hom.map_add, coe_eval₂_hom, ideal.quotient.lift_mk, ideal.quotient.mk_eq_mk],
      rw [hp, hq] },
    { simp_intros p i hp only [eval₂_hom_eq_bind₂, submodule.quotient.quot_mk_eq_mk, coe_eval₂_hom,
        ideal.quotient.lift_mk, ideal.quotient.mk_eq_mk, bind₂_X_right, eval₂_mul, ring_hom.map_mul,
        eval₂_X],
      simp only [hp] }
  end,
  commutes' := λ r, eval₂_hom_C _ _ (ideal.quotient.mk I r) }

end mv_polynomial
