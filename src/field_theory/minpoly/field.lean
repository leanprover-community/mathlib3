/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
import data.polynomial.field_division
import field_theory.minpoly.basic
import ring_theory.algebraic

/-!
# Minimal polynomials on an algebra over a field

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file specializes the theory of minpoly to the setting of field extensions
and derives some well-known properties, amongst which the fact that minimal polynomials
are irreducible, and uniquely determined by their defining property.

-/

open_locale classical polynomial
open polynomial set function minpoly

namespace minpoly

variables {A B : Type*}
variables (A) [field A]

section ring

variables [ring B] [algebra A B] (x : B)

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `gcd_domain_degree_le_of_ne_zero` which relaxes
the assumptions on `A` in exchange for stronger assumptions on `B`. -/
lemma degree_le_of_ne_zero
  {p : A[X]} (pnz : p ≠ 0) (hp : polynomial.aeval x p = 0) :
  degree (minpoly A x) ≤ degree p :=
calc degree (minpoly A x) ≤ degree (p * C (leading_coeff p)⁻¹) :
    min A x (monic_mul_leading_coeff_inv pnz) (by simp [hp])
  ... = degree p : degree_mul_leading_coeff_inv p pnz

lemma ne_zero_of_finite_field_extension (e : B) [finite_dimensional A B] : minpoly A e ≠ 0 :=
minpoly.ne_zero $ is_integral_of_noetherian (is_noetherian.iff_fg.2 infer_instance) _

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root, then this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.gcd_unique` which relaxes the
assumptions on `A` in exchange for stronger assumptions on `B`. -/
lemma unique {p : A[X]}
  (pmonic : p.monic) (hp : polynomial.aeval x p = 0)
  (pmin : ∀ q : A[X], q.monic → polynomial.aeval x q = 0 → degree p ≤ degree q) :
  p = minpoly A x :=
begin
  have hx : is_integral A x := ⟨p, pmonic, hp⟩,
  symmetry, apply eq_of_sub_eq_zero,
  by_contra hnz,
  have := degree_le_of_ne_zero A x hnz (by simp [hp]),
  contrapose! this,
  apply degree_sub_lt _ (ne_zero hx),
  { rw [(monic hx).leading_coeff, pmonic.leading_coeff] },
  { exact le_antisymm (min A x pmonic hp)
      (pmin (minpoly A x) (monic hx) (aeval A x)) }
end

/-- If an element `x` is a root of a polynomial `p`, then the minimal polynomial of `x` divides `p`.
See also `minpoly.gcd_domain_dvd` which relaxes the assumptions on `A` in exchange for stronger
assumptions on `B`. -/
lemma dvd {p : A[X]} (hp : polynomial.aeval x p = 0) : minpoly A x ∣ p :=
begin
  by_cases hp0 : p = 0,
  { simp only [hp0, dvd_zero] },
  have hx : is_integral A x,
  { rw ← is_algebraic_iff_is_integral, exact ⟨p, hp0, hp⟩ },
  rw ← dvd_iff_mod_by_monic_eq_zero (monic hx),
  by_contra hnz,
  have := degree_le_of_ne_zero A x hnz _,
  { contrapose! this,
    exact degree_mod_by_monic_lt _ (monic hx) },
  { rw ← mod_by_monic_add_div p (monic hx) at hp,
    simpa using hp }
end

lemma dvd_map_of_is_scalar_tower (A K : Type*) {R : Type*} [comm_ring A] [field K] [comm_ring R]
  [algebra A K] [algebra A R] [algebra K R] [is_scalar_tower A K R] (x : R) :
  minpoly K x ∣ (minpoly A x).map (algebra_map A K) :=
by { refine minpoly.dvd K x _, rw [aeval_map_algebra_map, minpoly.aeval] }

lemma dvd_map_of_is_scalar_tower' (R : Type*) {S : Type*} (K L : Type*) [comm_ring R]
  [comm_ring S] [field K] [comm_ring L] [algebra R S] [algebra R K] [algebra S L] [algebra K L]
  [algebra R L] [is_scalar_tower R K L] [is_scalar_tower R S L] (s : S):
  minpoly K (algebra_map S L s) ∣ (map (algebra_map R K) (minpoly R s)) :=
begin
  apply minpoly.dvd K (algebra_map S L s),
  rw [← map_aeval_eq_aeval_map, minpoly.aeval, map_zero],
  rw [← is_scalar_tower.algebra_map_eq, ← is_scalar_tower.algebra_map_eq]
end

/-- If `y` is a conjugate of `x` over a field `K`, then it is a conjugate over a subring `R`. -/
lemma aeval_of_is_scalar_tower (R : Type*) {K T U : Type*} [comm_ring R] [field K] [comm_ring T]
  [algebra R K] [algebra K T] [algebra R T] [is_scalar_tower R K T]
  [comm_semiring U] [algebra K U] [algebra R U] [is_scalar_tower R K U]
  (x : T) (y : U)
  (hy : polynomial.aeval y (minpoly K x) = 0) : polynomial.aeval y (minpoly R x) = 0 :=
aeval_map_algebra_map K y (minpoly R x) ▸ eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebra_map K U)
                                              y (minpoly.dvd_map_of_is_scalar_tower R K x) hy

variables {A x}

theorem eq_of_irreducible_of_monic
  [nontrivial B] {p : A[X]} (hp1 : _root_.irreducible p)
  (hp2 : polynomial.aeval x p = 0) (hp3 : p.monic) : p = minpoly A x :=
let ⟨q, hq⟩ := dvd A x hp2 in
eq_of_monic_of_associated hp3 (monic ⟨p, ⟨hp3, hp2⟩⟩) $
mul_one (minpoly A x) ▸ hq.symm ▸ associated.mul_left _ $
associated_one_iff_is_unit.2 $ (hp1.is_unit_or_is_unit hq).resolve_left $ not_is_unit A x

lemma eq_of_irreducible [nontrivial B] {p : A[X]}
  (hp1 : _root_.irreducible p) (hp2 : polynomial.aeval x p = 0) :
  p * C p.leading_coeff⁻¹ = minpoly A x :=
begin
  have : p.leading_coeff ≠ 0 := leading_coeff_ne_zero.mpr hp1.ne_zero,
  apply eq_of_irreducible_of_monic,
  { exact associated.irreducible ⟨⟨C p.leading_coeff⁻¹, C p.leading_coeff,
      by rwa [←C_mul, inv_mul_cancel, C_1], by rwa [←C_mul, mul_inv_cancel, C_1]⟩, rfl⟩ hp1 },
  { rw [aeval_mul, hp2, zero_mul] },
  { rwa [polynomial.monic, leading_coeff_mul, leading_coeff_C, mul_inv_cancel] },
end

/-- If `y` is the image of `x` in an extension, their minimal polynomials coincide.

We take `h : y = algebra_map L T x` as an argument because `rw h` typically fails
since `is_integral R y` depends on y.
-/
lemma eq_of_algebra_map_eq {K S T : Type*} [field K] [comm_ring S] [comm_ring T]
  [algebra K S] [algebra K T] [algebra S T]
  [is_scalar_tower K S T] (hST : function.injective (algebra_map S T))
  {x : S} {y : T} (hx : is_integral K x) (h : y = algebra_map S T x) :
  minpoly K x = minpoly K y :=
minpoly.unique _ _ (minpoly.monic hx)
  (by rw [h, aeval_algebra_map_apply, minpoly.aeval, ring_hom.map_zero])
  (λ q q_monic root_q, minpoly.min _ _ q_monic
    ((aeval_algebra_map_eq_zero_iff_of_injective hST).mp
      (h ▸ root_q : polynomial.aeval (algebra_map S T x) q = 0)))

lemma add_algebra_map {B : Type*} [comm_ring B] [algebra A B] {x : B}
  (hx : is_integral A x) (a : A) :
  minpoly A (x + (algebra_map A B a)) = (minpoly A x).comp (X - C a) :=
begin
  refine (minpoly.unique _ _ ((minpoly.monic hx).comp_X_sub_C _) _ (λ q qmo hq, _)).symm,
  { simp [aeval_comp] },
  { have : (polynomial.aeval x) (q.comp (X + C a)) = 0 := by simpa [aeval_comp] using hq,
    have H := minpoly.min A x (qmo.comp_X_add_C _) this,
    rw [degree_eq_nat_degree qmo.ne_zero, degree_eq_nat_degree
      ((minpoly.monic hx).comp_X_sub_C _).ne_zero, with_bot.coe_le_coe, nat_degree_comp,
      nat_degree_X_sub_C, mul_one],
    rwa [degree_eq_nat_degree (minpoly.ne_zero hx), degree_eq_nat_degree
      (qmo.comp_X_add_C _).ne_zero, with_bot.coe_le_coe, nat_degree_comp,
      nat_degree_X_add_C, mul_one] at H }
end

lemma sub_algebra_map {B : Type*} [comm_ring B] [algebra A B] {x : B}
  (hx : is_integral A x) (a : A) :
  minpoly A (x - (algebra_map A B a)) = (minpoly A x).comp (X + C a) :=
by simpa [sub_eq_add_neg] using add_algebra_map hx (-a)

section alg_hom_fintype

/-- A technical finiteness result. -/
noncomputable def fintype.subtype_prod {E : Type*} {X : set E} (hX : X.finite) {L : Type*}
  (F : E → multiset L) : fintype (Π x : X, {l : L // l ∈ F x}) :=
let hX := finite.fintype hX in by exactI pi.fintype

variables (F E K : Type*) [field F] [ring E] [comm_ring K] [is_domain K]
  [algebra F E] [algebra F K] [finite_dimensional F E]

/-- Function from Hom_K(E,L) to pi type Π (x : basis), roots of min poly of x -/
-- Marked as `noncomputable!` since this definition takes multiple seconds to compile,
-- and isn't very computable in practice (since neither `finrank` nor `fin_basis` are).
noncomputable! def roots_of_min_poly_pi_type (φ : E →ₐ[F] K)
  (x : range (finite_dimensional.fin_basis F E : _ → E)) :
  {l : K // l ∈ (((minpoly F x.1).map (algebra_map F K)).roots : multiset K)} :=
⟨φ x, by rw [mem_roots_map (minpoly.ne_zero_of_finite_field_extension F x.val),
  subtype.val_eq_coe, ←aeval_def, aeval_alg_hom_apply, minpoly.aeval, map_zero]⟩

lemma aux_inj_roots_of_min_poly : injective (roots_of_min_poly_pi_type F E K) :=
begin
  intros f g h,
  suffices : (f : E →ₗ[F] K) = g,
  { rwa fun_like.ext'_iff at this ⊢ },
  rw funext_iff at h,
  exact linear_map.ext_on (finite_dimensional.fin_basis F E).span_eq
    (λ e he, subtype.ext_iff.mp (h ⟨e, he⟩)),
end

/-- Given field extensions `E/F` and `K/F`, with `E/F` finite, there are finitely many `F`-algebra
  homomorphisms `E →ₐ[K] K`. -/
noncomputable instance alg_hom.fintype : fintype (E →ₐ[F] K) :=
@fintype.of_injective _ _ (fintype.subtype_prod (finite_range (finite_dimensional.fin_basis F E))
  (λ e, ((minpoly F e).map (algebra_map F K)).roots)) _ (aux_inj_roots_of_min_poly F E K)

end alg_hom_fintype

variables (B) [nontrivial B]

/-- If `B/K` is a nontrivial algebra over a field, and `x` is an element of `K`,
then the minimal polynomial of `algebra_map K B x` is `X - C x`. -/
lemma eq_X_sub_C (a : A) : minpoly A (algebra_map A B a) = X - C a :=
eq_X_sub_C_of_algebra_map_inj a (algebra_map A B).injective

lemma eq_X_sub_C' (a : A) : minpoly A a = X - C a := eq_X_sub_C A a

variables (A)

/-- The minimal polynomial of `0` is `X`. -/
@[simp] lemma zero : minpoly A (0:B) = X :=
by simpa only [add_zero, C_0, sub_eq_add_neg, neg_zero, ring_hom.map_zero]
  using eq_X_sub_C B (0:A)

/-- The minimal polynomial of `1` is `X - 1`. -/
@[simp] lemma one : minpoly A (1:B) = X - 1 :=
by simpa only [ring_hom.map_one, C_1, sub_eq_add_neg] using eq_X_sub_C B (1:A)

end ring

section is_domain

variables [ring B] [is_domain B] [algebra A B]
variables {A} {x : B}

/-- A minimal polynomial is prime. -/
lemma prime (hx : is_integral A x) : prime (minpoly A x) :=
begin
  refine ⟨ne_zero hx, not_is_unit A x, _⟩,
  rintros p q ⟨d, h⟩,
  have :    polynomial.aeval x (p*q) = 0 := by simp [h, aeval A x],
  replace : polynomial.aeval x p = 0 ∨ polynomial.aeval x q = 0 := by simpa,
  exact or.imp (dvd A x) (dvd A x) this
end

/-- If `L/K` is a field extension and an element `y` of `K` is a root of the minimal polynomial
of an element `x ∈ L`, then `y` maps to `x` under the field embedding. -/
lemma root {x : B} (hx : is_integral A x) {y : A} (h : is_root (minpoly A x) y) :
  algebra_map A B y = x :=
have key : minpoly A x = X - C y :=
eq_of_monic_of_associated (monic hx) (monic_X_sub_C y) (associated_of_dvd_dvd
  ((irreducible_X_sub_C y).dvd_symm (irreducible hx) (dvd_iff_is_root.2 h))
  (dvd_iff_is_root.2 h)),
by { have := aeval A x, rwa [key, alg_hom.map_sub, aeval_X, aeval_C, sub_eq_zero, eq_comm] at this }

/-- The constant coefficient of the minimal polynomial of `x` is `0` if and only if `x = 0`. -/
@[simp] lemma coeff_zero_eq_zero (hx : is_integral A x) : coeff (minpoly A x) 0 = 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    have zero_root := zero_is_root_of_coeff_zero_eq_zero h,
    rw ← root hx zero_root,
    exact ring_hom.map_zero _ },
  { rintro rfl, simp }
end

/-- The minimal polynomial of a nonzero element has nonzero constant coefficient. -/
lemma coeff_zero_ne_zero (hx : is_integral A x) (h : x ≠ 0) : coeff (minpoly A x) 0 ≠ 0 :=
by { contrapose! h, simpa only [hx, coeff_zero_eq_zero] using h }

end is_domain

end minpoly
