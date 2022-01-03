/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import tactic.noncomm_ring
import field_theory.is_alg_closed.basic
/-!
# Spectrum of an element in an algebra
This file develops the basic theory of the spectrum of an element of an algebra.
This theory will serve as the foundation for spectral theory in Banach algebras.

## Main definitions

* `resolvent_set a : set R`: the resolvent set of an element `a : A` where
  `A` is an  `R`-algebra.
* `spectrum a : set R`: the spectrum of an element `a : A` where
  `A` is an  `R`-algebra.
* `resolvent : R → A`: the resolvent function is `λ r, ring.inverse (↑ₐr - a)`, and hence
  when `r ∈ resolvent R A`, it is actually the inverse of the unit `(↑ₐr - a)`.

## Main statements

* `spectrum.unit_smul_eq_smul` and `spectrum.smul_eq_smul`: units in the scalar ring commute
  (multiplication) with the spectrum, and over a field even `0` commutes with the spectrum.
* `spectrum.left_add_coset_eq`: elements of the scalar ring commute (addition) with the spectrum.
* `spectrum.unit_mem_mul_iff_mem_swap_mul` and `spectrum.preimage_units_mul_eq_swap_mul`: the
  units (of `R`) in `σ (a*b)` coincide with those in `σ (b*a)`.
* `spectrum.scalar_eq`: in a nontrivial algebra over a field, the spectrum of a scalar is
  a singleton.
* `spectrum.subset_polynomial_aeval`, `spectrum.map_polynomial_aeval_of_degree_pos`,
  `spectrum.map_polynomial_aeval_of_nonempty`: variations on the spectral mapping theorem.

## Notations

* `σ a` : `spectrum R a` of `a : A`
-/

universes u v


section defs

variables (R : Type u) {A : Type v}
variables [comm_semiring R] [ring A] [algebra R A]

-- definition and basic properties

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent set* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
algebra `A`.  -/
def resolvent_set (a : A) : set R :=
{ r : R | is_unit (algebra_map R A r - a) }


/-- Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is not a unit of the
algebra `A`.

The spectrum is simply the complement of the resolvent set.  -/
def spectrum (a : A) : set R :=
(resolvent_set R a)ᶜ

variable {R}
/-- Given an `a : A` where `A` is an `R`-algebra, the *resolvent* is
    a map `R → A` which sends `r : R` to `(algebra_map R A r - a)⁻¹` when
    `r ∈ resolvent R A` and `0` when `r ∈ spectrum R A`. -/
noncomputable def resolvent (a : A) (r : R) : A :=
ring.inverse (algebra_map R A r - a)


end defs


-- products of scalar units and algebra units


lemma is_unit.smul_sub_iff_sub_inv_smul {R : Type u} {A : Type v}
  [comm_ring R] [ring A] [algebra R A] {r : units R} {a : A} :
  is_unit (r • 1 - a) ↔ is_unit (1 - r⁻¹ • a) :=
begin
  have a_eq : a = r•r⁻¹•a, by simp,
  nth_rewrite 0 a_eq,
  rw [←smul_sub,is_unit_smul_iff],
end

namespace spectrum

section scalar_ring

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] [algebra R A]

local notation `σ` := spectrum R
local notation `↑ₐ` := algebra_map R A

lemma mem_iff {r : R} {a : A} :
  r ∈ σ a ↔ ¬ is_unit (↑ₐr - a) :=
iff.rfl

lemma not_mem_iff {r : R} {a : A} :
  r ∉ σ a ↔ is_unit (↑ₐr - a) :=
by { apply not_iff_not.mp, simp [set.not_not_mem, mem_iff] }

lemma mem_resolvent_set_of_left_right_inverse {r : R} {a b c : A}
  (h₁ : (↑ₐr - a) * b = 1) (h₂ : c * (↑ₐr - a) = 1) :
  r ∈ resolvent_set R a :=
units.is_unit ⟨↑ₐr - a, b, h₁, by rwa ←left_inv_eq_right_inv h₂ h₁⟩

lemma mem_resolvent_set_iff {r : R} {a : A} :
  r ∈ resolvent_set R a ↔ is_unit (↑ₐr - a) :=
iff.rfl

lemma resolvent_eq {a : A} {r : R} (h : r ∈ resolvent_set R a) :
  resolvent a r = ↑h.unit⁻¹ :=
ring.inverse_unit h.unit

lemma add_mem_iff {a : A} {r s : R} :
  r ∈ σ a ↔ r + s ∈ σ (↑ₐs + a) :=
begin
  apply not_iff_not.mpr,
  simp only [mem_resolvent_set_iff],
  have h_eq : ↑ₐ(r + s) - (↑ₐs + a) = ↑ₐr - a,
    { simp, noncomm_ring },
  rw h_eq,
end

lemma smul_mem_smul_iff {a : A} {s : R} {r : units R} :
  r • s ∈ σ (r • a) ↔ s ∈ σ a :=
begin
  apply not_iff_not.mpr,
  simp only [mem_resolvent_set_iff, algebra.algebra_map_eq_smul_one],
  have h_eq : (r • s) • (1 : A) = r • s • 1, by simp,
  rw [h_eq, ←smul_sub, is_unit_smul_iff],
end

open_locale pointwise

theorem unit_smul_eq_smul (a : A) (r : units R) :
  σ (r • a) = r • σ a :=
begin
  ext,
  have x_eq : x = r • r⁻¹ • x, by simp,
  nth_rewrite 0 x_eq,
  rw smul_mem_smul_iff,
  split,
    { exact λ h, ⟨r⁻¹ • x, ⟨h, by simp⟩⟩},
    { rintros ⟨_, _, x'_eq⟩, simpa [←x'_eq],}
end

theorem left_add_coset_eq (a : A) (r : R) :
  left_add_coset r (σ a) = σ (↑ₐr + a) :=
by { ext, rw [mem_left_add_coset_iff, neg_add_eq_sub, add_mem_iff],
     nth_rewrite 1 ←sub_add_cancel x r, }

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : units R`
theorem unit_mem_mul_iff_mem_swap_mul {a b : A} {r : units R} :
  ↑r ∈ σ (a * b) ↔ ↑r ∈ σ (b * a) :=
begin
  apply not_iff_not.mpr,
  simp only [mem_resolvent_set_iff, algebra.algebra_map_eq_smul_one],
  have coe_smul_eq : ↑r • 1 = r • (1 : A), from rfl,
  rw coe_smul_eq,
  simp only [is_unit.smul_sub_iff_sub_inv_smul],
  have right_inv_of_swap : ∀ {x y z : A} (h : (1 - x * y) * z = 1),
    (1 - y * x) * (1 + y * z * x) = 1, from λ x y z h,
      calc (1 - y * x) * (1 + y * z * x) = 1 - y * x + y * ((1 - x * y) * z) * x : by noncomm_ring
      ...                                = 1                                     : by simp [h],
  have left_inv_of_swap : ∀ {x y z : A} (h : z * (1 - x * y) = 1),
    (1 + y * z * x) * (1 - y * x) = 1, from λ x y z h,
      calc (1 + y * z * x) * (1 - y * x) = 1 - y * x + y * (z * (1 - x * y)) * x : by noncomm_ring
      ...                                = 1                                     : by simp [h],
  have is_unit_one_sub_mul_of_swap : ∀ {x y : A} (h : is_unit (1 - x * y)),
    is_unit (1 - y * x), from λ x y h, by
      { let h₁ := right_inv_of_swap h.unit.val_inv,
        let h₂ := left_inv_of_swap h.unit.inv_val,
        exact ⟨⟨1 - y * x, 1 + y * h.unit.inv * x, h₁, h₂⟩, rfl⟩, },
  have is_unit_one_sub_mul_iff_swap : ∀ {x y : A},
    is_unit (1 - x * y) ↔ is_unit (1 - y * x), by
      { intros, split, repeat {apply is_unit_one_sub_mul_of_swap}, },
  rw [←smul_mul_assoc, ←mul_smul_comm r⁻¹ b a, is_unit_one_sub_mul_iff_swap],
end

theorem preimage_units_mul_eq_swap_mul {a b : A} :
  (coe : units R → R) ⁻¹' σ (a * b) = coe ⁻¹'  σ (b * a) :=
by { ext, exact unit_mem_mul_iff_mem_swap_mul, }

end scalar_ring

section scalar_field

variables {𝕜 : Type u} {A : Type v}
variables [field 𝕜] [ring A] [algebra 𝕜 A]

local notation `σ` := spectrum 𝕜
local notation `↑ₐ` := algebra_map 𝕜 A

/-- Without the assumption `nontrivial A`, then `0 : A` would be invertible. -/
@[simp] lemma zero_eq [nontrivial A] : σ (0 : A) = {0} :=
begin
  refine set.subset.antisymm _ (by simp [algebra.algebra_map_eq_smul_one, mem_iff]),
  rw [spectrum, set.compl_subset_comm],
  intros k hk,
  rw set.mem_compl_singleton_iff at hk,
  have : is_unit (units.mk0 k hk • (1 : A)) := is_unit.smul (units.mk0 k hk) is_unit_one,
  simpa [mem_resolvent_set_iff, algebra.algebra_map_eq_smul_one]
end

@[simp] theorem scalar_eq [nontrivial A] (k : 𝕜) : σ (↑ₐk) = {k} :=
begin
  have coset_eq : left_add_coset k {0} = {k}, by
    { ext, split,
      { intro hx, simp [left_add_coset] at hx, exact hx, },
      { intro hx, simp at hx, exact ⟨0, ⟨set.mem_singleton 0, by simp [hx]⟩⟩, }, },
  calc σ (↑ₐk) = σ (↑ₐk + 0)                  : by simp
    ...        = left_add_coset k (σ (0 : A)) : by rw ←left_add_coset_eq
    ...        = left_add_coset k {0}         : by rw zero_eq
    ...        = {k}                          : coset_eq,
end

@[simp] lemma one_eq [nontrivial A] : σ (1 : A) = {1} :=
calc σ (1 : A) = σ (↑ₐ1) : by simp [algebra.algebra_map_eq_smul_one]
  ...          = {1}     : scalar_eq 1

open_locale pointwise

/-- the assumption `(σ a).nonempty` is necessary and cannot be removed without
    further conditions on the algebra `A` and scalar field `𝕜`. -/
theorem smul_eq_smul [nontrivial A] (k : 𝕜) (a : A) (ha : (σ a).nonempty) :
  σ (k • a) = k • (σ a) :=
begin
  rcases eq_or_ne k 0 with rfl | h,
  { simpa [ha, zero_smul_set] },
  { exact unit_smul_eq_smul a (units.mk0 k h) },
end

theorem nonzero_mul_eq_swap_mul (a b : A) : σ (a * b) \ {0} = σ (b * a) \ {0} :=
begin
  suffices h : ∀ (x y : A), σ (x * y) \ {0} ⊆ σ (y * x) \ {0},
  { exact set.eq_of_subset_of_subset (h a b) (h b a) },
  { rintros _ _ k ⟨k_mem, k_neq⟩,
    change k with ↑(units.mk0 k k_neq) at k_mem,
    exact ⟨unit_mem_mul_iff_mem_swap_mul.mp k_mem, k_neq⟩ },
end

open polynomial
/-- Half of the spectral mapping theorem for polynomials. We prove it separately
because it holds over any field, whereas `spectrum.map_polynomial_aeval_of_degree_pos` and
`spectrum.map_polynomial_aeval_of_nonempty` need the field to be algebraically closed. -/
theorem subset_polynomial_aeval (a : A) (p : polynomial 𝕜) :
  (λ k, eval k p) '' (σ a) ⊆ σ (aeval a p) :=
begin
  rintros _ ⟨k, hk, rfl⟩,
  let q := C (eval k p) - p,
  have hroot : is_root q k, by simp only [eval_C, eval_sub, sub_self, is_root.def],
  rw [←mul_div_eq_iff_is_root, ←neg_mul_neg, neg_sub] at hroot,
  have aeval_q_eq : ↑ₐ(eval k p) - aeval a p = aeval a q,
    by simp only [aeval_C, alg_hom.map_sub, sub_left_inj],
  rw [mem_iff, aeval_q_eq, ←hroot, aeval_mul],
  have hcomm := (commute.all (C k - X) (- (q / (X - C k)))).map (aeval a),
  apply mt (λ h, (hcomm.is_unit_mul_iff.mp h).1),
  simpa only [aeval_X, aeval_C, alg_hom.map_sub] using hk,
end

lemma exists_mem_of_not_is_unit_aeval_prod {p : polynomial 𝕜} {a : A} (hp : p ≠ 0)
  (h : ¬is_unit (aeval a (multiset.map (λ (x : 𝕜), X - C x) p.roots).prod)) :
  ∃ k : 𝕜, k ∈ σ a ∧ eval k p = 0 :=
begin
  rw [←multiset.prod_to_list, alg_hom.map_list_prod] at h,
  replace h := mt list.prod_is_unit h,
  simp only [not_forall, exists_prop, aeval_C, multiset.mem_to_list,
    list.mem_map, aeval_X, exists_exists_and_eq_and, multiset.mem_map, alg_hom.map_sub] at h,
  rcases h with ⟨r, r_mem, r_nu⟩,
  exact ⟨r, by rwa [mem_iff, ←is_unit.sub_iff], by rwa [←is_root.def, ←mem_roots hp]⟩
end

/-- The *spectral mapping theorem* for polynomials.  Note: the assumption `degree p > 0`
is necessary in case `σ a = ∅`, for then the left-hand side is `∅` and the right-hand side,
assuming `[nontrivial A]`, is `{k}` where `p = polynomial.C k`. -/
theorem map_polynomial_aeval_of_degree_pos [is_alg_closed 𝕜] (a : A) (p : polynomial 𝕜)
  (hdeg : 0 < degree p) : σ (aeval a p) = (λ k, eval k p) '' (σ a) :=
begin
  /- handle the easy direction via `spectrum.subset_polynomial_aeval` -/
  refine set.eq_of_subset_of_subset (λ k hk, _) (subset_polynomial_aeval a p),
  /- write `C k - p` product of linear factors and a constant; show `C k - p ≠ 0`. -/
  have hprod := eq_prod_roots_of_splits_id (is_alg_closed.splits (C k - p)),
  have h_ne : C k - p ≠ 0, from ne_zero_of_degree_gt
    (by rwa [degree_sub_eq_right_of_degree_lt (lt_of_le_of_lt degree_C_le hdeg)]),
  have lead_ne := leading_coeff_ne_zero.mpr h_ne,
  have lead_unit := (units.map (↑ₐ).to_monoid_hom (units.mk0 _ lead_ne)).is_unit,
  /- leading coefficient is a unit so product of linear factors is not a unit;
  apply `exists_mem_of_not_is_unit_aeval_prod`. -/
  have p_a_eq : aeval a (C k - p) = ↑ₐk - aeval a p,
    by simp only [aeval_C, alg_hom.map_sub, sub_left_inj],
  rw [mem_iff, ←p_a_eq, hprod, aeval_mul,
    ((commute.all _ _).map (aeval a)).is_unit_mul_iff, aeval_C] at hk,
  replace hk := exists_mem_of_not_is_unit_aeval_prod h_ne (not_and.mp hk lead_unit),
  rcases hk with ⟨r, r_mem, r_ev⟩,
  exact ⟨r, r_mem, symm (by simpa [eval_sub, eval_C, sub_eq_zero] using r_ev)⟩,
end

/-- In this version of the spectral mapping theorem, we assume the spectrum
is nonempty instead of assuming the degree of the polynomial is positive. Note: the
assumption `[nontrivial A]` is necessary for the same reason as in `spectrum.zero_eq`. -/
theorem map_polynomial_aeval_of_nonempty [is_alg_closed 𝕜] [nontrivial A] (a : A) (p : polynomial 𝕜)
  (hnon : (σ a).nonempty) : σ (aeval a p) = (λ k, eval k p) '' (σ a) :=
begin
  refine or.elim (le_or_gt (degree p) 0) (λ h, _) (map_polynomial_aeval_of_degree_pos a p),
  { rw eq_C_of_degree_le_zero h,
    simp only [set.image_congr, eval_C, aeval_C, scalar_eq, set.nonempty.image_const hnon] },
end

variable (𝕜)
/--
Every element `a` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `𝕜` has non-empty spectrum. -/
-- We will use this both to show eigenvalues exist, and to prove Schur's lemma.
lemma nonempty_of_is_alg_closed_of_finite_dimensional [is_alg_closed 𝕜]
  [nontrivial A] [I : finite_dimensional 𝕜 A] (a : A) :
  ∃ k : 𝕜, k ∈ σ a :=
begin
  obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := is_integral_of_noetherian (is_noetherian.iff_fg.2 I) a,
  have nu : ¬ is_unit (aeval a p), { rw [←aeval_def] at h_eval_p, rw h_eval_p, simp, },
  rw [eq_prod_roots_of_monic_of_splits_id h_mon (is_alg_closed.splits p)] at nu,
  obtain ⟨k, hk, _⟩ := exists_mem_of_not_is_unit_aeval_prod (monic.ne_zero h_mon) nu,
  exact ⟨k, hk⟩
end

end scalar_field

end spectrum
