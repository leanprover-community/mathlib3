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

## Notations

* `σ a` : `spectrum R a` of `a : A`

## TODO

* Prove the *spectral mapping theorem* for the polynomial functional calculus
-/

universes u v

namespace polynomial

theorem aeval_comm {R : Type*} {A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  (a : A) (p q : polynomial R) : aeval a p * aeval a q = aeval a q * aeval a p :=
by rw [←aeval_mul, mul_comm, aeval_mul]

end polynomial

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

lemma is_unit.sub_of_sub {R : Type u} [ring R] {x y : R} (h : is_unit (x - y)) :
  is_unit (y - x) :=
begin
  have : (-1 : R) * -1 = 1, by simp only [mul_one, mul_neg_eq_neg_mul_symm, neg_neg],
  let u : units R := ⟨-1, -1, this, this⟩,
  have hu : ↑u * (x - y) = y - x,
    by simp only [neg_mul_eq_neg_mul_symm, one_mul, units.coe_mk, neg_sub],
  simpa only [hu] using is_unit.mul u.is_unit h,
end

lemma is_unit.sub_iff {R : Type u} [ring R] {x y : R} :
  is_unit (x - y) ↔ is_unit (y - x) :=
iff.intro (λ h, h.sub_of_sub) (λ h, h.sub_of_sub)

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
/-- This is half of the spectral mapping theorem for polynomials. We prove it separately
because it holds over any field, whereas `spectrum.polynomial_spectrum` needs the field to
be algebraically closed. -/
theorem polynomial_subset (a : A) (p : polynomial 𝕜) :
  (λ k, eval k p) '' (σ a) ⊆ σ (aeval a p) :=
begin
  rintros _ ⟨k, hk, rfl⟩,
  let q := C (eval k p) - p,
  have hroot : is_root q k, by simp only [eval_C, eval_sub, sub_self, is_root.def],
  rw [←mul_div_eq_iff_is_root, ←neg_mul_neg, neg_sub] at hroot,
  have aeval_q_eq : ↑ₐ(eval k p) - aeval a p = aeval a q,
    by simp only [aeval_C, alg_hom.map_sub, sub_left_inj],
  rw [mem_iff, aeval_q_eq, ←hroot, aeval_mul],
  have hcomm := aeval_comm a (C k - X) (- (q / (X - C k))),
  apply mt (is_unit_of_mul_is_unit_left_of_commutes hcomm),
  simpa only [aeval_X, aeval_C, alg_hom.map_sub] using hk,
end

lemma aeval_list_prod_is_unit {R M : Type*} [comm_semiring R] [ring M] [algebra R M] {m : M}
  {s : list (polynomial R)} (h : ∀ p ∈ s, is_unit (aeval m p)) :
  is_unit (aeval m s.prod) :=
begin
  induction s,
  { simp only [aeval_one, is_unit_one, list.prod_nil] },
  { have u_hd := h s_hd (list.mem_cons_self s_hd s_tl),
    have u_tl := s_ih (λ p p_mem, h p (list.mem_of_mem_tail p_mem)),
    rw [list.prod_cons, aeval_mul, is_unit.mul_iff_of_commutes (aeval_comm m _ _)],
    exact ⟨u_hd, u_tl⟩ }
end

/-- This is the *spectral mapping theorem* for polynomials.  Note: the assumption `degree p > 0`
is necessary in case `σ a = ∅`, for then the left-hand side is `∅` and the right-hand side,
assuming `[nontrivial A]`, is `{k}` where `p = polynomial.C k`. -/
theorem polynomial_eq_of_degree_pos [is_alg_closed 𝕜] [nontrivial A] (a : A) (p : polynomial 𝕜)
  (hdeg : degree p > 0) : (λ k, eval k p) '' (σ a) = σ (aeval a p) :=
begin
  /- handle the easy direction via `spectrum.polynomial_subset` -/
  apply set.eq_of_subset_of_subset (polynomial_subset a p),
  intros k hk,
  /- write `C k - p` as a product of linear factors and a constant; show `(C k - p).degree > 0`
  and hence the leading coefficient is nonzero, thus it is a unit in `A` -/
  have hprod := eq_prod_roots_of_splits_id (is_alg_closed.splits (C k - p)),
  replace hdeg : degree (C k - p) > 0,
    by rwa [degree_sub_eq_right_of_degree_lt (lt_of_le_of_lt degree_C_le hdeg)],
  have lead_ne := leading_coeff_ne_zero.mpr (ne_zero_of_degree_gt hdeg),
  have lead_unit := (units.map (↑ₐ).to_monoid_hom (units.mk0 _ lead_ne)).is_unit,
  /- rewrite `k ∈ σ (p a)` to say that `↑ₐk - p a` is not a unit; then by the factorization
  one of the linear factors must not be a unit; note, we must pass from multisets to lists
  because we are ultimately working in `A` which is not necessarily commutative (so `prod` is
  not defined on `multiset A`); nevertheless, we are essentially working in the commutative
  subalgebra of `A` generated by `a`.-/
  have p_a_eq : aeval a (C k - p) = ↑ₐk - aeval a p,
    by simp only [aeval_C, alg_hom.map_sub, sub_left_inj],
  rw [mem_iff, ←p_a_eq, hprod, aeval_mul,
    is_unit.mul_iff_of_commutes (aeval_comm a _ _), aeval_C] at hk,
  replace hk := not_and.mp hk lead_unit,
  rw ←multiset.prod_to_list at hk,
  replace hk := (mt aeval_list_prod_is_unit) hk,
  push_neg at hk,
  rcases hk with ⟨q, q_mem, hq⟩,
  rw multiset.mem_to_list at q_mem,
  /- get the root `r` of `C k - p` for which `a - ↑ₐr` is not a unit; then show `r ∈ σ a` and
  also `p r = k`. -/
  rcases multiset.mem_map.mp q_mem with ⟨r, r_mem, rfl⟩,
  refine ⟨r, _, symm _⟩,
  { simpa only [aeval_X, aeval_C, alg_hom.map_sub, is_unit.sub_iff, mem_iff] using hq },
  { simpa only [mem_roots (ne_zero_of_degree_gt hdeg),
      eval_C, eval_sub, is_root.def, sub_eq_zero] using r_mem }
end

end scalar_field

end spectrum
