/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import ring_theory.dedekind_domain.adic_valuation
import topology.algebra.uniform_ring


/-!
# The finite adèle ring of a Dedekind domain
We define the ring of finite adèles of a Dedekind domain `R`.

## Main definitions
- `dedekind_domain.finite_integral_adeles` : product of `adic_completion_integers`, where `v`
  runs over all maximal ideals of `R`.
- `dedekind_domain.prod_adic_completions` : the product of `adic_completion`, where `v` runs over
  all maximal ideals of `R`.
- `dedekind_domain.finite_adele_ring` : The finite adèle ring of `R`, defined as the
  restricted product `Π'_v K_v`.

## Implementation notes
We are only interested on Dedekind domains of Krull dimension 1 (i.e., not fields). If `R` is a
field, its finite adèle ring is just defined to be the trivial ring.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
finite adèle ring, dedekind domain
-/

noncomputable theory
open function set is_dedekind_domain is_dedekind_domain.height_one_spectrum

namespace dedekind_domain

variables (R K : Type*) [comm_ring R] [is_domain R] [is_dedekind_domain R] [field K]
  [algebra R K] [is_fraction_ring R K] (v : height_one_spectrum R)

/-- The product of all `adic_completion_integers`, where `v` runs over the maximal ideals of `R`. -/
@[derive [comm_ring, topological_space, inhabited]]
def finite_integral_adeles : Type* := Π (v : height_one_spectrum R), v.adic_completion_integers K

local notation `R_hat` := finite_integral_adeles

/-- The product of all `adic_completion`, where `v` runs over the maximal ideals of `R`. -/
@[derive [non_unital_non_assoc_ring, topological_space, topological_ring, comm_ring, inhabited]]
def prod_adic_completions := Π (v : height_one_spectrum R), v.adic_completion K

local notation `K_hat` := prod_adic_completions

namespace finite_integral_adeles

noncomputable! instance : has_coe (R_hat R K) (K_hat R K) := { coe := λ x v, x v }

lemma coe_apply (x : R_hat R K) (v : height_one_spectrum R) : (x : K_hat R K) v = ↑(x v) := rfl

/-- The inclusion of `R_hat` in `K_hat` as a homomorphism of additive monoids. -/
@[simps] def coe.add_monoid_hom : add_monoid_hom (R_hat R K) (K_hat R K) :=
{ to_fun    := coe,
  map_zero' := rfl,
  map_add'  := λ x y, by { ext v, simp only [coe_apply, pi.add_apply, subring.coe_add] }}

/-- The inclusion of `R_hat` in `K_hat` as a ring homomorphism. -/
@[simps] def coe.ring_hom : ring_hom (R_hat R K) (K_hat R K)  :=
{ to_fun   := coe,
  map_one' := rfl,
  map_mul' := λ x y, by {ext p, simp only [pi.mul_apply, subring.coe_mul], refl },
  ..coe.add_monoid_hom R K }

end finite_integral_adeles

section algebra_instances

instance : algebra K (K_hat R K) :=
(by apply_instance : algebra K $ Π v : height_one_spectrum R, v.adic_completion K)

instance prod_adic_completions.algebra' : algebra R (K_hat R K) :=
(by apply_instance : algebra R $ Π v : height_one_spectrum R, v.adic_completion K)

instance : is_scalar_tower R K (K_hat R K) :=
(by apply_instance : is_scalar_tower R K $ Π v : height_one_spectrum R, v.adic_completion K)

instance : algebra R (R_hat R K) :=
(by apply_instance : algebra R $ Π v : height_one_spectrum R, v.adic_completion_integers K)

instance prod_adic_completions.algebra_completions : algebra (R_hat R K) (K_hat R K) :=
(finite_integral_adeles.coe.ring_hom R K).to_algebra

instance prod_adic_completions.is_scalar_tower_completions :
  is_scalar_tower R (R_hat R K) (K_hat R K) :=
(by apply_instance : is_scalar_tower R (Π v : height_one_spectrum R, v.adic_completion_integers K) $
  Π v : height_one_spectrum R, v.adic_completion K)

end algebra_instances

namespace finite_integral_adeles

/-- The inclusion of `R_hat` in `K_hat` as an algebra homomorphism. -/
def coe.alg_hom : alg_hom R (R_hat R K) (K_hat R K)  :=
{ to_fun    := coe,
  commutes' := λ r, rfl,
  ..coe.ring_hom R K  }

lemma coe.alg_hom_apply (x : R_hat R K) (v : height_one_spectrum R) :
  (coe.alg_hom R K) x v = x v := rfl

end finite_integral_adeles

/-! ### The finite adèle ring of a Dedekind domain
We define the finite adèle ring of `R` as the restricted product over all maximal ideals `v` of `R`
of `adic_completion` with respect to `adic_completion_integers`. We prove that it is a commutative
ring. TODO: show that it is a topological ring with the restricted product topology. -/

namespace prod_adic_completions

variables {R K}

/-- An element `x : K_hat R K` is a finite adèle if for all but finitely many height one ideals
  `v`, the component `x v` is a `v`-adic integer. -/
def is_finite_adele (x : K_hat R K) :=
∀ᶠ v : height_one_spectrum R in filter.cofinite, x v ∈ v.adic_completion_integers K

namespace is_finite_adele

/-- The sum of two finite adèles is a finite adèle. -/
lemma add {x y : K_hat R K} (hx : x.is_finite_adele) (hy : y.is_finite_adele) :
  (x + y).is_finite_adele :=
begin
  rw [is_finite_adele, filter.eventually_cofinite] at hx hy ⊢,
  have h_subset : {v : height_one_spectrum R | ¬ (x + y) v ∈  (v.adic_completion_integers K)} ⊆
    {v : height_one_spectrum R | ¬ x v ∈ (v.adic_completion_integers K)} ∪
    {v : height_one_spectrum R | ¬ y v ∈ (v.adic_completion_integers K)},
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq],
    rw mem_set_of_eq at hv,
    contrapose! hv,
    rw [mem_adic_completion_integers, mem_adic_completion_integers, ← max_le_iff] at hv,
    rw [mem_adic_completion_integers, pi.add_apply],
    exact le_trans (valued.v.map_add_le_max' (x v) (y v)) hv },
  exact (hx.union hy).subset h_subset,
end

/-- The tuple `(0)_v` is a finite adèle. -/
lemma zero : (0 : K_hat R K).is_finite_adele :=
begin
  rw [is_finite_adele, filter.eventually_cofinite],
  have h_empty : {v : height_one_spectrum R |
    ¬ ((0 : v.adic_completion K) ∈ v.adic_completion_integers K)} = ∅,
  { ext v, rw [mem_empty_iff_false, iff_false], intro hv,
    rw mem_set_of_eq at hv, apply hv, rw mem_adic_completion_integers,
    have h_zero : (valued.v (0 : v.adic_completion K) : (with_zero(multiplicative ℤ))) = 0 :=
    valued.v.map_zero',
    rw h_zero, exact zero_le_one' _ },
  simp_rw [pi.zero_apply, h_empty],
  exact finite_empty,
end

/-- The negative of a finite adèle is a finite adèle. -/
lemma neg {x : K_hat R K} (hx : x.is_finite_adele) : (-x).is_finite_adele  :=
begin
  rw is_finite_adele at hx ⊢,
  have h : ∀ (v : height_one_spectrum R), (-x v ∈ v.adic_completion_integers K) ↔
    (x v ∈ v.adic_completion_integers K),
  { intro v,
    rw [mem_adic_completion_integers, mem_adic_completion_integers, valuation.map_neg], },
  simpa only [pi.neg_apply, h] using hx,
end

/-- The product of two finite adèles is a finite adèle. -/
lemma mul {x y : K_hat R K} (hx : x.is_finite_adele) (hy : y.is_finite_adele) :
  (x * y).is_finite_adele :=
begin
  rw [is_finite_adele, filter.eventually_cofinite] at hx hy ⊢,
  have h_subset : {v : height_one_spectrum R | ¬ (x * y) v ∈  (v.adic_completion_integers K)} ⊆
    {v : height_one_spectrum R | ¬ x v ∈ (v.adic_completion_integers K)} ∪
    {v : height_one_spectrum R | ¬ y v ∈ (v.adic_completion_integers K)},
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq],
    rw mem_set_of_eq at hv,
    contrapose! hv,
    rw [mem_adic_completion_integers, mem_adic_completion_integers] at hv,
    have h_mul : valued.v (x v * y v) = (valued.v (x v)) * (valued.v (y v)) :=
      (valued.v).map_mul' (x v) (y v),
    rw [mem_adic_completion_integers, pi.mul_apply, h_mul],
    exact @mul_le_one' (with_zero (multiplicative ℤ)) _ _
      (ordered_comm_monoid.to_covariant_class_left _) _ _ hv.left hv.right  },
  exact (hx.union hy).subset h_subset,
end

/-- The tuple `(1)_v` is a finite adèle. -/
lemma one : (1 : K_hat R K).is_finite_adele :=
begin
  rw [is_finite_adele, filter.eventually_cofinite],
  have h_empty : {v : height_one_spectrum R |
    ¬ ((1 : v.adic_completion K) ∈ v.adic_completion_integers K)} = ∅,
  { ext v, rw [mem_empty_iff_false, iff_false], intro hv,
    rw mem_set_of_eq at hv, apply hv, rw mem_adic_completion_integers,
    exact le_of_eq valued.v.map_one' },
  simp_rw [pi.one_apply, h_empty],
  exact finite_empty,
end

end is_finite_adele

end prod_adic_completions

open prod_adic_completions.is_finite_adele

variables (R K)
/-- The finite adèle ring of `R` is the restricted product over all maximal ideals `v` of `R`
of `adic_completion` with respect to `adic_completion_integers`. -/
noncomputable! def finite_adele_ring : subring (K_hat R K) :=
{ carrier   := { x : K_hat R K | x.is_finite_adele },
  mul_mem'  := λ _ _ hx hy, mul hx hy,
  one_mem'  := one,
  add_mem'  := λ _ _ hx hy, add hx hy,
  zero_mem' := zero,
  neg_mem'  := λ _ hx, neg hx, }

variables {R K}

@[simp] lemma mem_finite_adele_ring_iff (x : K_hat R K) :
  x ∈ finite_adele_ring R K ↔ x.is_finite_adele :=
iff.rfl

end dedekind_domain
