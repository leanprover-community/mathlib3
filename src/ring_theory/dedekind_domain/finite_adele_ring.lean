/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import ring_theory.dedekind_domain.adic_valuation
import topology.algebra.uniform_ring


/-!
# The finite adèle ring of a Dedekind domain
We define the ring of finite adèles of a Dedekind domain `R`.

## Main definitions
- `finite_integral_adeles` : product of `adic_completion_integers`, where `v` runs over all
   maximal ideals of `R`.
- `prod_completions` : the product of `adic_completion`, where `v` runs over all maximal ideals
  of `R`.
- `finite_adele_ring` : The finite adèle ring of `R`, defined as the restricted product
  `Π'_v K_v`.

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

variables (R K : Type*) [comm_ring R] [is_domain R] [is_dedekind_domain R] [field K]
  [algebra R K] [is_fraction_ring R K] (v : height_one_spectrum R)

/-- The product of all `adic_completion_integers`, where `v` runs over the maximal ideals of `R`. -/
def finite_integral_adeles := Π (v : height_one_spectrum R), v.adic_completion_integers K

local notation `R_hat` := finite_integral_adeles

instance : comm_ring (R_hat R K) := pi.comm_ring

instance : topological_space (R_hat R K) := Pi.topological_space

instance finite_integral_adeles.inhabited : inhabited (finite_integral_adeles R K) := ⟨0⟩

/-- The product of all `adic_completion`, where `v` runs over the maximal ideals of `R`. -/
def prod_completions := Π (v : height_one_spectrum R), v.adic_completion K

local notation `K_hat` := prod_completions

instance : comm_ring (K_hat R K) := pi.comm_ring
instance : ring (K_hat R K) := infer_instance
instance : topological_space (K_hat R K) := Pi.topological_space
instance : topological_ring (K_hat R K) :=
(infer_instance : topological_ring (Π (v : height_one_spectrum R), v.adic_completion K))

instance prod_completions.inhabited : inhabited (prod_completions R K) := ⟨0⟩

namespace finite_integral_adeles

noncomputable! instance : has_coe (R_hat R K) (K_hat R K) := { coe := λ x v, x v }

lemma coe_apply (x : R_hat R K) (v : height_one_spectrum R) : (x : K_hat R K) v = ↑(x v) := rfl

/-- The inclusion of `R_hat` in `K_hat` is a homomorphism of additive monoids. -/
noncomputable! def coe.add_monoid_hom : add_monoid_hom (R_hat R K) (K_hat R K) :=
{ to_fun    := coe,
  map_zero' := rfl,
  map_add'  := λ x y, by { ext v, simp only [coe_apply, pi.add_apply, subring.coe_add] }}

lemma coe.add_monoid_hom_apply (x : R_hat R K) (v : height_one_spectrum R) :
  (coe.add_monoid_hom R K) x v = x v := rfl

/-- The inclusion of `R_hat` in `K_hat` is a ring homomorphism. -/
noncomputable! def coe.ring_hom : ring_hom (R_hat R K) (K_hat R K)  :=
{ to_fun   := coe,
  map_one' := rfl,
  map_mul' := λ x y, by {ext p, simp only [pi.mul_apply, subring.coe_mul], refl },
  ..coe.add_monoid_hom R K }

lemma coe.ring_hom_apply (x : R_hat R K) (v : height_one_spectrum R) :
  (coe.ring_hom R K) x v = x v := rfl

end finite_integral_adeles

section algebra_instances

instance : algebra K (K_hat R K) :=
(by apply_instance : algebra K ((Π (v : height_one_spectrum R), v.adic_completion K)))

instance prod_completions.algebra' : algebra R (K_hat R K) :=
(by apply_instance : algebra R (Π (v : height_one_spectrum R), v.adic_completion K))

instance : is_scalar_tower R K (K_hat R K) :=
(by apply_instance : is_scalar_tower R K ((Π (v : height_one_spectrum R), v.adic_completion K)))

instance : algebra R (R_hat R K) :=
(by apply_instance : algebra R (Π (v : height_one_spectrum R), v.adic_completion_integers K))

instance prod_completions.algebra_completions : algebra (R_hat R K) (K_hat R K) :=
(finite_integral_adeles.coe.ring_hom R K).to_algebra

instance prod_completions.is_scalar_tower_completions :
  is_scalar_tower R (R_hat R K) (K_hat R K) :=
(by apply_instance : is_scalar_tower R (Π (v : height_one_spectrum R), v.adic_completion_integers K)
   (Π (v : height_one_spectrum R), v.adic_completion K))

end algebra_instances

namespace finite_integral_adeles

/-- The inclusion of `R_hat` in `K_hat` is a ring homomorphism. -/
noncomputable! def coe.alg_hom : alg_hom R (R_hat R K) (K_hat R K)  :=
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

/-- The finite adèle ring of `R` is the restricted product over all maximal ideals `v` of `R`
of `adic_completion` with respect to `adic_completion_integers`.-/
def finite_adele_ring := { x : (K_hat R K) //
  ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, (x v ∈ v.adic_completion_integers K) }

/-- The coercion map from `finite_adele_ring R K` to `K_hat R K`. -/
noncomputable! def coe' : (finite_adele_ring R K) → K_hat R K := λ x, x.val
instance has_coe' : has_coe (finite_adele_ring R K) (K_hat R K) := {coe := coe' R K }
instance has_lift_t' : has_lift_t (finite_adele_ring R K) (K_hat R K) := {lift := coe' R K }

/-- The sum of two finite adèles is a finite adèle. -/
lemma restr_add (x y : finite_adele_ring R K) : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
  ((x.val + y.val) v ∈ v.adic_completion_integers K) :=
begin
  cases x with x hx,
  cases y with y hy,
  rw filter.eventually_cofinite at hx hy ⊢,
  have h_subset : {v : height_one_spectrum R | ¬ (x + y) v ∈  (v.adic_completion_integers K)} ⊆
    {v : height_one_spectrum R | ¬ x v ∈ (v.adic_completion_integers K)} ∪
    {v : height_one_spectrum R | ¬ y v ∈ (v.adic_completion_integers K)},
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq],
    rw mem_set_of_eq at hv,
    by_contradiction h,
    push_neg at h,
    apply hv,
    rw [adic_completion.is_integer, adic_completion.is_integer, ← max_le_iff] at h,
    rw [adic_completion.is_integer, pi.add_apply],
    exact le_trans (valued.v.map_add_le_max' (x v) (y v)) h },
  exact finite.subset (finite.union hx hy) h_subset,
end

/-- Addition on the finite adèle ring. -/
def add' (x y : finite_adele_ring R K) : finite_adele_ring R K :=
⟨x.val + y.val, restr_add R K x y⟩

/-- The tuple `(0)_v` is a finite adèle. -/
lemma restr_zero : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
  ((0 : v.adic_completion K) ∈ v.adic_completion_integers K) :=
begin
  rw filter.eventually_cofinite,
  have h_empty : {v : height_one_spectrum R |
    ¬ ((0 : v.adic_completion K) ∈ v.adic_completion_integers K)} = ∅,
  { ext v, rw mem_empty_iff_false, split; intro hv,
    { rw mem_set_of_eq at hv, apply hv, rw adic_completion.is_integer,
      have h_zero : (valued.v (0 : v.adic_completion K) : (with_zero(multiplicative ℤ))) = 0 :=
      valued.v.map_zero',
      rw h_zero, exact zero_le_one' _ },
    { exfalso, exact hv }},
  rw h_empty,
  exact finite_empty,
end

/-- The negative of a finite adèle is a finite adèle. -/
lemma restr_neg (x : finite_adele_ring R K)  : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
  (-x.val v ∈ v.adic_completion_integers K) :=
begin
  cases x with x hx,
  have h : ∀ (v : height_one_spectrum R), (-x v ∈ v.adic_completion_integers K) ↔
    (x v ∈ v.adic_completion_integers K),
  { intro v,
    rw [adic_completion.is_integer, adic_completion.is_integer, valuation.map_neg], },
  simpa only [h] using hx,
end

/-- Negation on the finite adèle ring. -/
def neg' (x : finite_adele_ring R K) : finite_adele_ring R K := ⟨-x.val, restr_neg R K x⟩

/-- The product of two finite adèles is a finite adèle. -/
lemma restr_mul (x y : finite_adele_ring R K) : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
  ((x.val * y.val) v ∈ v.adic_completion_integers K) :=
begin
  cases x with x hx,
  cases y with y hy,
  rw filter.eventually_cofinite at hx hy ⊢,
  have h_subset : {v : height_one_spectrum R | ¬ (x * y) v ∈  (v.adic_completion_integers K)} ⊆
    {v : height_one_spectrum R | ¬ x v ∈ (v.adic_completion_integers K)} ∪
    {v : height_one_spectrum R | ¬ y v ∈ (v.adic_completion_integers K)},
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq],
    rw mem_set_of_eq at hv,
    by_contradiction h,
    push_neg at h,
    apply hv,
    rw [adic_completion.is_integer, adic_completion.is_integer] at h,
    have h_mul : valued.v (x v * y v) = (valued.v (x v)) * (valued.v (y v))
    := (valued.v).map_mul' (x v) (y v),
    rw [adic_completion.is_integer, pi.mul_apply, h_mul],
    exact @mul_le_one' (with_zero (multiplicative ℤ)) _ _
      (ordered_comm_monoid.to_covariant_class_left _) _ _ h.left h.right  },
  exact finite.subset (finite.union hx hy) h_subset,
end

/-- Multiplication on the finite adèle ring. -/
def mul' (x y : finite_adele_ring R K) : finite_adele_ring R K :=
⟨x.val * y.val, restr_mul R K x y⟩

/-- The tuple `(1)_v` is a finite adèle. -/
lemma restr_one : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
  ((1 : v.adic_completion K) ∈ v.adic_completion_integers K) :=
begin
  rw filter.eventually_cofinite,
  have h_empty : {v : height_one_spectrum R |
    ¬ ((1 : v.adic_completion K) ∈ v.adic_completion_integers K)} = ∅,
  { ext v, rw mem_empty_iff_false, split; intro hv,
    { rw mem_set_of_eq at hv, apply hv, rw adic_completion.is_integer,
      exact le_of_eq valued.v.map_one' },
    { exfalso, exact hv }},
  rw h_empty,
  exact finite_empty,
end

/-- `finite_adele_ring R K` is a commutative additive group. -/
instance : add_comm_group (finite_adele_ring R K) :=
{ add          := add' R K,
  add_assoc    := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩,
  by { dsimp only [add'], rw [subtype.mk_eq_mk], exact add_assoc _ _ _, },
  zero         := ⟨0, restr_zero R K⟩,
  zero_add     := λ x, by { simp_rw [add', zero_add, subtype.val_eq_coe, subtype.coe_eta] },
  add_zero     := λ x, by { simp_rw [add', add_zero, subtype.val_eq_coe, subtype.coe_eta] },
  neg          := λ x, ⟨-x.val, restr_neg R K x⟩,
  add_left_neg := λ x, by { unfold_projs,  dsimp only [add'], ext,
    rw [subtype.coe_mk, subtype.coe_mk, pi.add_apply, add_left_neg], refl, },
  add_comm     := λ x y, by { unfold_projs,  dsimp only [add'], ext,
    rw [subtype.coe_mk, subtype.coe_mk, pi.add_apply, pi.add_apply, add_comm], }}

/-- `finite_adele_ring R K` is a commutative ring. -/
instance : comm_ring (finite_adele_ring R K) :=
{ mul           := mul' R K,
  mul_assoc     := λ x y z, by { unfold_projs, simp_rw [mul'],
    rw [subtype.mk_eq_mk, mul_assoc]},
  one           := ⟨1, restr_one R K⟩,
  one_mul       := λ x, by { simp_rw [mul', one_mul, subtype.val_eq_coe, subtype.coe_eta] },
  mul_one       := λ x, by { simp_rw [mul', mul_one, subtype.val_eq_coe, subtype.coe_eta] },
  left_distrib  := λ x y z, by { unfold_projs, simp_rw [mul', add', left_distrib] },
  right_distrib := λ x y z, by { unfold_projs, simp_rw [mul', add', right_distrib] },
  mul_comm      := λ x y, by { unfold_projs, rw [mul', mul', subtype.mk_eq_mk, mul_comm] },
  ..(finite_adele_ring.add_comm_group R K) }

namespace finite_adele_ring
variables {R K}

@[norm_cast] lemma coe_add (x y : finite_adele_ring R K) :(↑(x + y) : K_hat R K) = ↑x + ↑y := rfl

@[norm_cast] lemma coe_zero : (↑(0 : finite_adele_ring R K) : K_hat R K) = 0 :=
rfl

@[norm_cast] lemma coe_neg (x : finite_adele_ring R K) : (↑(-x) : K_hat R K) = -↑x  := rfl

@[norm_cast] lemma coe_mul (x y : finite_adele_ring R K) :(↑(x * y) : K_hat R K) = ↑x * ↑y := rfl

@[norm_cast] lemma coe_one : (↑(1 : finite_adele_ring R K) : K_hat R K) = 1 := rfl

instance inhabited : inhabited (finite_adele_ring R K) := ⟨⟨0, restr_zero R K⟩⟩

end finite_adele_ring
