/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import algebra.star.pointwise
import algebra.star.subalgebra
import tactic.noncomm_ring
/-!
# Spectrum of an element in an algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
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
-/

open set
open_locale pointwise

universes u v

section defs

variables (R : Type u) {A : Type v}
variables [comm_semiring R] [ring A] [algebra R A]

local notation `↑ₐ` := algebra_map R A

-- definition and basic properties

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent set* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
algebra `A`.  -/
def resolvent_set (a : A) : set R :=
{ r : R | is_unit (↑ₐr - a) }


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
ring.inverse (↑ₐr - a)

/-- The unit `1 - r⁻¹ • a` constructed from `r • 1 - a` when the latter is a unit. -/
@[simps]
noncomputable def is_unit.sub_inv_smul {r : Rˣ} {s : R} {a : A}
  (h : is_unit $ r • ↑ₐs  - a) : Aˣ :=
{ val := ↑ₐs - r⁻¹ • a,
  inv := r • ↑h.unit⁻¹,
  val_inv := by rw [mul_smul_comm, ←smul_mul_assoc, smul_sub, smul_inv_smul, h.mul_coe_inv],
  inv_val := by rw [smul_mul_assoc, ←mul_smul_comm, smul_sub, smul_inv_smul, h.coe_inv_mul], }

end defs

namespace spectrum

section scalar_semiring

variables {R : Type u} {A : Type v}
variables [comm_semiring R] [ring A] [algebra R A]

local notation `σ` := spectrum R
local notation `↑ₐ` := algebra_map R A

lemma mem_iff {r : R} {a : A} :
  r ∈ σ a ↔ ¬ is_unit (↑ₐr - a) :=
iff.rfl

lemma not_mem_iff {r : R} {a : A} :
  r ∉ σ a ↔ is_unit (↑ₐr - a) :=
by { apply not_iff_not.mp, simp [set.not_not_mem, mem_iff] }

variables (R)

lemma zero_mem_iff {a : A} : (0 : R) ∈ σ a ↔ ¬is_unit a :=
by rw [mem_iff, map_zero, zero_sub, is_unit.neg_iff]

lemma zero_not_mem_iff {a : A} : (0 : R) ∉ σ a ↔ is_unit a :=
by rw [zero_mem_iff, not_not]

variables {R}

lemma mem_resolvent_set_of_left_right_inverse {r : R} {a b c : A}
  (h₁ : (↑ₐr - a) * b = 1) (h₂ : c * (↑ₐr - a) = 1) :
  r ∈ resolvent_set R a :=
units.is_unit ⟨↑ₐr - a, b, h₁, by rwa ←left_inv_eq_right_inv h₂ h₁⟩

lemma mem_resolvent_set_iff {r : R} {a : A} :
  r ∈ resolvent_set R a ↔ is_unit (↑ₐr - a) :=
iff.rfl

@[simp] lemma resolvent_set_of_subsingleton [subsingleton A] (a : A) :
  resolvent_set R a = set.univ :=
by simp_rw [resolvent_set, subsingleton.elim (algebra_map R A _ - a) 1, is_unit_one,
  set.set_of_true]

@[simp] lemma of_subsingleton [subsingleton A] (a : A) :
  spectrum R a = ∅ :=
by rw [spectrum, resolvent_set_of_subsingleton, set.compl_univ]

lemma resolvent_eq {a : A} {r : R} (h : r ∈ resolvent_set R a) :
  resolvent a r = ↑h.unit⁻¹ :=
ring.inverse_unit h.unit

lemma units_smul_resolvent {r : Rˣ} {s : R} {a : A} :
  r • resolvent a (s : R) = resolvent (r⁻¹ • a) (r⁻¹ • s : R) :=
begin
  by_cases h : s ∈ spectrum R a,
  { rw [mem_iff] at h,
    simp only [resolvent, algebra.algebra_map_eq_smul_one] at *,
    rw [smul_assoc, ←smul_sub],
    have h' : ¬ is_unit (r⁻¹ • (s • 1 - a)),
      from λ hu, h (by simpa only [smul_inv_smul] using is_unit.smul r hu),
    simp only [ring.inverse_non_unit _ h, ring.inverse_non_unit _ h', smul_zero] },
  { simp only [resolvent],
    have h' : is_unit (r • (algebra_map R A (r⁻¹ • s)) - a),
      { simpa [algebra.algebra_map_eq_smul_one, smul_assoc] using not_mem_iff.mp h },
    rw [←h'.coe_sub_inv_smul, ←(not_mem_iff.mp h).unit_spec, ring.inverse_unit, ring.inverse_unit,
      h'.coe_inv_sub_inv_smul],
    simp only [algebra.algebra_map_eq_smul_one, smul_assoc, smul_inv_smul], },
end

lemma units_smul_resolvent_self {r : Rˣ} {a : A} :
  r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R) :=
by simpa only [units.smul_def, algebra.id.smul_eq_mul, units.inv_mul]
  using @units_smul_resolvent _ _ _ _ _ r r a

/-- The resolvent is a unit when the argument is in the resolvent set. -/
lemma is_unit_resolvent {r : R} {a : A} :
  r ∈ resolvent_set R a ↔ is_unit (resolvent a r) :=
is_unit_ring_inverse.symm

lemma inv_mem_resolvent_set {r : Rˣ} {a : Aˣ} (h : (r : R) ∈ resolvent_set R (a : A)) :
  (↑r⁻¹ : R) ∈ resolvent_set R (↑a⁻¹ : A) :=
begin
  rw [mem_resolvent_set_iff, algebra.algebra_map_eq_smul_one, ←units.smul_def] at h ⊢,
  rw [is_unit.smul_sub_iff_sub_inv_smul, inv_inv, is_unit.sub_iff],
  have h₁ : (a : A) * (r • (↑a⁻¹ : A) - 1) = r • 1 - a,
  { rw [mul_sub, mul_smul_comm, a.mul_inv, mul_one], },
  have h₂ : (r • (↑a⁻¹ : A) - 1) * a = r • 1 - a,
  { rw [sub_mul, smul_mul_assoc, a.inv_mul, one_mul], },
  have hcomm : commute (a : A) (r • (↑a⁻¹ : A) - 1), { rwa ←h₂ at h₁ },
  exact (hcomm.is_unit_mul_iff.mp (h₁.symm ▸ h)).2,
end

lemma inv_mem_iff {r : Rˣ} {a : Aˣ} :
  (r : R) ∈ σ (a : A) ↔ (↑r⁻¹ : R) ∈ σ (↑a⁻¹ : A) :=
not_iff_not.2 $ ⟨inv_mem_resolvent_set, inv_mem_resolvent_set⟩

lemma zero_mem_resolvent_set_of_unit (a : Aˣ) : 0 ∈ resolvent_set R (a : A) :=
by simpa only [mem_resolvent_set_iff, ←not_mem_iff, zero_not_mem_iff] using a.is_unit

lemma ne_zero_of_mem_of_unit {a : Aˣ} {r : R} (hr : r ∈ σ (a : A)) : r ≠ 0 :=
λ hn, (hn ▸ hr) (zero_mem_resolvent_set_of_unit a)

lemma add_mem_iff {a : A} {r s : R} :
  r + s ∈ σ a ↔ r ∈ σ (-↑ₐs + a) :=
by simp only [mem_iff, sub_neg_eq_add, ←sub_sub, map_add]

lemma add_mem_add_iff {a : A} {r s : R} :
  r + s ∈ σ (↑ₐs + a) ↔ r ∈ σ a  :=
by rw [add_mem_iff, neg_add_cancel_left]

lemma smul_mem_smul_iff {a : A} {s : R} {r : Rˣ} :
  r • s ∈ σ (r • a) ↔ s ∈ σ a :=
by simp only [mem_iff, not_iff_not, algebra.algebra_map_eq_smul_one, smul_assoc, ←smul_sub,
  is_unit_smul_iff]

theorem unit_smul_eq_smul (a : A) (r : Rˣ) :
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

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : Rˣ`
theorem unit_mem_mul_iff_mem_swap_mul {a b : A} {r : Rˣ} :
  ↑r ∈ σ (a * b) ↔ ↑r ∈ σ (b * a) :=
begin
  have h₁ : ∀ x y : A, is_unit (1 - x * y) → is_unit (1 - y * x),
  { refine λ x y h, ⟨⟨1 - y * x, 1 + y * h.unit.inv * x, _, _⟩, rfl⟩,
    calc (1 - y * x) * (1 + y * (is_unit.unit h).inv * x)
        = (1 - y * x) + y * ((1 - x * y) * h.unit.inv) * x : by noncomm_ring
    ... = 1 : by simp only [units.inv_eq_coe_inv, is_unit.mul_coe_inv, mul_one, sub_add_cancel],
    calc (1 + y * (is_unit.unit h).inv * x) * (1 - y * x)
        = (1 - y * x) + y * (h.unit.inv * (1 - x * y)) * x : by noncomm_ring
    ... = 1 : by simp only [units.inv_eq_coe_inv, is_unit.coe_inv_mul, mul_one, sub_add_cancel]},
  simpa only [mem_iff, not_iff_not, algebra.algebra_map_eq_smul_one, ←units.smul_def,
    is_unit.smul_sub_iff_sub_inv_smul, ←smul_mul_assoc, ←mul_smul_comm r⁻¹ b a]
    using iff.intro (h₁ (r⁻¹ • a) b) (h₁ b (r⁻¹ • a)),
end

theorem preimage_units_mul_eq_swap_mul {a b : A} :
  (coe : Rˣ → R) ⁻¹' σ (a * b) = coe ⁻¹'  σ (b * a) :=
set.ext $ λ _, unit_mem_mul_iff_mem_swap_mul

section star

variables [has_involutive_star R] [star_ring A] [star_module R A]

lemma star_mem_resolvent_set_iff {r : R} {a : A} :
  star r ∈ resolvent_set R a ↔ r ∈ resolvent_set R (star a) :=
by refine ⟨λ h, _, λ h, _⟩;
  simpa only [mem_resolvent_set_iff, algebra.algebra_map_eq_smul_one, star_sub, star_smul,
    star_star, star_one] using is_unit.star h

protected lemma map_star (a : A) : σ (star a) = star (σ a) :=
by { ext, simpa only [set.mem_star, mem_iff, not_iff_not] using star_mem_resolvent_set_iff.symm }

end star

end scalar_semiring

section scalar_ring

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] [algebra R A]

local notation `σ` := spectrum R
local notation `↑ₐ` := algebra_map R A

-- it would be nice to state this for `subalgebra_class`, but we don't have such a thing yet
lemma subset_subalgebra {S : subalgebra R A} (a : S) : spectrum R (a : A) ⊆ spectrum R a :=
compl_subset_compl.2 (λ _, is_unit.map S.val)

-- this is why it would be nice if `subset_subalgebra` was registered for `subalgebra_class`.
lemma subset_star_subalgebra [star_ring R] [star_ring A] [star_module R A] {S : star_subalgebra R A}
  (a : S) : spectrum R (a : A) ⊆ spectrum R a :=
compl_subset_compl.2 (λ _, is_unit.map S.subtype)

lemma singleton_add_eq (a : A) (r : R) : {r} + (σ a) = σ (↑ₐr + a) :=
ext $ λ x,
  by rw [singleton_add, image_add_left, mem_preimage, add_comm, add_mem_iff, map_neg, neg_neg]

lemma add_singleton_eq (a : A) (r : R) : (σ a) + {r} = σ (a + ↑ₐr) :=
add_comm {r} (σ a) ▸ add_comm (algebra_map R A r) a ▸ singleton_add_eq a r

lemma vadd_eq (a : A) (r : R) : r +ᵥ (σ a) = σ (↑ₐr + a) :=
(singleton_add).symm.trans $ singleton_add_eq a r

lemma neg_eq (a : A) : -(σ a) = σ (-a) :=
set.ext $ λ x, by simp only [mem_neg, mem_iff, map_neg, ←neg_add', is_unit.neg_iff, sub_neg_eq_add]

lemma singleton_sub_eq (a : A) (r : R) :
  {r} - (σ a) = σ (↑ₐr - a) :=
by rw [sub_eq_add_neg, neg_eq, singleton_add_eq, sub_eq_add_neg]

lemma sub_singleton_eq (a : A) (r : R) :
  (σ a) - {r} = σ (a - ↑ₐr) :=
by simpa only [neg_sub, neg_eq] using congr_arg has_neg.neg (singleton_sub_eq a r)

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
by rw [←add_zero (↑ₐk), ←singleton_add_eq, zero_eq, set.singleton_add_singleton, add_zero]

@[simp] lemma one_eq [nontrivial A] : σ (1 : A) = {1} :=
calc σ (1 : A) = σ (↑ₐ1) : by rw [algebra.algebra_map_eq_smul_one, one_smul]
  ...          = {1}     : scalar_eq 1

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

protected lemma map_inv (a : Aˣ) : (σ (a : A))⁻¹ = σ (↑a⁻¹ : A) :=
begin
  refine set.eq_of_subset_of_subset (λ k hk, _) (λ k hk, _),
  { rw set.mem_inv at hk,
    have : k ≠ 0,
    { simpa only [inv_inv] using inv_ne_zero (ne_zero_of_mem_of_unit hk), },
    lift k to 𝕜ˣ using is_unit_iff_ne_zero.mpr this,
    rw ←units.coe_inv k at hk,
    exact inv_mem_iff.mp hk },
  { lift k to 𝕜ˣ using is_unit_iff_ne_zero.mpr (ne_zero_of_mem_of_unit hk),
    simpa only [units.coe_inv] using inv_mem_iff.mp hk, }
end

end scalar_field

end spectrum

namespace alg_hom

section comm_semiring

variables {F R A B : Type*} [comm_semiring R] [ring A] [algebra R A] [ring B] [algebra R B]
variables [alg_hom_class F R A B]
local notation `σ` := spectrum R
local notation `↑ₐ` := algebra_map R A

lemma mem_resolvent_set_apply (φ : F) {a : A} {r : R} (h : r ∈ resolvent_set R a) :
  r ∈ resolvent_set R ((φ : A → B) a) :=
by simpa only [map_sub, alg_hom_class.commutes] using h.map φ

lemma spectrum_apply_subset (φ : F) (a : A) : σ ((φ : A → B) a) ⊆ σ a :=
λ _, mt (mem_resolvent_set_apply φ)

end comm_semiring

section comm_ring

variables {F R A B : Type*} [comm_ring R] [ring A] [algebra R A] [ring B] [algebra R B]
variables [alg_hom_class F R A R]
local notation `σ` := spectrum R
local notation `↑ₐ` := algebra_map R A

lemma apply_mem_spectrum [nontrivial R] (φ : F) (a : A) : φ a ∈ σ a :=
begin
  have h : ↑ₐ(φ a) - a ∈ (φ : A →+* R).ker,
  { simp only [ring_hom.mem_ker, map_sub, ring_hom.coe_coe, alg_hom_class.commutes,
      algebra.id.map_eq_id, ring_hom.id_apply, sub_self], },
  simp only [spectrum.mem_iff, ←mem_nonunits_iff, coe_subset_nonunits ((φ : A →+* R).ker_ne_top) h],
end

end comm_ring

end alg_hom
