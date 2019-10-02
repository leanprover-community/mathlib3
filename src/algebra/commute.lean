/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/

import data.equiv.algebra algebra.group_power
  group_theory.submonoid group_theory.subgroup
  ring_theory.subring

/-!
# Commuting pairs of elements in monoids

## Main definitions

* `commute a b` : `a * b = b * a`
* `centralizer a` : `{ x | commute a x }`
* `set.centralizer s` : elements that commute with all `a ∈ s`

We prove that `centralizer` and `set_centralilzer` are submonoid/subgroups/subrings depending on the available structures, and provide operations on `commute _ _`.

E.g., if `a`, `b`, and c are elements of a ring, and
that `hb : commute a b` and `hc : commute a c`.  Then
`hb.pow_left 5` proves `commute (a ^ 5) b` and
`(hb.pow 2).add (hb.mul hc)` proves `commute a (b ^ 2 + b * c)`.

Lean does not immediately recognise these terms as equations,
so for rewriting we need syntax like `rw [(hb.pow_left 5).eq]`
rather than just `rw [hb.pow_left 5]`.
-/

/-- Two elements commute, if `a * b = b * a`. -/
def commute {S : Type*} [has_mul S] (a b : S) : Prop := a * b = b * a

namespace commute

variables {S : Type*} [has_mul S]

/-- Equality behind `commute a b`; useful for rewriting. -/
protected theorem eq {a b : S} (h : commute a b) : a * b = b * a := h

/-- Any element commutes with itself. -/
@[refl] protected theorem refl (a : S) : commute a a := eq.refl (a * a)

/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[symm] protected theorem symm {a b : S} (h : commute a b) : commute b a :=
eq.symm h

protected theorem symm_iff {a b : S} : commute a b ↔ commute b a := ⟨commute.symm, commute.symm⟩

end commute

-- Definitions and trivial theorems about them
section defs

variables {S : Type*} [has_mul S]

/-- Centralizer of an element `a : S` is the set of elements that commute with `a`. -/
def centralizer (a : S) : set S := { x | commute a x }

theorem mem_centralizer {a b : S} : b ∈ centralizer a ↔ commute a b := iff.rfl

/-- Centralizer of a set `T` is the set of elements that commute with all `a ∈ T`. -/
protected def set.centralizer (s : set S) : set S := { x | ∀ a ∈ s, commute a x }

protected theorem set.mem_centralizer (s : set S) {x : S} :
  x ∈ s.centralizer ↔ ∀ a ∈ s, commute a x :=
iff.rfl

protected theorem set.mem_centralizer_iff_subset (s : set S) {x : S} :
  x ∈ s.centralizer ↔ s ⊆ centralizer x :=
by simp only [set.centralizer, centralizer, set.mem_set_of_eq, @commute.symm_iff _ _ x]; refl

protected theorem set.centralizer_eq (s : set S) :
  s.centralizer =  ⋂ a ∈ s, centralizer a :=
set.ext $ assume x,
by simp only [s.mem_centralizer, set.mem_bInter_iff, mem_centralizer]

protected theorem set.centralizer_decreasing {s t : set S} (h : s ⊆ t) :
  t.centralizer ⊆ s.centralizer :=
by simp only [set.centralizer_eq, set.bInter_subset_bInter_left h]

end defs

namespace commute

section semigroup

variables {S : Type*} [semigroup S]

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
protected theorem mul {a b c : S} (hab : commute a b) (hac : commute a c) : commute a (b * c) :=
by dunfold commute; assoc_rw [hab.eq, hac.eq]

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
theorem mul_left {a b c : S}
  (hac : commute a c) (hbc : commute b c) : commute (a * b) c :=
(hac.symm.mul hbc.symm).symm

end semigroup

protected theorem all {S : Type*} [comm_semigroup S] (a b : S) : commute a b := mul_comm a b

section monoid

variables {M : Type*} [monoid M]

protected theorem one (a : M) : commute a 1 :=
by rw [commute, one_mul, mul_one]

theorem one_left (a : M) : commute 1 a := (commute.one a).symm

theorem units_inv {a : M} {u : units M} (h : commute a u) : commute a ↑u⁻¹ :=
calc a * ↑u⁻¹ = ↑u⁻¹ * u * a * ↑u⁻¹ : by rw [units.inv_mul, one_mul]
          ... = ↑u⁻¹ * a * u * ↑u⁻¹ : by assoc_rw [h.eq]
          ... = ↑u⁻¹ * a            : units.mul_inv_cancel_right _ u

protected theorem map {N : Type*} [monoid N] (f : M →* N) {a b : M} (h : commute a b) :
  commute (f a) (f b) :=
by rw [commute, ← f.map_mul, h.eq, f.map_mul]

end monoid

section group

variables {G : Type*} [group G]

protected theorem inv {a b : G} (h : commute a b) : commute a b⁻¹ :=
@units_inv G _ a (to_units G b) h

theorem inv_left {a b : G} (h : commute a b) : commute a⁻¹ b :=
h.symm.inv.symm

theorem inv_inv {a b : G} (hab : commute a b) : commute a⁻¹ b⁻¹ :=
hab.inv.symm.inv.symm

end group

section semiring

variables {A : Type*} [semiring A]

theorem zero (a : A) : commute a 0 := by rw [commute, mul_zero, zero_mul]
theorem zero_left (a : A) : commute 0 a := (commute.zero a).symm

protected theorem add {a b c : A} (hab : commute a b) (hac : commute a c) :
  commute a (b + c) :=
by rw [commute, mul_add, add_mul, hab.eq, hac.eq]

theorem add_left {a b c : A} (hac : commute a c) (hbc : commute b c) :
  commute (a + b) c :=
(hac.symm.add hbc.symm).symm

end semiring

section ring

variables {R : Type*} [ring R]

protected theorem neg {a b : R} (hab : commute a b) : commute a (- b) :=
by rw [commute, ← neg_mul_eq_mul_neg, hab.eq, neg_mul_eq_neg_mul_symm ]

theorem neg_left {a b : R} (hab : commute a b) : commute (- a) b :=
hab.symm.neg.symm

protected theorem neg_one (a : R) : commute a (-1) := (commute.one a).neg
theorem neg_one_left (a : R): commute (-1) a := (commute.neg_one a).symm

protected theorem sub {a b c : R} (hab : commute a b) (hac : commute a c) :
  commute a (b - c) :=
hab.add hac.neg

theorem sub_left {a b c : R} (hac : commute a c) (hbc : commute b c) :
  commute (a - b) c :=
(hac.symm.sub hbc.symm).symm

end ring


end commute

section monoid

variables {M : Type*} [monoid M] (a : M) (s : set M)

instance centralizer.is_submonoid : is_submonoid (centralizer a) :=
{ one_mem := commute.one a,
  mul_mem := λ _ _, commute.mul }

instance set.centralizer.is_submonoid : is_submonoid s.centralizer :=
by rw s.centralizer_eq; apply_instance

theorem monoid.centralizer_closure : (monoid.closure s).centralizer = s.centralizer :=
set.subset.antisymm
  (set.centralizer_decreasing monoid.subset_closure)
  (λ x, by simp only [set.mem_centralizer_iff_subset]; exact monoid.closure_subset)

-- Not sure if this should be an instance
lemma centralizer.inter_units_is_subgroup : is_subgroup { x : units M | commute a x } :=
{ one_mem := commute.one a,
  mul_mem := λ _ _, commute.mul,
  inv_mem := λ _, commute.units_inv }

end monoid

section group

variables {G : Type*} [group G] (a : G) (s : set G)

instance centralizer.is_subgroup : is_subgroup (centralizer a) :=
{ inv_mem := λ _, commute.inv }

instance set.centralizer.is_subgroup : is_subgroup s.centralizer :=
by rw s.centralizer_eq; apply_instance

lemma group.centralizer_closure : (group.closure s).centralizer = s.centralizer :=
set.subset.antisymm
  (set.centralizer_decreasing group.subset_closure)
  (λ x, by simp only [set.mem_centralizer_iff_subset]; exact group.closure_subset)

end group

/- There is no `is_subsemiring` in mathlib, so we only prove `is_add_submonoid` here. -/
section semiring

variables {A : Type*} [semiring A] (a : A) (s : set A)

instance centralizer.is_add_submonoid : is_add_submonoid (centralizer a) :=
{ zero_mem := commute.zero a,
  add_mem := λ _ _, commute.add }

instance set.centralizer.is_add_submonoid : is_add_submonoid s.centralizer :=
by rw s.centralizer_eq; apply_instance

lemma add_monoid.centralizer_closure : (add_monoid.closure s).centralizer = s.centralizer :=
set.subset.antisymm
  (set.centralizer_decreasing add_monoid.subset_closure)
  (λ x, by simp only [set.mem_centralizer_iff_subset]; exact add_monoid.closure_subset)

end semiring

section ring

variables {R : Type*} [ring R] (a : R) (s : set R)

instance centralizer.is_subring : is_subring (centralizer a) :=
{ neg_mem := λ _, commute.neg }

instance set.centralizer.is_subring : is_subring s.centralizer :=
by rw s.centralizer_eq; apply_instance

lemma ring.centralizer_closure : (ring.closure s).centralizer = s.centralizer :=
set.subset.antisymm
  (set.centralizer_decreasing ring.subset_closure)
  (λ x, by simp only [set.mem_centralizer_iff_subset]; exact ring.closure_subset)

end ring

namespace commute

section monoid

variables {M : Type*} [monoid M] {a b : M} (hab : commute a b) (n m : ℕ)

protected theorem pow : commute a (b ^ n) := is_submonoid.pow_mem (mem_centralizer.2 hab)
theorem pow_left : commute (a ^ n) b := (hab.symm.pow n).symm
theorem pow_pow : commute (a ^ n) (b ^ m) := commute.pow (commute.pow_left hab n) m

protected theorem list_prod {a : M} {l : list M} (h : ∀ x ∈ l, commute a x) :
  commute a l.prod :=
is_submonoid.list_prod_mem (λ x hx, mem_centralizer.2 (h x hx))

theorem list_prod_left {l : list M} {a : M} (h : ∀ x ∈ l, commute x a) :
  commute l.prod a :=
(commute.list_prod (λ x hx, (h x hx).symm)).symm

section

include hab

protected theorem mul_pow : ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
| 0 := by simp only [pow_zero, mul_one]
| (n + 1) := by simp only [pow_succ, mul_pow n];
                assoc_rw [(hab.symm.pow n).eq]; rw [mul_assoc]

end

variable (a)

theorem self_pow : commute a (a ^ n) := (commute.refl a).pow n
theorem pow_self : commute (a ^ n) a := (commute.refl a).pow_left n
theorem pow_pow_self : commute (a ^ n) (a ^ m) := (commute.refl a).pow_pow n m

end monoid

section group

variables {G : Type*} [group G] {a b : G} (hab : commute a b) (n m : ℤ)

theorem gpow : commute a (b ^ n) := is_subgroup.gpow_mem (mem_centralizer.2 hab)
theorem gpow_left : commute (a ^ n) b := (hab.symm.gpow n).symm
theorem gpow_gpow : commute (a ^ n) (b ^ m) := (hab.gpow m).gpow_left n

variable (a)

theorem self_gpow : commute a (a ^ n) := (commute.refl a).gpow n
theorem gpow_self : commute (a ^ n) a := (commute.refl a).gpow_left n
theorem gpow_gpow_self : commute (a ^ n) (a ^ m) := (commute.refl a).gpow_gpow n m

include hab

protected theorem mul_gpow : ∀ (n : ℤ), (a * b) ^ n = a ^ n * b ^ n
| (int.of_nat n) := hab.mul_pow n
| (int.neg_succ_of_nat n) :=
    by { simp only [gpow_neg_succ, hab.mul_pow, mul_inv_rev],
         exact (hab.pow_pow n.succ n.succ).inv_inv.symm.eq }

end group

section semiring

variables {A : Type*} [semiring A] {a b : A} (hab : commute a b) (n m : ℕ)

open_locale add_monoid

protected theorem smul : commute a (n • b) := is_add_submonoid.smul_mem (mem_centralizer.2 hab)

theorem smul_left : commute (n • a) b := (hab.symm.smul n).symm
theorem smul_smul : commute (n • a) (m • b) := (hab.smul_left n).smul m

variable (a)

theorem self_smul : commute a (n • a) := (commute.refl a).smul n
theorem smul_self : commute (n • a) a := (commute.refl a).smul_left n
theorem self_smul_smul : commute (n • a) (m • a) := (commute.refl a).smul_smul n m

theorem cast_nat : commute a (n : A) :=
by rw [← add_monoid.smul_one n]; exact (commute.one a).smul n

theorem cast_nat_left : commute (n : A) a :=
(cast_nat a n).symm

end semiring

section ring

variables {R : Type*} [ring R] {a b : R} (hab : commute a b) (n m : ℤ)

open_locale add_group

protected theorem gsmul : commute a (n • b) := is_add_subgroup.gsmul_mem (mem_centralizer.2 hab)
theorem gsmul_left : commute (n • a) b := (hab.symm.gsmul n).symm
theorem gsmul_gsmul : commute (n • a) (m • b) := (hab.gsmul_left n).gsmul m

theorem self_gsmul : commute a (n • a) := (commute.refl a).gsmul n
theorem gsmul_self : commute (n • a) a := (commute.refl a).gsmul_left n
theorem self_gsmul_gsmul : commute (n • a) (m • a) := (commute.refl a).gsmul_gsmul n m

variable (a)

theorem cast_int : commute a (n : R) :=
by rw [← gsmul_one n]; exact (commute.one a).gsmul n

theorem cast_int_left : commute (n : R) a := (commute.cast_int a n).symm

end ring

end commute

theorem neg_pow {R : Type*} [ring R] (a : R) (n : ℕ) : (- a) ^ n = (-1) ^ n * a ^ n :=
(neg_one_mul a) ▸ (commute.neg_one_left a).mul_pow n
