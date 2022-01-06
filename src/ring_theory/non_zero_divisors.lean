/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma
-/

import group_theory.submonoid.operations
import group_theory.submonoid.membership

/-!
# Non-zero divisors

In this file we define the submonoid `non_zero_divisors` of a `monoid_with_zero`.

## Notations

This file declares the notation `R⁰` for the submonoid of non-zero-divisors of `R`,
in the locale `non_zero_divisors`. Use the statement `open_locale non_zero_divisors`
to access this notation in your own code.

-/

section non_zero_divisors

/-- The submonoid of non-zero-divisors of a `monoid_with_zero` `R`. -/
def non_zero_divisors (R : Type*) [monoid_with_zero R] : submonoid R :=
{ carrier := {x | ∀ z, z * x = 0 → z = 0},
  one_mem' := λ z hz, by rwa mul_one at hz,
  mul_mem' := λ x₁ x₂ hx₁ hx₂ z hz,
    have z * x₁ * x₂ = 0, by rwa mul_assoc,
    hx₁ z $ hx₂ (z * x₁) this }

localized "notation R`⁰`:9000 := non_zero_divisors R" in non_zero_divisors

variables {M M' M₁ R R' : Type*} [monoid_with_zero M] [monoid_with_zero M']
  [comm_monoid_with_zero M₁] [ring R] [comm_ring R']

lemma mem_non_zero_divisors_iff {r : M} : r ∈ M⁰ ↔ ∀ x, x * r = 0 → x = 0 := iff.rfl

lemma mul_right_mem_non_zero_divisors_eq_zero_iff {x r : M} (hr : r ∈ M⁰) :
  x * r = 0 ↔ x = 0 :=
⟨hr _, by simp {contextual := tt}⟩

@[simp] lemma mul_right_coe_non_zero_divisors_eq_zero_iff {x : M} {c : M⁰} :
  x * c = 0 ↔ x = 0 :=
mul_right_mem_non_zero_divisors_eq_zero_iff c.prop

lemma mul_left_mem_non_zero_divisors_eq_zero_iff {r x : M₁} (hr : r ∈ M₁⁰) :
  r * x = 0 ↔ x = 0 :=
by rw [mul_comm, mul_right_mem_non_zero_divisors_eq_zero_iff hr]

@[simp] lemma mul_left_coe_non_zero_divisors_eq_zero_iff {c : M₁⁰} {x : M₁} :
  (c : M₁) * x = 0 ↔ x = 0 :=
mul_left_mem_non_zero_divisors_eq_zero_iff c.prop

lemma mul_cancel_right_mem_non_zero_divisor {x y r : R} (hr : r ∈ R⁰) :
  x * r = y * r ↔ x = y :=
begin
  refine ⟨λ h, _, congr_arg _⟩,
  rw [←sub_eq_zero, ←mul_right_mem_non_zero_divisors_eq_zero_iff hr, sub_mul, h, sub_self]
end

lemma mul_cancel_right_coe_non_zero_divisor {x y : R} {c : R⁰} :
  x * c = y * c ↔ x = y :=
mul_cancel_right_mem_non_zero_divisor c.prop

@[simp] lemma mul_cancel_left_mem_non_zero_divisor {x y r : R'} (hr : r ∈ R'⁰) :
  r * x = r * y ↔ x = y :=
by simp_rw [mul_comm r, mul_cancel_right_mem_non_zero_divisor hr]

lemma mul_cancel_left_coe_non_zero_divisor {x y : R'} {c : R'⁰} :
  (c : R') * x = c * y ↔ x = y :=
mul_cancel_left_mem_non_zero_divisor c.prop

lemma non_zero_divisors.ne_zero [nontrivial M] {x} (hx : x ∈ M⁰) : x ≠ 0 :=
λ h, one_ne_zero (hx _ $ (one_mul _).trans h)

lemma non_zero_divisors.coe_ne_zero [nontrivial M] (x : M⁰) : (x : M) ≠ 0 :=
non_zero_divisors.ne_zero x.2

lemma mul_mem_non_zero_divisors {a b : M₁} :
  a * b ∈ M₁⁰ ↔ a ∈ M₁⁰ ∧ b ∈ M₁⁰ :=
begin
  split,
  { intro h,
    split; intros x h'; apply h,
    { rw [←mul_assoc, h', zero_mul] },
    { rw [mul_comm a b, ←mul_assoc, h', zero_mul] } },
  { rintros ⟨ha, hb⟩ x hx,
    apply ha,
    apply hb,
    rw [mul_assoc, hx] },
end

lemma is_unit_of_mem_non_zero_divisors {G₀ : Type*} [group_with_zero G₀]
  {x : G₀} (hx : x ∈ non_zero_divisors G₀) : is_unit x :=
⟨⟨x, x⁻¹, mul_inv_cancel (non_zero_divisors.ne_zero hx),
  inv_mul_cancel (non_zero_divisors.ne_zero hx)⟩, rfl⟩

lemma eq_zero_of_ne_zero_of_mul_right_eq_zero [no_zero_divisors M]
  {x y : M} (hnx : x ≠ 0) (hxy : y * x = 0) : y = 0 :=
or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

lemma eq_zero_of_ne_zero_of_mul_left_eq_zero [no_zero_divisors M]
  {x y : M} (hnx : x ≠ 0) (hxy : x * y = 0) : y = 0 :=
or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

lemma mem_non_zero_divisors_iff_ne_zero [no_zero_divisors M] [nontrivial M] {x : M} :
  x ∈ M⁰ ↔ x ≠ 0 :=
⟨non_zero_divisors.ne_zero, λ hnx z, eq_zero_of_ne_zero_of_mul_right_eq_zero hnx⟩

lemma monoid_with_zero_hom.map_ne_zero_of_mem_non_zero_divisors [nontrivial M]
  (g : monoid_with_zero_hom M M') (hg : function.injective g)
  {x : M} (h : x ∈ M⁰) : g x ≠ 0 :=
λ h0, one_ne_zero (h 1 ((one_mul x).symm ▸ (hg (trans h0 g.map_zero.symm))))

lemma ring_hom.map_ne_zero_of_mem_non_zero_divisors {R R' : Type*} [semiring R] [semiring R']
  [nontrivial R]
  (g : R →+* R') (hg : function.injective g)
  {x : R} (h : x ∈ R⁰) : g x ≠ 0 :=
g.to_monoid_with_zero_hom.map_ne_zero_of_mem_non_zero_divisors hg h

lemma monoid_with_zero_hom.map_mem_non_zero_divisors [nontrivial M] [no_zero_divisors M']
  (g : monoid_with_zero_hom M M') (hg : function.injective g)
  {x : M} (h : x ∈ M⁰) : g x ∈ M'⁰ :=
λ z hz, eq_zero_of_ne_zero_of_mul_right_eq_zero
  (g.map_ne_zero_of_mem_non_zero_divisors hg h) hz

lemma ring_hom.map_mem_non_zero_divisors {R R' : Type*} [semiring R] [semiring R']
  [nontrivial R] [no_zero_divisors R']
  (g : R →+* R') (hg : function.injective g)
  {x : R} (h : x ∈ R⁰) : g x ∈ R'⁰ :=
g.to_monoid_with_zero_hom.map_mem_non_zero_divisors hg h

lemma le_non_zero_divisors_of_no_zero_divisors [no_zero_divisors M] {S : submonoid M}
  (hS : (0 : M) ∉ S) : S ≤ M⁰ :=
λ x hx y hy, or.rec_on (eq_zero_or_eq_zero_of_mul_eq_zero hy)
  (λ h, h) (λ h, absurd (h ▸ hx : (0 : M) ∈ S) hS)

lemma powers_le_non_zero_divisors_of_no_zero_divisors [no_zero_divisors M]
  {a : M} (ha : a ≠ 0) : submonoid.powers a ≤ M⁰ :=
le_non_zero_divisors_of_no_zero_divisors (λ h, absurd (h.rec_on (λ _ hn, pow_eq_zero hn)) ha)

lemma monoid_with_zero_hom.map_le_non_zero_divisors_of_injective
  [nontrivial M] [no_zero_divisors M']
  (f : monoid_with_zero_hom M M') (hf : function.injective f)
  {S : submonoid M} (hS : S ≤ M⁰) : S.map ↑f ≤ M'⁰ :=
le_non_zero_divisors_of_no_zero_divisors (λ h, let ⟨x, hx, hx0⟩ := h in
  zero_ne_one (hS (hf (trans hx0 (f.map_zero.symm)) ▸ hx : 0 ∈ S) 1 (mul_zero 1)).symm)

lemma ring_hom.map_le_non_zero_divisors_of_injective {R R' : Type*} [semiring R] [semiring R']
  [nontrivial R] [no_zero_divisors R']
  (f : R →+* R') (hf : function.injective f)
  {S : submonoid R} (hS : S ≤ R⁰) : S.map ↑f ≤ R'⁰ :=
f.to_monoid_with_zero_hom.map_le_non_zero_divisors_of_injective hf hS

lemma prod_zero_iff_exists_zero [no_zero_divisors M₁] [nontrivial M₁]
  {s : multiset M₁} : s.prod = 0 ↔ ∃ (r : M₁) (hr : r ∈ s), r = 0 :=
begin
  split, swap,
  { rintros ⟨r, hrs, rfl⟩,
    exact multiset.prod_eq_zero hrs, },
  refine multiset.induction _ (λ a s ih, _) s,
  { intro habs,
    simpa using habs, },
  { rw multiset.prod_cons,
    intro hprod,
    replace hprod := eq_zero_or_eq_zero_of_mul_eq_zero hprod,
    cases hprod with ha,
    { exact ⟨a, multiset.mem_cons_self a s, ha⟩ },
    { apply (ih hprod).imp _,
      rintros b ⟨hb₁, hb₂⟩,
      exact ⟨multiset.mem_cons_of_mem hb₁, hb₂⟩, }, },
end

end non_zero_divisors
