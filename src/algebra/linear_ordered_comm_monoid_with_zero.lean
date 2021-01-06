/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/

import algebra.ordered_monoid
import algebra.group_with_zero.basic

/-!
# Linearly ordered commutative monoids with a zero element adjoined

This file sets up a special class of linearly ordered commutative monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative group Γ and formally adjoining a zero element: Γ ∪ {0}.

The disadvantage is that a type such as `nnreal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.
-/

set_option old_structure_cmd true

/-- A linearly ordered commutative monoid with a zero element. -/
class linear_ordered_comm_monoid_with_zero (α : Type*)
  extends linear_order α, comm_monoid_with_zero α, ordered_comm_monoid α :=
(zero_le_one : (0:α) ≤ 1)
(lt_of_mul_lt_mul_left := λ x y z, by {
  -- type-class inference uses a meaningless `linear_order` without this!
  set l : linear_order α := {
    le := le,
    lt := lt,
    le_refl := ‹_›,
    le_trans := ‹_›,
    lt_iff_le_not_le := ‹_›,
    le_antisymm := ‹_›,
    le_total := ‹_›,
    decidable_le := ‹_›,
    decidable_eq := ‹_›,
    decidable_lt := ‹_› },
  apply imp_of_not_imp_not,
  intro h,
  apply not_lt_of_le,
  apply mul_le_mul_left,
  exact @le_of_not_lt _ l _ _ h })

variables {α : Type*}
variables {a b c d x y z : α}

variables [linear_ordered_comm_monoid_with_zero α]

lemma one_le_pow_of_one_le' {n : ℕ} (H : 1 ≤ x) : 1 ≤ x^n :=
begin
  induction n with n ih,
  { exact le_refl 1 },
  { exact one_le_mul H ih }
end

lemma pow_le_one_of_le_one {n : ℕ} (H : x ≤ 1) : x^n ≤ 1 :=
begin
  induction n with n ih,
  { exact le_refl 1 },
  { exact mul_le_one' H ih }
end

lemma eq_one_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) (H : x ^ n = 1) : x = 1 :=
begin
  rcases nat.exists_eq_succ_of_ne_zero hn with ⟨n, rfl⟩, clear hn,
  induction n with n ih,
  { simpa using H },
  { cases le_total x 1 with h,
    all_goals
    { have h1 := mul_le_mul_right' h (x ^ (n + 1)),
      rw pow_succ at H,
      rw [H, one_mul] at h1 },
    { have h2 := pow_le_one_of_le_one h,
      exact ih (le_antisymm h2 h1) },
    { have h2 := one_le_pow_of_one_le' h,
      exact ih (le_antisymm h1 h2) } }
end

lemma pow_eq_one_iff {n : ℕ} (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 :=
⟨eq_one_of_pow_eq_one hn, by { rintro rfl, exact one_pow _ }⟩

lemma one_le_pow_iff {n : ℕ} (hn : n ≠ 0) : 1 ≤ x^n ↔ 1 ≤ x :=
begin
  refine ⟨_, one_le_pow_of_one_le'⟩,
  contrapose!,
  intro h, apply lt_of_le_of_ne (pow_le_one_of_le_one (le_of_lt h)),
  rw [ne.def, pow_eq_one_iff hn],
  exact ne_of_lt h,
end

lemma pow_le_one_iff {n : ℕ} (hn : n ≠ 0) : x^n ≤ 1 ↔ x ≤ 1 :=
begin
  refine ⟨_, pow_le_one_of_le_one⟩,
  contrapose!,
  intro h, apply lt_of_le_of_ne (one_le_pow_of_one_le' (le_of_lt h)),
  rw [ne.def, eq_comm, pow_eq_one_iff hn],
  exact ne_of_gt h,
end

lemma zero_le_one' : (0 : α) ≤ 1 :=
linear_ordered_comm_monoid_with_zero.zero_le_one

@[simp] lemma zero_le' : 0 ≤ a :=
by simpa only [mul_zero, mul_one] using mul_le_mul_left' (@zero_le_one' α _) a

@[simp] lemma not_lt_zero' : ¬a < 0 :=
not_lt_of_le zero_le'

@[simp] lemma le_zero_iff : a ≤ 0 ↔ a = 0 :=
⟨λ h, le_antisymm h zero_le', λ h, h ▸ le_refl _⟩

lemma zero_lt_iff : 0 < a ↔ a ≠ 0 :=
⟨ne_of_gt, λ h, lt_of_le_of_ne zero_le' h.symm⟩

lemma ne_zero_of_lt (h : b < a) : a ≠ 0 :=
λ h1, not_lt_zero' $ show b < 0, from h1 ▸ h
