/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import algebra.ring.basic
import algebra.algebra.basic
import algebra.group_power.basic

/-!  This file proves some general facts about even and odd elements of semirings. -/

variables {α β : Type*}

section semiring
variables [semiring α] [semiring β] {m n : α}

lemma even.add_even (hm : even m) (hn : even n) : even (m + n) :=
begin
  rcases hm with ⟨m, rfl⟩,
  rcases hn with ⟨n, rfl⟩,
  exact ⟨m + n, (mul_add _ _ _).symm⟩
end

lemma even.add_odd (hm : even m) (hn : odd n) : odd (m + n) :=
begin
  rcases hm with ⟨m, rfl⟩,
  rcases hn with ⟨n, rfl⟩,
  exact ⟨m + n, by rw [mul_add, add_assoc]⟩
end

lemma odd.add_even (hm : odd m) (hn : even n) : odd (m + n) :=
by { rw add_comm, exact hn.add_odd hm }

lemma odd.add_odd (hm : odd m) (hn : odd n) : even (m + n) :=
begin
  rcases hm with ⟨m, rfl⟩,
  rcases hn with ⟨n, rfl⟩,
  refine ⟨n + m + 1, _⟩,
  rw [←add_assoc, add_comm _ (2 * n), ←add_assoc, ←mul_add, add_assoc, mul_add _ (n + m), mul_one],
  refl
end

@[simp] lemma even_zero : even (0 : α) := ⟨0, (mul_zero _).symm⟩

@[simp] lemma odd_one : odd (1 : α) :=
⟨0, (zero_add _).symm.trans (congr_arg (+ (1 : α)) (mul_zero _).symm)⟩

@[simp] lemma even_two : even (2 : α) := ⟨1, (mul_one _).symm⟩

lemma even_two_mul (m : α) : even (2 * m) := ⟨m, rfl⟩

@[simp] lemma odd_two_mul_add_one (m : α) : odd (2 * m + 1) := ⟨m, rfl⟩

lemma add_monoid_hom.even (f : α →+ β) (hm : even m) : even (f m) :=
begin
  rcases hm with ⟨m, rfl⟩,
  exact ⟨f m, by simp [two_mul]⟩
end

lemma ring_hom.odd (f : α →+* β) (hm : odd m) : odd (f m) :=
begin
  rcases hm with ⟨m, rfl⟩,
  exact ⟨f m, by simp [two_mul]⟩
end

@[simp] lemma even.mul_right (hm : even m) (n) : even (m * n) :=
(add_monoid_hom.mul_right n).even hm

@[simp] lemma even.mul_left (hm : even m) (n) : even (n * m) :=
(add_monoid_hom.mul_left n).even hm

@[simp] lemma odd.mul_odd (hm : odd m) (hn : odd n) : odd (m * n) :=
begin
  rcases hm with ⟨m, rfl⟩,
  rcases hn with ⟨n, rfl⟩,
  refine ⟨2 * m * n + n + m, _⟩,
  rw [mul_add, add_mul, mul_one, ← add_assoc, one_mul, mul_assoc, ← mul_add, ← mul_add, ← mul_assoc,
    ← nat.cast_two, ← nat.cast_comm],
end

lemma even.pow_of_ne_zero (hm : even m) : ∀ {a : ℕ}, a ≠ 0 → even (m ^ a)
| 0       a0 := (a0 rfl).elim
| (a + 1) _  := by { rw pow_succ, exact hm.mul_right _ }

lemma odd.pow (hm : odd m) : ∀ {a : ℕ}, odd (m ^ a)
| 0       := by { rw pow_zero, exact odd_one }
| (a + 1) := by { rw pow_succ, exact hm.mul_odd odd.pow }

end semiring

section ring
variables [ring α] {m n : α}

@[simp] lemma odd_neg_one : odd (- 1 : α) := by simp

@[simp] lemma even_neg_two : even (- 2 : α) := by simp

lemma even.sub_even (hm : even m) (hn : even n) : even (m - n) :=
by { rw sub_eq_add_neg, exact hm.add_even ((even_neg n).mpr hn) }

theorem odd.sub_even (hm : odd m) (hn : even n) : odd (m - n) :=
by { rw sub_eq_add_neg, exact hm.add_even ((even_neg n).mpr hn) }

theorem even.sub_odd (hm : even m) (hn : odd n) : odd (m - n) :=
by { rw sub_eq_add_neg, exact hm.add_odd ((odd_neg n).mpr hn) }

lemma odd.sub_odd (hm : odd m) (hn : odd n) : even (m - n) :=
by { rw sub_eq_add_neg, exact hm.add_odd ((odd_neg n).mpr hn) }

end ring
