/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import algebra.ring.basic

/-!  This file proves some general facts about even and odd elements of semirings. -/

variables {α β : Type*}

section semiring
variables [semiring α] [semiring β]

lemma even.add_even {m n : α} (hm : even m) (hn : even n) : even (m + n) :=
begin
  rcases hm with ⟨m, rfl⟩,
  rcases hn with ⟨n, rfl⟩,
  exact ⟨m + n, (mul_add _ _ _).symm⟩
end

lemma even.add_odd {m n : α} (hm : even m) (hn : odd n) : odd (m + n) :=
begin
  rcases hm with ⟨m, rfl⟩,
  rcases hn with ⟨n, rfl⟩,
  exact ⟨m + n, by rw [mul_add, add_assoc]⟩
end

lemma odd.add_even {m n : α} (hm : odd m) (hn : even n) : odd (m + n) :=
by { rw add_comm, exact hn.add_odd hm }

lemma odd.add_odd {m n : α} (hm : odd m) (hn : odd n) : even (m + n) :=
begin
  rcases hm with ⟨m, rfl⟩,
  rcases hn with ⟨n, rfl⟩,
  refine ⟨n + m + 1, _⟩,
  rw [←add_assoc, add_comm _ (2 * n), ←add_assoc, ←mul_add, add_assoc, mul_add _ (n + m), mul_one],
  refl
end

lemma even_to_even {m : α} (f : α →+ β) (hm : even m) : even (f m) :=
begin
  rcases hm with ⟨m, rfl⟩,
  exact ⟨f m, by simp [two_mul]⟩
end

lemma odd_to_odd {m : α} (f : α →+* β) (hm : odd m) : odd (f m) :=
begin
  rcases hm with ⟨m, rfl⟩,
  exact ⟨f m, by simp [two_mul]⟩
end

end semiring
