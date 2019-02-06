/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard

Fractional parts of reals (and more general floor_rings)
-/

-- note heavy imports. Is this bad? This is why I made a separate file
-- rather than dropping into archimedean.lean
import algebra.archimedean tactic.linarith tactic.abel

variables {α : Type*} [linear_ordered_ring α] [floor_ring α]

/-- The fractional part fract r of r is just r - ⌊r⌋ -/
def fract (r : α) : α := r - ⌊r⌋

-- Mathematical notation is usually {r}. Let's not even go there.
-- I have no notation currently.

@[simp] theorem fract_add_floor (r : α) : (⌊r⌋ : α) + fract r = r := by unfold fract;simp

theorem fract_nonneg (r : α) : 0 ≤ fract r :=
sub_nonneg.2 $ floor_le _

theorem fract_lt_one (r : α) : fract r < 1 :=
sub_lt.1 $ sub_one_lt_floor _

@[simp] lemma fract_zero : fract (0 : α) = 0 := by unfold fract; simp

@[simp] lemma fract_coe (z : ℤ) : fract (z : α) = 0 :=
by unfold fract; rw floor_coe; exact sub_self _

@[simp] lemma fract_floor (r : α) : fract (⌊r⌋ : α) = 0 := fract_coe _

@[simp] lemma floor_fract (r : α) : ⌊fract r⌋ = 0 :=
by rw floor_eq_iff; exact ⟨fract_nonneg _,
  by rw [int.cast_zero, zero_add]; exact fract_lt_one r⟩

theorem fract_eq_iff {r s : α} : fract r = s ↔ 0 ≤ s ∧ s < 1 ∧ ∃ z : ℤ, r - s = z :=
⟨λ h, by rw ←h; exact ⟨fract_nonneg _, fract_lt_one _,
  ⟨⌊r⌋, sub_sub_cancel _ _⟩⟩, begin
    intro h,
    show r - ⌊r⌋ = s, apply eq.symm,
    rw [eq_sub_iff_add_eq, add_comm, ←eq_sub_iff_add_eq],
    rcases h with ⟨hge, hlt, ⟨z, hz⟩⟩,
    rw [hz, int.cast_inj, floor_eq_iff, ←hz],
    clear hz, split; linarith {discharger := `[simp]}
  end⟩

theorem fract_eq_fract {r s : α} : fract r = fract s ↔ ∃ z : ℤ, r - s = z :=
⟨λ h, ⟨⌊r⌋ - ⌊s⌋, begin
  unfold fract at h, rw [int.cast_sub, sub_eq_sub_iff_sub_eq_sub.1 h],
 end⟩,
λ h, begin
  rcases h with ⟨z, hz⟩,
  rw fract_eq_iff,
  split, exact fract_nonneg _,
  split, exact fract_lt_one _,
  use z + ⌊s⌋,
  rw [eq_add_of_sub_eq hz, int.cast_add],
  unfold fract, simp
end⟩

@[simp] lemma fract_fract (r : α) : fract (fract r) = fract r :=
by rw fract_eq_fract; exact ⟨-⌊r⌋, by unfold fract;simp⟩

theorem fract_add (r s : α) : ∃ z : ℤ, fract (r + s) - fract r - fract s = z :=
⟨⌊r⌋ + ⌊s⌋ - ⌊r + s⌋, by unfold fract; simp⟩

theorem fract_mul_nat (r : α) (b : ℕ) : ∃ z : ℤ, fract r * b - fract (r * b) = z :=
begin
  induction b with c hc,
    use 0, simp,
  rcases hc with ⟨z, hz⟩,
  rw [nat.succ_eq_add_one, nat.cast_add, mul_add, mul_add, nat.cast_one, mul_one, mul_one],
  rcases fract_add (r * c) r with ⟨y, hy⟩,
  use z - y,
  rw [int.cast_sub, ←hz, ←hy],
  abel
end
