/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import data.set.lattice
import data.list.basic
import algebra.group_power.order

/-!
# Languages

This file contains the definition and operations on formal languages over an alphabet. Note strings
are implemented as lists over the alphabet.
The operations in this file define a [Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra)
over the languages.
-/

universes u v

variables {α : Type u}

/-- A language is a set of strings over an alphabet. -/
@[derive [has_mem (list α), has_singleton (list α), has_insert (list α), complete_boolean_algebra]]
def language (α) := set (list α)

namespace language

local attribute [reducible] language

/-- Zero language has no elements. -/
instance : has_zero (language α) := ⟨(∅ : set _)⟩
/-- `1 : language α` contains only one element `[]`. -/
instance : has_one (language α) := ⟨{[]}⟩

instance : inhabited (language α) := ⟨0⟩

/-- The sum of two languages is the union of  -/
instance : has_add (language α) := ⟨set.union⟩
instance : has_mul (language α) := ⟨set.image2 (++)⟩

lemma zero_def : (0 : language α) = (∅ : set _) := rfl
lemma one_def : (1 : language α) = {[]} := rfl

lemma add_def (l m : language α) : l + m = l ∪ m := rfl
lemma mul_def (l m : language α) : l * m = set.image2 (++) l m := rfl

/-- The star of a language `L` is the set of all strings which can be written by concatenating
  strings from `L`. -/
def star (l : language α) : language α :=
{ x | ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, y ∈ l}

lemma star_def (l : language α) :
  l.star = { x | ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, y ∈ l} := rfl

@[simp] lemma mem_one (x : list α) : x ∈ (1 : language α) ↔ x = [] := by refl
@[simp] lemma mem_add (l m : language α) (x : list α) : x ∈ l + m ↔ x ∈ l ∨ x ∈ m :=
by simp [add_def]
lemma mem_mul (l m : language α) (x : list α) : x ∈ l * m ↔ ∃ a b, a ∈ l ∧ b ∈ m ∧ a ++ b = x :=
by simp [mul_def]
lemma mem_star (l : language α) (x : list α) :
  x ∈ l.star ↔ ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, y ∈ l :=
iff.rfl

instance : semiring (language α) :=
{ add := (+),
  add_assoc := set.union_assoc,
  zero := 0,
  zero_add := set.empty_union,
  add_zero := set.union_empty,
  add_comm := set.union_comm,
  mul := (*),
  mul_assoc := λ l m n,
    by simp only [mul_def, set.image2_image2_left, set.image2_image2_right, list.append_assoc],
  zero_mul := by simp [zero_def, mul_def],
  mul_zero := by simp [zero_def, mul_def],
  one := 1,
  one_mul := λ l, by simp [mul_def, one_def],
  mul_one := λ l, by simp [mul_def, one_def],
  left_distrib := λ l m n, by simp only [mul_def, add_def, set.image2_union_right],
  right_distrib := λ l m n, by simp only [mul_def, add_def, set.image2_union_left] }

@[simp] lemma add_self (l : language α) : l + l = l := sup_idem

lemma star_def_nonempty (l : language α) :
  l.star = {x | ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, y ∈ l ∧ y ≠ []} :=
begin
  ext x,
  split,
  { rintro ⟨S, rfl, h⟩,
    refine ⟨S.filter (λ l, ¬list.empty l), by simp, λ y hy, _⟩,
    rw [list.mem_filter, list.empty_iff_eq_nil] at hy,
    exact ⟨h y hy.1, hy.2⟩ },
  { rintro ⟨S, hx, h⟩,
    exact ⟨S, hx, λ y hy, (h y hy).1⟩ }
end

lemma le_iff (l m : language α) : l ≤ m ↔ l + m = m := sup_eq_right.symm

lemma le_mul_congr {l₁ l₂ m₁ m₂ : language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ * l₂ ≤ m₁ * m₂ :=
begin
  intros h₁ h₂ x hx,
  simp only [mul_def, exists_and_distrib_left, set.mem_image2, set.image_prod] at hx ⊢,
  tauto
end

lemma le_add_congr {l₁ l₂ m₁ m₂ : language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ + l₂ ≤ m₁ + m₂ := sup_le_sup

lemma mem_supr {ι : Sort v} {l : ι → language α} {x : list α} :
  x ∈ (⨆ i, l i) ↔ ∃ i, x ∈ l i :=
set.mem_Union

lemma supr_mul {ι : Sort v} (l : ι → language α) (m : language α) :
  (⨆ i, l i) * m = ⨆ i, l i * m :=
set.image2_Union_left _ _ _

lemma mul_supr {ι : Sort v} (l : ι → language α) (m : language α) :
  m * (⨆ i, l i) = ⨆ i, m * l i :=
set.image2_Union_right _ _ _

lemma supr_add {ι : Sort v} [nonempty ι] (l : ι → language α) (m : language α) :
  (⨆ i, l i) + m = ⨆ i, l i + m := supr_sup

lemma add_supr {ι : Sort v} [nonempty ι] (l : ι → language α) (m : language α) :
  m + (⨆ i, l i) = ⨆ i, m + l i := sup_supr

lemma mem_pow {l : language α} {x : list α} {n : ℕ} :
  x ∈ l ^ n ↔ ∃ S : list (list α), x = S.join ∧ S.length = n ∧ ∀ y ∈ S, y ∈ l :=
begin
  induction n with n ihn generalizing x,
  { simp only [mem_one, pow_zero, list.length_eq_zero],
    split,
    { rintro rfl, exact ⟨[], rfl, rfl, λ y h, h.elim⟩ },
    { rintro ⟨_, rfl, rfl, _⟩, refl } },
  { simp only [pow_succ, mem_mul, ihn],
    split,
    { rintro ⟨a, b, ha, ⟨S, rfl, rfl, hS⟩, rfl⟩,
      exact ⟨a :: S, rfl, rfl, list.forall_mem_cons.2 ⟨ha, hS⟩⟩ },
    { rintro ⟨_|⟨a, S⟩, rfl, hn, hS⟩; cases hn,
      rw list.forall_mem_cons at hS,
      exact ⟨a, _, hS.1, ⟨S, rfl, rfl, hS.2⟩, rfl⟩ } }
end

lemma star_eq_supr_pow (l : language α) : l.star = ⨆ i : ℕ, l ^ i :=
begin
  ext x,
  simp only [mem_star, mem_supr, mem_pow],
  split,
  { rintro ⟨S, rfl, hS⟩, exact ⟨_, S, rfl, rfl, hS⟩ },
  { rintro ⟨_, S, rfl, rfl, hS⟩, exact ⟨S, rfl, hS⟩ }
end

lemma mul_self_star_comm (l : language α) : l.star * l = l * l.star :=
by simp only [star_eq_supr_pow, mul_supr, supr_mul, ← pow_succ, ← pow_succ']

@[simp] lemma one_add_self_mul_star_eq_star (l : language α) : 1 + l * l.star = l.star :=
begin
  simp only [star_eq_supr_pow, mul_supr, ← pow_succ, ← pow_zero l],
  exact sup_supr_nat_succ _
end

@[simp] lemma one_add_star_mul_self_eq_star (l : language α) : 1 + l.star * l = l.star :=
by rw [mul_self_star_comm, one_add_self_mul_star_eq_star]

lemma star_mul_le_right_of_mul_le_right (l m : language α) : l * m ≤ m → l.star * m ≤ m :=
begin
  intro h,
  rw [star_eq_supr_pow, supr_mul],
  refine supr_le _,
  intro n,
  induction n with n ih,
  { simp },
  rw [pow_succ', mul_assoc (l^n) l m],
  exact le_trans (le_mul_congr (le_refl _) h) ih,
end

lemma star_mul_le_left_of_mul_le_left (l m : language α) : m * l ≤ m → m * l.star ≤ m :=
begin
  intro h,
  rw [star_eq_supr_pow, mul_supr],
  refine supr_le _,
  intro n,
  induction n with n ih,
  { simp },
  rw [pow_succ, ←mul_assoc m l (l^n)],
  exact le_trans (le_mul_congr h (le_refl _)) ih
end

end language
