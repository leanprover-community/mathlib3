/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson.
-/
import data.finset.basic

/-!
# Languages
This file contains the definition and operations on formal languages over an alphabet. Note strings
are implemented as lists over the alphabet.
-/

universe u

variables {α : Type u} [dec : decidable_eq α]

/-- A language is a set of strings over an alphabet. -/
@[derive [has_union, has_emptyc, has_mem (list α), has_singleton (list α)]]
def language (α) := set (list α)

namespace language

instance : inhabited (language α) := ⟨∅⟩

instance : has_zero (language α) := ⟨∅⟩
instance : has_one (language α) := ⟨{[]}⟩

instance : has_add (language α) := ⟨set.union⟩
instance : has_mul (language α) := ⟨λ l m, (l.prod m).image (λ p, p.1 ++ p.2)⟩

@[simp] lemma zero_def : (0 : language α) = ∅ := rfl
@[simp] lemma one_def : (1 : language α) = {[]} := rfl

@[simp] lemma add_def (l m : language α) : l + m = l ∪ m := rfl
@[simp] lemma mul_def (l m : language α) : l * m = (l.prod m).image (λ p, p.1 ++ p.2) := rfl

/-- The star of a language `L` is the set of all strings which can be written by concatenating
  strings from `L`. -/
def star (l : language α) : language α :=
{ x | ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, ¬(list.empty y) ∧ y ∈ l}

@[simp] lemma star_def (l : language α) :
  l.star = { x | ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, ¬(list.empty y) ∧ y ∈ l} := rfl

private lemma mul_assoc (l m n : language α) : (l * m) * n = l * (m * n) :=
by ext x; simp; tauto {closer := `[subst_vars, simp *]}

private lemma one_mul (l : language α) : 1 * l = l :=
by ext x; simp; tauto {closer := `[subst_vars, simp *]}

private lemma mul_one (l : language α) : l * 1 = l :=
by ext x; simp; tauto {closer := `[subst_vars, simp *]}

private lemma left_distrib (l m n : language α) : l * (m + n) = (l * m) + (l * n) :=
begin
  ext x,
  simp only [mul_def, set.mem_image, add_def, set.mem_prod, exists_and_distrib_left, set.mem_image2,
    set.image_prod, set.mem_union_eq, set.prod_union, prod.exists],
  split,
  { rintro ⟨ y, z, (⟨ hy, hz ⟩ | ⟨ hy, hz ⟩), hx ⟩,
    { left,
      exact ⟨ y, hy, z, hz, hx ⟩ },
    { right,
      exact ⟨ y, hy, z, hz, hx ⟩ } },
  { rintro (⟨ y, hy, z, hz, hx ⟩ | ⟨ y, hy, z, hz, hx ⟩);
    refine ⟨ y, z, _, hx ⟩,
    { left,
      exact ⟨ hy, hz ⟩ },
    { right,
      exact ⟨ hy, hz ⟩ } }
end

private lemma right_distrib (l m n : language α) : (l + m) * n = (l * n) + (m * n) :=
begin
  ext x,
  simp only [mul_def, set.mem_image, add_def, set.mem_prod, exists_and_distrib_left, set.mem_image2,
    set.image_prod, set.mem_union_eq, set.prod_union, prod.exists],
  split,
  { rintro ⟨ y, (hy | hy), z, hz, hx ⟩,
    { left,
      exact ⟨ y, hy, z, hz, hx ⟩ },
    { right,
      exact ⟨ y, hy, z, hz, hx ⟩ } },
  { rintro (⟨ y, hy, z, hz, hx ⟩ | ⟨ y, hy, z, hz, hx ⟩);
    refine ⟨ y, _, z, hz, hx ⟩,
    { left,
      exact hy },
    { right,
      exact hy } }
end

instance : semiring (language α) :=
{ add := (+),
  add_assoc := by simp [set.union_assoc],
  zero := 0,
  zero_add := by simp,
  add_zero := by simp,
  add_comm := by simp [set.union_comm],
  mul := (*),
  mul_assoc := mul_assoc,
  zero_mul := by simp,
  mul_zero := by simp,
  one := 1,
  one_mul := one_mul,
  mul_one := mul_one,
  left_distrib := left_distrib,
  right_distrib := right_distrib }

@[simp] lemma add_self (l : language α) : l + l = l := by finish

end language
