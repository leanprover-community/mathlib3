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
The operations in this file define a [Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra)
over the languages.
-/

universe u

variables {α : Type u} [dec : decidable_eq α]

/-- A language is a set of strings over an alphabet. -/
@[derive [has_mem (list α), has_singleton (list α), has_insert (list α)]]
def language (α) := set (list α)

namespace language

local attribute [reducible] language

instance : has_zero (language α) := ⟨(∅ : set _)⟩
instance : has_one (language α) := ⟨{[]}⟩

instance : inhabited (language α) := ⟨0⟩

instance : has_add (language α) := ⟨set.union⟩
instance : has_mul (language α) := ⟨λ l m, (l.prod m).image (λ p, p.1 ++ p.2)⟩

lemma zero_def : (0 : language α) = (∅ : set _) := rfl
lemma one_def : (1 : language α) = {[]} := rfl

lemma add_def (l m : language α) : l + m = l ∪ m := rfl
lemma mul_def (l m : language α) : l * m = (l.prod m).image (λ p, p.1 ++ p.2) := rfl

/-- The star of a language `L` is the set of all strings which can be written by concatenating
  strings from `L`. -/
def star (l : language α) : language α :=
{ x | ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, y ∈ l}

lemma star_def (l : language α) :
  l.star = { x | ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, y ∈ l} := rfl

private lemma mul_assoc (l m n : language α) : (l * m) * n = l * (m * n) :=
by { ext x, simp [mul_def], tauto {closer := `[subst_vars, simp *] } }

private lemma one_mul (l : language α) : 1 * l = l :=
by { ext x, simp [mul_def, one_def], tauto {closer := `[subst_vars, simp [*]] } }

private lemma mul_one (l : language α) : l * 1 = l :=
by { ext x, simp [mul_def, one_def], tauto {closer := `[subst_vars, simp *] } }

private lemma left_distrib (l m n : language α) : l * (m + n) = (l * m) + (l * n) :=
begin
  ext x,
  simp only [mul_def, add_def, exists_and_distrib_left, set.mem_image2, set.image_prod,
  set.mem_image, set.mem_prod, set.mem_union_eq, set.prod_union, prod.exists],
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
  add_assoc := by simp [add_def, set.union_assoc],
  zero := 0,
  zero_add := by simp [zero_def, add_def],
  add_zero := by simp [zero_def, add_def],
  add_comm := by simp [add_def, set.union_comm],
  mul := (*),
  mul_assoc := mul_assoc,
  zero_mul := by simp [zero_def, mul_def],
  mul_zero := by simp [zero_def, mul_def],
  one := 1,
  one_mul := one_mul,
  mul_one := mul_one,
  left_distrib := left_distrib,
  right_distrib := right_distrib }

@[simp] lemma add_self (l : language α) : l + l = l := by finish [add_def]

lemma star_def_nonempty (l : language α) :
  l.star = { x | ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, y ∈ l ∧ y ≠ []} :=
begin
  ext x,
  rw star_def,
  split,
  { rintro ⟨ S, hx, h ⟩,
    refine ⟨ S.filter (λ l, ¬list.empty l), _, _ ⟩,
    { rw hx,
      induction S with y S ih generalizing x,
      { refl },
      { rw list.filter,
        cases y with a y,
        { apply ih,
          { intros y hy,
            apply h,
            rw list.mem_cons_iff,
            right,
            assumption },
          { refl } },
        { simp only [true_and, list.join, eq_ff_eq_not_eq_tt, if_true, list.cons_append,
            list.empty, eq_self_iff_true],
          rw list.append_right_inj,
          simp only [eq_ff_eq_not_eq_tt, forall_eq] at ih,
          apply ih,
          intros y hy,
          apply h,
          rw list.mem_cons_iff,
          right,
          assumption } } },
    { intros y hy,
      simp only [eq_ff_eq_not_eq_tt, list.mem_filter] at hy,
      finish } },
  { rintro ⟨ S, hx, h ⟩,
    refine ⟨ S, hx, _ ⟩,
    finish }
end

end language
