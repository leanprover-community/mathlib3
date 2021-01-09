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
@[derive [has_mem (list α), has_singleton (list α), has_insert (list α), has_le]]
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

lemma le_iff (l m : language α) : l ≤ m ↔ l + m = m :=
begin
  rw [set.le_eq_subset, add_def],
  split,
  { intro h,
    ext x,
    simp only [set.mem_union_eq, or_iff_right_iff_imp],
    tauto },
  { intro h,
    rw ←h,
    exact set.subset_union_left l m }
end

lemma one_add_lang_lang_star_le_lang_star (l : language α) : 1 + l*l.star ≤ l.star :=
begin
  rw [set.le_eq_subset, one_def, add_def, mul_def, star_def],
  intros x hx,
  simp only [exists_and_distrib_left, set.mem_image2, set.image_prod, set.mem_union_eq,
    set.mem_set_of_eq] at hx,
  cases hx,
  { rw [set.mem_singleton_iff] at hx,
    subst hx,
    use [[]],
    split,
    refl,
    tauto },
  { rcases hx with ⟨ a, ha, b, ⟨ ⟨ S, hb, hS ⟩, hx ⟩ ⟩,
    use a :: S,
    split,
    finish,
    rintros y (hy|hy);
    finish }
end

lemma one_add_lang_star_lang_le_lang_star (l : language α) : 1 + l.star*l ≤ l.star :=
begin
  rw [set.le_eq_subset, one_def, add_def, mul_def, star_def],
  intros x hx,
  simp only [exists_and_distrib_left, set.mem_image2, set.image_prod, set.mem_union_eq,
    set.mem_set_of_eq] at hx,
  cases hx,
  { rw [set.mem_singleton_iff] at hx,
    subst hx,
    use [[]],
    split,
    refl,
    tauto },
  { rcases hx with ⟨ b, ⟨ S, hb, hS ⟩, a, ha, hx ⟩,
    use S ++ [a],
    split,
    finish,
    simp only [list.mem_append, list.mem_singleton],
    rintros y (hy|hy);
    finish }
end

lemma star_mul_le_right_of_mul_le_right (l m : language α) : l*m ≤ m → l.star*m ≤ m :=
begin
  simp only [set.le_eq_subset, mul_def, star_def],
  intros hle x hx,
  simp only [exists_and_distrib_left, set.mem_image2, set.image_prod, set.mem_set_of_eq] at hx,
  simp only [set.image_prod, set.image2_subset_iff] at hle,
  rcases hx with ⟨ _, ⟨ S, rfl, hS ⟩, b, hb, rfl ⟩,
  induction S with a S ih,
  { assumption },
  { specialize hle a _ (S.join ++ b) _,
    { simp only [list.join, list.mem_cons_iff, list.append_assoc] at ⊢ hle,
      assumption },
    all_goals {simp only [forall_eq_or_imp, list.mem_cons_iff] at hS},
    { exact hS.1 },
    { cases hS,
      tauto } }
end

lemma star_mul_le_left_of_mul_le_left (l m : language α) : m*l ≤ m → m*l.star ≤ m :=
begin
  simp only [set.le_eq_subset, mul_def, star_def],
  intros hle x hx,
  simp only [exists_and_distrib_left, set.mem_image2, set.image_prod, set.mem_set_of_eq] at hx,
  simp only [set.image_prod, set.image2_subset_iff] at hle,
  rcases hx with ⟨ a, ha, _, ⟨ S, rfl, hS ⟩, rfl ⟩,
  induction S with b S ih,
  { simpa only [list.join, list.append_nil] },
  { specialize hle a _ (b ++ S.join) _,

    { simp only [list.join, list.mem_cons_iff, list.append_assoc] at ⊢ hle,
      assumption },
    { assumption },
end

end language
