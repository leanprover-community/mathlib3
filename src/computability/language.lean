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

universes u v

variables {α : Type u} [dec : decidable_eq α]

/-- A language is a set of strings over an alphabet. -/
@[derive [has_mem (list α), has_singleton (list α), has_insert (list α), complete_lattice]]
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

@[simp] lemma mem_one (x : list α) : x ∈ (1 : language α) ↔ x = [] := by refl
@[simp] lemma mem_add (l m : language α) (x : list α) : x ∈ l + m ↔ x ∈ l ∨ x ∈ m :=
by simp [add_def]
lemma mem_mul (l m : language α) (x : list α) : x ∈ l * m ↔ ∃ a b, a ∈ l ∧ b ∈ m ∧ a ++ b = x :=
by simp [mul_def]
lemma mem_star (l : language α) (x : list α) :
  x ∈ l.star ↔ ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, y ∈ l :=
by refl

private lemma mul_assoc_lang (l m n : language α) : (l * m) * n = l * (m * n) :=
by { ext x, simp [mul_def], tauto {closer := `[subst_vars, simp *] } }

private lemma one_mul_lang (l : language α) : 1 * l = l :=
by { ext x, simp [mul_def, one_def], tauto {closer := `[subst_vars, simp [*]] } }

private lemma mul_one_lang (l : language α) : l * 1 = l :=
by { ext x, simp [mul_def, one_def], tauto {closer := `[subst_vars, simp *] } }

private lemma left_distrib_lang (l m n : language α) : l * (m + n) = (l * m) + (l * n) :=
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

private lemma right_distrib_lang (l m n : language α) : (l + m) * n = (l * n) + (m * n) :=
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
  mul_assoc := mul_assoc_lang,
  zero_mul := by simp [zero_def, mul_def],
  mul_zero := by simp [zero_def, mul_def],
  one := 1,
  one_mul := one_mul_lang,
  mul_one := mul_one_lang,
  left_distrib := left_distrib_lang,
  right_distrib := right_distrib_lang }

@[simp] lemma add_self (l : language α) : l + l = l := sup_idem

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

lemma le_iff (l m : language α) : l ≤ m ↔ l + m = m := sup_eq_right.symm

lemma le_mul_congr {l₁ l₂ m₁ m₂ : language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ * l₂ ≤ m₁ * m₂ :=
begin
  intros h₁ h₂ x hx,
  simp only [mul_def, exists_and_distrib_left, set.mem_image2, set.image_prod] at hx ⊢,
  tauto
end

lemma le_add_congr {l₁ l₂ m₁ m₂ : language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ + l₂ ≤ m₁ + m₂ := sup_le_sup

lemma supr_mul {ι : Sort v} (l : ι → language α) (m : language α) :
  (⨆ i, l i) * m = ⨆ i, l i * m :=
begin
  ext x,
  simp only [mem_mul, set.mem_Union, exists_and_distrib_left],
  tauto
end

lemma mul_supr {ι : Sort v} (l : ι → language α) (m : language α) :
  m * (⨆ i, l i) = ⨆ i, m * l i :=
begin
  ext x,
  simp only [mem_mul, set.mem_Union, exists_and_distrib_left],
  tauto
end

lemma supr_add {ι : Sort v} [nonempty ι] (l : ι → language α) (m : language α) :
  (⨆ i, l i) + m = ⨆ i, l i + m := supr_sup

lemma add_supr {ι : Sort v} [nonempty ι] (l : ι → language α) (m : language α) :
  m + (⨆ i, l i) = ⨆ i, m + l i := sup_supr

lemma star_eq_supr_pow (l : language α) : l.star = ⨆ i : ℕ, l ^ i :=
begin
  ext x,
  simp only [star_def, set.mem_Union, set.mem_set_of_eq],
  split,
  { revert x,
    rintros _ ⟨ S, rfl, hS ⟩,
    induction S with x S ih,
    { use 0,
      tauto },
    { specialize ih _,
      { exact λ y hy, hS _ (list.mem_cons_of_mem _ hy) },
      { cases ih with i ih,
        use i.succ,
        rw [pow_succ, mem_mul],
        exact ⟨ x, S.join, hS x (list.mem_cons_self _ _), ih, rfl ⟩ } } },
  { rintro ⟨ i, hx ⟩,
    induction i with i ih generalizing x,
    { rw [pow_zero, mem_one] at hx,
      subst hx,
      use [[]],
      tauto },
    { rw [pow_succ, mem_mul] at hx,
      rcases hx with ⟨ a, b, ha, hb, hx ⟩,
      rcases ih b hb with ⟨ S, hb, hS ⟩,
      use a :: S,
      rw list.join,
      refine ⟨hb ▸ hx.symm, λ y, or.rec (λ hy, _) (hS _)⟩,
      exact hy.symm ▸ ha } }
end

lemma mul_self_star_comm (l : language α) : l.star * l = l * l.star :=
by simp [star_eq_supr_pow, mul_supr, supr_mul, ← pow_succ, ← pow_succ']

@[simp] lemma one_add_self_mul_star_eq_star (l : language α) : 1 + l * l.star = l.star :=
begin
  rw [star_eq_supr_pow, mul_supr, add_def, supr_split_single (λ i, l ^ i) 0],
  have h : (⨆ (i : ℕ), l * l ^ i) = ⨆ (i : ℕ) (h : i ≠ 0), (λ (i : ℕ), l ^ i) i,
  { ext x,
    simp only [exists_prop, set.mem_Union, ne.def],
    split,
    { rintro ⟨ i, hi ⟩,
      use [i.succ, nat.succ_ne_zero i],
      rwa pow_succ },
    { rintro ⟨ (_ | i), h0, hi ⟩,
      { contradiction },
      use i,
      rwa ←pow_succ } },
  rw h,
  refl
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
