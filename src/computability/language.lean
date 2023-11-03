/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import algebra.free_monoid.basic
import algebra.hom.ring
import algebra.order.kleene
import data.list.join
import data.set.semiring

/-!
# Languages

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition and operations on formal languages over an alphabet. Note strings
are implemented as lists over the alphabet.
The operations in this file define a [Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra)
over the languages.
-/

open list set
open_locale computability

universes v

variables {α β γ : Type*}

/-- A language is a set of strings over an alphabet. -/
abbreviation language (α) := set_semiring (free_monoid α)

namespace language
variables {l m : language α} {a b x : free_monoid α}

/-- Zero language has no elements. -/
lemma zero_def : (0 : language α) = (∅ : set _) := rfl

/-- `1 : language α` contains only one element `1`. -/
lemma one_def : (1 : language α) = set.up ({1} : set (free_monoid α)) := rfl

/-- The sum of two languages is their union. -/
lemma add_def (l m : language α) : l + m = set.up (l ∪ m) := rfl

/-- The product of two languages `l` and `m` is the language made of the strings `x * y` where
`x ∈ l` and `y ∈ m`. -/
lemma mul_def (l m : language α) : l * m = set.up (image2 (*) l m) := rfl

/-- The Kleene star of a language `L` is the set of all strings which can be written by
concatenating strings from `L`. -/
instance : has_kstar (language α) :=
⟨λ l, {x | ∃ L : list (free_monoid α), x = L.prod ∧ ∀ y ∈ L, y ∈ l}⟩

lemma kstar_def (l : language α) :
  l∗ = {x | ∃ L : list (free_monoid α), x = L.prod ∧ ∀ y ∈ L, y ∈ l} :=
rfl

@[simp] lemma not_mem_zero (x : free_monoid α) : x ∉ (0 : language α) := id
@[simp] lemma mem_one (x : free_monoid α) : x ∈ (1 : language α) ↔ x = 1 := by refl
lemma nil_mem_one : (1 : free_monoid α) ∈ (1 : language α) := set.mem_singleton _
lemma mem_add (l m : language α) (x : free_monoid α) : x ∈ l + m ↔ x ∈ l ∨ x ∈ m := iff.rfl
lemma mem_mul : x ∈ l * m ↔ ∃ a b, a ∈ l ∧ b ∈ m ∧ a * b = x := mem_image2
lemma append_mem_mul : a ∈ l → b ∈ m → a * b ∈ l * m := mem_image2_of_mem
lemma mem_kstar : x ∈ l∗ ↔ ∃ L : list (free_monoid α), x = L.prod ∧ ∀ y ∈ L, y ∈ l := iff.rfl
lemma join_mem_kstar {L : list (free_monoid α)} (h : ∀ y ∈ L, y ∈ l) : L.prod ∈ l∗ := ⟨L, rfl, h⟩
lemma nil_mem_kstar (l : language α) : [] ∈ l∗ := ⟨[], rfl, λ _, false.elim⟩

@[simp] lemma add_self (l : language α) : l + l = l := sup_idem

/-- Maps the alphabet of a language. -/
def map (f : α → β) : language α →+* language β :=
{ to_fun := λ s, set.up (free_monoid.map f '' s.down),
  map_zero' := image_empty _,
  map_one' := image_singleton,
  map_add' := image_union _,
  map_mul' := λ _ _, image_image2_distrib $ map_append _ }

@[simp] lemma map_id (l : language α) : map id l = l := by simp [map]
@[simp] lemma map_map (g : β → γ) (f : α → β) (l : language α) : map g (map f l) = map (g ∘ f) l :=
by simp_rw [map, ring_hom.coe_mk, free_monoid.map_comp g f, monoid_hom.coe_comp,
  set_semiring.down_up, image_image]

@[simp, to_additive] lemma _root_.list.prod_filter_ne_one {α} [monoid α]
  [decidable_pred (λ x : α, x ≠ 1)] (l : list α) :
  (l.filter $ λ x : α, x ≠ 1).prod = l.prod :=
begin
  induction l with x xs ih,
  { simp },
  { by_cases h : x ≠ 1,
    { rw [filter_cons_of_pos, list.prod_cons, ih, list.prod_cons],
      exact h },
    { rw [filter_cons_of_neg, list.prod_cons, ih, not_ne_iff.mp h, one_mul],
      exact h } }
end

lemma kstar_def_nonempty (l : language α) :
  l∗ = {x | ∃ S : list (free_monoid α), x = S.prod ∧ ∀ y ∈ S, y ∈ l ∧ y ≠ (1 : free_monoid α)} :=
begin
  ext x,
  split,
  { rintro ⟨S, rfl, h⟩,
    classical,
    refine ⟨S.filter (λ l, ¬list.empty l.to_list), by simp [list.empty_iff_eq_nil], λ y hy, _⟩,
    rw [mem_filter, empty_iff_eq_nil] at hy,
    exact ⟨h y hy.1, hy.2⟩ },
  { rintro ⟨S, hx, h⟩,
    exact ⟨S, hx, λ y hy, (h y hy).1⟩ }
end

lemma le_iff (l m : language α) : l ≤ m ↔ l + m = m := sup_eq_right.symm

lemma le_mul_congr {l₁ l₂ m₁ m₂ : language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ * l₂ ≤ m₁ * m₂ :=
begin
  intros h₁ h₂ x hx,
  simp only [set.mem_up, mul_def, exists_and_distrib_left, mem_image2, image_prod] at hx ⊢,
  tauto
end

lemma le_add_congr {l₁ l₂ m₁ m₂ : language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ + l₂ ≤ m₁ + m₂ := sup_le_sup

lemma mem_supr {ι : Sort v} {l : ι → language α} {x : free_monoid α} :
  x ∈ (⨆ i, l i) ↔ ∃ i, x ∈ l i :=
mem_Union

lemma supr_mul {ι : Sort v} (l : ι → language α) (m : language α) :
  (⨆ i, l i) * m = ⨆ i, l i * m :=
image2_Union_left _ _ _

lemma mul_supr {ι : Sort v} (l : ι → language α) (m : language α) :
  m * (⨆ i, l i) = ⨆ i, m * l i :=
image2_Union_right _ _ _

lemma supr_add {ι : Sort v} [nonempty ι] (l : ι → language α) (m : language α) :
  (⨆ i, l i) + m = ⨆ i, l i + m := supr_sup

lemma add_supr {ι : Sort v} [nonempty ι] (l : ι → language α) (m : language α) :
  m + (⨆ i, l i) = ⨆ i, m + l i := sup_supr

lemma mem_pow {l : language α} {x : free_monoid α} {n : ℕ} :
  x ∈ l ^ n ↔ ∃ S : list (free_monoid α), x = S.prod ∧ S.length = n ∧ ∀ y ∈ S, y ∈ l :=
begin
  induction n with n ihn generalizing x,
  { simp only [mem_one, pow_zero, length_eq_zero],
    split,
    { rintro rfl, exact ⟨[], rfl, rfl, λ y h, h.elim⟩ },
    { rintro ⟨_, rfl, rfl, _⟩, refl } },
  { simp only [pow_succ, mem_mul, ihn],
    split,
    { rintro ⟨a, b, ha, ⟨S, rfl, rfl, hS⟩, rfl⟩,
      exact ⟨a :: S, prod_cons.symm, rfl, forall_mem_cons.2 ⟨ha, hS⟩⟩ },
    { rintro ⟨_|⟨a, S⟩, rfl, hn, hS⟩; cases hn,
      rw forall_mem_cons at hS,
      exact ⟨a, _, hS.1, ⟨S, rfl, rfl, hS.2⟩, prod_cons.symm⟩, } }
end

lemma kstar_eq_supr_pow (l : language α) : l∗ = ⨆ i : ℕ, l ^ i :=
begin
  ext x,
  simp only [mem_kstar, mem_supr, mem_pow],
  split,
  { rintro ⟨S, rfl, hS⟩, exact ⟨_, S, rfl, rfl, hS⟩ },
  { rintro ⟨_, S, rfl, rfl, hS⟩, exact ⟨S, rfl, hS⟩ }
end

@[simp] lemma map_kstar (f : α → β) (l : language α) : map f l∗ = (map f l)∗ :=
begin
  rw [kstar_eq_supr_pow, kstar_eq_supr_pow],
  simp_rw ←map_pow,
  exact image_Union,
end

lemma mul_self_kstar_comm (l : language α) : l∗ * l = l * l∗ :=
by simp only [kstar_eq_supr_pow, mul_supr, supr_mul, ← pow_succ, ← pow_succ']

@[simp] lemma one_add_self_mul_kstar_eq_kstar (l : language α) : 1 + l * l∗ = l∗ :=
begin
  simp only [kstar_eq_supr_pow, mul_supr, ← pow_succ, ← pow_zero l, add_eq_sup],
  exact sup_supr_nat_succ _
end

@[simp] lemma one_add_kstar_mul_self_eq_kstar (l : language α) : 1 + l∗ * l = l∗ :=
by rw [mul_self_kstar_comm, one_add_self_mul_kstar_eq_kstar]

instance : kleene_algebra (language α) :=
{ one_le_kstar := λ a l hl, ⟨[], hl, by simp⟩,
  mul_kstar_le_kstar := λ a, (one_add_self_mul_kstar_eq_kstar a).le.trans' le_sup_right,
  kstar_mul_le_kstar := λ a, (one_add_kstar_mul_self_eq_kstar a).le.trans' le_sup_right,
  kstar_mul_le_self := λ l m h, begin
    rw [kstar_eq_supr_pow, supr_mul],
    refine supr_le (λ n, _),
    induction n with n ih,
    { simp },
    rw [pow_succ', mul_assoc (l^n) l m],
    exact le_trans (le_mul_congr le_rfl h) ih,
  end,
  mul_kstar_le_self := λ l m h, begin
    rw [kstar_eq_supr_pow, mul_supr],
    refine supr_le (λ n, _),
    induction n with n ih,
    { simp },
    rw [pow_succ, ←mul_assoc m l (l^n)],
    exact le_trans (le_mul_congr h le_rfl) ih,
    end,
  ..set_semiring.idem_semiring, ..language.has_kstar }

end language
