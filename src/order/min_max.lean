/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import order.lattice

/-!
# `max` and `min`

This file proves basic properties about maxima and minima on a `linear_order`.

## Tags

min, max
-/

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

attribute [simp] max_eq_left max_eq_right min_eq_left min_eq_right

variables [linear_order α] [linear_order β] {f : α → β} {s : set α} {a b c d : α}

-- translate from lattices to linear orders (sup → max, inf → min)
@[simp] lemma le_min_iff : c ≤ min a b ↔ c ≤ a ∧ c ≤ b := le_inf_iff
@[simp] lemma max_le_iff : max a b ≤ c ↔ a ≤ c ∧ b ≤ c := sup_le_iff
lemma max_le_max : a ≤ c → b ≤ d → max a b ≤ max c d := sup_le_sup
lemma min_le_min : a ≤ c → b ≤ d → min a b ≤ min c d := inf_le_inf
lemma le_max_of_le_left : a ≤ b → a ≤ max b c := le_sup_of_le_left
lemma le_max_of_le_right : a ≤ c → a ≤ max b c := le_sup_of_le_right
lemma lt_max_of_lt_left (h : a < b) : a < max b c := h.trans_le (le_max_left b c)
lemma lt_max_of_lt_right (h : a < c) : a < max b c := h.trans_le (le_max_right b c)
lemma min_le_of_left_le : a ≤ c → min a b ≤ c := inf_le_of_left_le
lemma min_le_of_right_le : b ≤ c → min a b ≤ c := inf_le_of_right_le
lemma min_lt_of_left_lt (h : a < c) : min a b < c := (min_le_left a b).trans_lt h
lemma min_lt_of_right_lt (h : b < c) : min a b < c := (min_le_right a b).trans_lt h
lemma max_min_distrib_left : max a (min b c) = min (max a b) (max a c) := sup_inf_left
lemma max_min_distrib_right : max (min a b) c = min (max a c) (max b c) := sup_inf_right
lemma min_max_distrib_left : min a (max b c) = max (min a b) (min a c) := inf_sup_left
lemma min_max_distrib_right : min (max a b) c = max (min a c) (min b c) := inf_sup_right
lemma min_le_max : min a b ≤ max a b := le_trans (min_le_left a b) (le_max_left a b)

@[simp] lemma min_eq_left_iff : min a b = a ↔ a ≤ b := inf_eq_left
@[simp] lemma min_eq_right_iff : min a b = b ↔ b ≤ a := inf_eq_right
@[simp] lemma max_eq_left_iff : max a b = a ↔ b ≤ a := sup_eq_left
@[simp] lemma max_eq_right_iff : max a b = b ↔ a ≤ b := sup_eq_right

/-- For elements `a` and `b` of a linear order, either `min a b = a` and `a ≤ b`,
    or `min a b = b` and `b < a`.
    Use cases on this lemma to automate linarith in inequalities -/
lemma min_cases (a b : α) : min a b = a ∧ a ≤ b ∨ min a b = b ∧ b < a :=
begin
  by_cases a ≤ b,
  { left,
    exact ⟨min_eq_left h, h⟩ },
  { right,
    exact ⟨min_eq_right (le_of_lt (not_le.mp h)), (not_le.mp h)⟩ }
end

/-- For elements `a` and `b` of a linear order, either `max a b = a` and `b ≤ a`,
    or `max a b = b` and `a < b`.
    Use cases on this lemma to automate linarith in inequalities -/
lemma max_cases (a b : α) : max a b = a ∧ b ≤ a ∨ max a b = b ∧ a < b :=
@min_cases (order_dual α) _ a b

lemma min_rec {p : α → Prop} {x y : α} (hx : x ≤ y → p x) (hy : y ≤ x → p y) : p (min x y) :=
(le_total x y).rec (λ h, (min_eq_left h).symm.subst (hx h))
  (λ h, (min_eq_right h).symm.subst (hy h))

lemma max_rec {p : α → Prop} {x y : α} (hx : y ≤ x → p x) (hy : x ≤ y → p y) : p (max x y) :=
@min_rec (order_dual α) _ _ _ _ hx hy

lemma min_rec' (p : α → Prop) {x y : α} (hx : p x) (hy : p y) : p (min x y) :=
min_rec (λ _, hx) (λ _, hy)

lemma max_rec' (p : α → Prop) {x y : α} (hx : p x) (hy : p y) : p (max x y) :=
max_rec (λ _, hx) (λ _, hy)

theorem min_choice (a b : α) : min a b = a ∨ min a b = b :=
by cases le_total a b; simp *

theorem max_choice (a b : α) : max a b = a ∨ max a b = b :=
@min_choice (order_dual α) _ a b

lemma min_eq_iff : min a b = c ↔ a = c ∧ a ≤ b ∨ b = c ∧ b ≤ a :=
begin
  split,
  { intro h,
    refine or.imp (λ h', _) (λ h', _) (le_total a b);
    exact ⟨by simpa [h'] using h, h'⟩ },
  { rintro (⟨rfl, h⟩|⟨rfl, h⟩);
    simp [h] }
end

lemma max_eq_iff : max a b = c ↔ a = c ∧ b ≤ a ∨ b = c ∧ a ≤ b :=
@min_eq_iff (order_dual α) _ a b c

/-- An instance asserting that `max a a = a` -/
instance max_idem : is_idempotent α max := by apply_instance -- short-circuit type class inference

/-- An instance asserting that `min a a = a` -/
instance min_idem : is_idempotent α min := by apply_instance -- short-circuit type class inference

@[simp] lemma max_lt_iff : max a b < c ↔ (a < c ∧ b < c) :=
⟨λ h, ⟨(le_max_left _ _).trans_lt h, (le_max_right _ _).trans_lt h⟩, and_imp.2 max_lt⟩

@[simp] lemma lt_min_iff : a < min b c ↔ (a < b ∧ a < c) :=
@max_lt_iff (order_dual α) _ _ _ _

@[simp] lemma lt_max_iff : a < max b c ↔ a < b ∨ a < c :=
begin
  symmetry, cases le_total b c with hbc hbc,
  { simpa only [max_eq_right hbc, or_iff_right_iff_imp] using flip lt_of_lt_of_le hbc },
  { simpa only [max_eq_left hbc, or_iff_left_iff_imp] using flip lt_of_lt_of_le hbc }
end

@[simp] lemma min_lt_iff : min a b < c ↔ a < c ∨ b < c :=
@lt_max_iff (order_dual α) _ _ _ _

@[simp] lemma le_max_iff : a ≤ max b c ↔ a ≤ b ∨ a ≤ c :=
begin
  symmetry, cases le_total b c with hbc hbc,
  { simpa only [max_eq_right hbc, or_iff_right_iff_imp] using flip le_trans hbc },
  { simpa only [max_eq_left hbc, or_iff_left_iff_imp] using flip le_trans hbc }
end

@[simp] lemma min_le_iff : min a b ≤ c ↔ a ≤ c ∨ b ≤ c :=
@le_max_iff (order_dual α) _ _ _ _

lemma min_lt_max : min a b < max a b ↔ a ≠ b := inf_lt_sup

lemma max_lt_max (h₁ : a < c) (h₂ : b < d) : max a b < max c d :=
by simp [lt_max_iff, max_lt_iff, *]

lemma min_lt_min (h₁ : a < c) (h₂ : b < d) : min a b < min c d :=
@max_lt_max (order_dual α) _ _ _ _ _ h₁ h₂

theorem min_right_comm (a b c : α) : min (min a b) c = min (min a c) b :=
inf_right_comm a b c

theorem max_right_comm (a b c : α) : max (max a b) c = max (max a c) b :=
sup_right_comm a b c

section

variables [semilattice_sup γ] [semilattice_inf δ]

lemma monotone_on.map_max_eq_sup {f : α → γ} (hf : monotone_on f s) (ha : a ∈ s) (hb : b ∈ s) :
  f (max a b) = f a ⊔ f b :=
by cases le_total a b;
  simp only [max_eq_right, max_eq_left, sup_of_le_left, sup_of_le_right, hf ha hb, hf hb ha, h]

lemma monotone_on.map_max (hf : monotone_on f s) (ha : a ∈ s) (hb : b ∈ s) :
  f (max a b) = max (f a) (f b) :=
hf.map_max_eq_sup ha hb

lemma monotone_on.map_min_eq_inf {f : α → δ} (hf : monotone_on f s) (ha : a ∈ s) (hb : b ∈ s) :
  f (min a b) = f a ⊓ f b :=
hf.dual.map_max_eq_sup ha hb

lemma monotone_on.map_min (hf : monotone_on f s) (ha : a ∈ s) (hb : b ∈ s) :
  f (min a b) = min (f a) (f b) :=
hf.dual.map_max ha hb

lemma antitone_on.map_max_eq_inf {f : α → δ} (hf : antitone_on f s) (ha : a ∈ s) (hb : b ∈ s) :
  f (max a b) = f a ⊓ f b :=
hf.dual_right.map_max_eq_sup ha hb

lemma antitone_on.map_max (hf : antitone_on f s) (ha : a ∈ s) (hb : b ∈ s) :
  f (max a b) = min (f a) (f b) :=
hf.map_max_eq_inf ha hb

lemma antitone_on.map_min_eq_sup {f : α → γ} (hf : antitone_on f s) (ha : a ∈ s) (hb : b ∈ s) :
  f (min a b) = f a ⊔ f b :=
hf.dual.map_max_eq_inf ha hb

lemma antitone_on.map_min (hf : antitone_on f s) (ha : a ∈ s) (hb : b ∈ s) :
  f (min a b) = max (f a) (f b) :=
hf.dual.map_max ha hb

lemma monotone.map_max_eq_sup {f : α → γ} (hf : monotone f) (a b : α) : f (max a b) = f a ⊔ f b :=
(hf.monotone_on set.univ).map_max_eq_sup trivial trivial

lemma monotone.map_max (hf : monotone f) (a b : α) : f (max a b) = max (f a) (f b) :=
hf.map_max_eq_sup a b

lemma monotone.map_min_eq_inf {f : α → δ} (hf : monotone f) (a b : α) : f (min a b) = f a ⊓ f b :=
hf.dual.map_max_eq_sup a b

lemma monotone.map_min (hf : monotone f) (a b : α) : f (min a b) = min (f a) (f b) :=
hf.dual.map_max a b

lemma antitone.map_max_eq_inf {f : α → δ} (hf : antitone f) (a b : α) : f (max a b) = f a ⊓ f b :=
hf.dual_right.map_max_eq_sup a b

lemma antitone.map_max (hf : antitone f) (a b : α) : f (max a b) = min (f a) (f b) :=
hf.map_max_eq_inf a b

lemma antitone.map_min_eq_sup {f : α → γ} (hf : antitone f) (a b : α) : f (min a b) = f a ⊔ f b :=
hf.dual.map_max_eq_inf a b

lemma antitone.map_min (hf : antitone f) (a b : α) : f (min a b) = max (f a) (f b) :=
hf.dual.map_max a b

end

lemma le_of_max_le_left {a b c : α} (h : max a b ≤ c) : a ≤ c :=
le_trans (le_max_left _ _) h

lemma le_of_max_le_right {a b c : α} (h : max a b ≤ c) : b ≤ c :=
le_trans (le_max_right _ _) h

lemma max_commutative : commutative (max : α → α → α) :=
max_comm

lemma max_associative : associative (max : α → α → α) :=
max_assoc

lemma max_left_commutative : left_commutative (max : α → α → α) :=
max_left_comm

lemma min_commutative : commutative (min : α → α → α) :=
min_comm

lemma min_associative : associative (min : α → α → α) :=
min_assoc

lemma min_left_commutative : left_commutative (min : α → α → α) :=
min_left_comm
