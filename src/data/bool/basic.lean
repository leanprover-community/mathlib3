/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/

/-!
# booleans

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves various trivial lemmas about booleans and their
relation to decidable propositions.

## Notations

This file introduces the notation `!b` for `bnot b`, the boolean "not".

## Tags
bool, boolean, De Morgan
-/

prefix `!`:90 := bnot

namespace bool

-- TODO: duplicate of a lemma in core
theorem coe_sort_tt : coe_sort.{1 1} tt = true := coe_sort_tt

-- TODO: duplicate of a lemma in core
theorem coe_sort_ff : coe_sort.{1 1} ff = false := coe_sort_ff

-- TODO: duplicate of a lemma in core
theorem to_bool_true {h} : @to_bool true h = tt :=
to_bool_true_eq_tt h

-- TODO: duplicate of a lemma in core
theorem to_bool_false {h} : @to_bool false h = ff :=
to_bool_false_eq_ff h

@[simp] theorem to_bool_coe (b:bool) {h} : @to_bool b h = b :=
(show _ = to_bool b, by congr).trans (by cases b; refl)

theorem coe_to_bool (p : Prop) [decidable p] : to_bool p ↔ p := to_bool_iff _

@[simp] lemma of_to_bool_iff {p : Prop} [decidable p] : to_bool p ↔ p :=
⟨of_to_bool_true, _root_.to_bool_true⟩

@[simp] lemma tt_eq_to_bool_iff {p : Prop} [decidable p] : tt = to_bool p ↔ p :=
eq_comm.trans of_to_bool_iff

@[simp] lemma ff_eq_to_bool_iff {p : Prop} [decidable p] : ff = to_bool p ↔ ¬ p :=
eq_comm.trans (to_bool_ff_iff _)

@[simp] theorem to_bool_not (p : Prop) [decidable p] : to_bool (¬ p) = !(to_bool p) :=
by by_cases p; simp *

@[simp] theorem to_bool_and (p q : Prop) [decidable p] [decidable q] :
  to_bool (p ∧ q) = p && q :=
by by_cases p; by_cases q; simp *

@[simp] theorem to_bool_or (p q : Prop) [decidable p] [decidable q] :
  to_bool (p ∨ q) = p || q :=
by by_cases p; by_cases q; simp *

@[simp] theorem to_bool_eq {p q : Prop} [decidable p] [decidable q] :
  to_bool p = to_bool q ↔ (p ↔ q) :=
⟨λ h, (coe_to_bool p).symm.trans $ by simp [h], to_bool_congr⟩

lemma not_ff : ¬ ff := ff_ne_tt

@[simp] theorem default_bool : default = ff := rfl

theorem dichotomy (b : bool) : b = ff ∨ b = tt :=
by cases b; simp

@[simp] theorem forall_bool {p : bool → Prop} : (∀ b, p b) ↔ p ff ∧ p tt :=
⟨λ h, by simp [h], λ ⟨h₁, h₂⟩ b, by cases b; assumption⟩

@[simp] theorem exists_bool {p : bool → Prop} : (∃ b, p b) ↔ p ff ∨ p tt :=
⟨λ ⟨b, h⟩, by cases b; [exact or.inl h, exact or.inr h],
 λ h, by cases h; exact ⟨_, h⟩⟩

/-- If `p b` is decidable for all `b : bool`, then `∀ b, p b` is decidable -/
instance decidable_forall_bool {p : bool → Prop} [∀ b, decidable (p b)] : decidable (∀ b, p b) :=
decidable_of_decidable_of_iff and.decidable forall_bool.symm

/-- If `p b` is decidable for all `b : bool`, then `∃ b, p b` is decidable -/
instance decidable_exists_bool {p : bool → Prop} [∀ b, decidable (p b)] : decidable (∃ b, p b) :=
decidable_of_decidable_of_iff or.decidable exists_bool.symm

@[simp] theorem cond_ff {α} (t e : α) : cond ff t e = e := rfl

@[simp] theorem cond_tt {α} (t e : α) : cond tt t e = t := rfl

theorem cond_eq_ite {α} (b : bool) (t e : α) : cond b t e = if b then t else e := by cases b; simp

@[simp] theorem cond_to_bool {α} (p : Prop) [decidable p] (t e : α) :
  cond (to_bool p) t e = if p then t else e :=
by simp [cond_eq_ite]

@[simp] theorem cond_bnot {α} (b : bool) (t e : α) : cond (!b) t e = cond b e t :=
by cases b; refl

theorem bnot_ne_id : bnot ≠ id := λ h, ff_ne_tt $ congr_fun h tt

theorem coe_bool_iff : ∀ {a b : bool}, (a ↔ b) ↔ a = b := dec_trivial

theorem eq_tt_of_ne_ff : ∀ {a : bool}, a ≠ ff → a = tt := dec_trivial

theorem eq_ff_of_ne_tt : ∀ {a : bool}, a ≠ tt → a = ff := dec_trivial

theorem bor_comm : ∀ a b, a || b = b || a := dec_trivial

@[simp] theorem bor_assoc : ∀ a b c, (a || b) || c = a || (b || c) := dec_trivial

theorem bor_left_comm : ∀ a b c, a || (b || c) = b || (a || c) := dec_trivial

theorem bor_inl {a b : bool} (H : a) : a || b :=
by simp [H]

theorem bor_inr {a b : bool} (H : b) : a || b :=
by simp [H]

theorem band_comm : ∀ a b, a && b = b && a := dec_trivial

@[simp] theorem band_assoc : ∀ a b c, (a && b) && c = a && (b && c) := dec_trivial

theorem band_left_comm : ∀ a b c, a && (b && c) = b && (a && c) := dec_trivial

theorem band_elim_left : ∀ {a b : bool}, a && b → a := dec_trivial

theorem band_intro : ∀ {a b : bool}, a → b → a && b := dec_trivial

theorem band_elim_right : ∀ {a b : bool}, a && b → b := dec_trivial

lemma band_bor_distrib_left (a b c : bool) : a && (b || c) = a && b || a && c := by cases a; simp
lemma band_bor_distrib_right (a b c : bool) : (a || b) && c = a && c || b && c := by cases c; simp
lemma bor_band_distrib_left (a b c : bool) : a || b && c = (a || b) && (a || c) := by cases a; simp
lemma bor_band_distrib_right (a b c : bool) : a && b || c = (a || c) && (b || c) := by cases c; simp

@[simp] theorem bnot_ff : !ff = tt := rfl

@[simp] theorem bnot_tt : !tt = ff := rfl

lemma eq_bnot_iff : ∀ {a b : bool}, a = !b ↔ a ≠ b := dec_trivial
lemma bnot_eq_iff : ∀ {a b : bool}, !a = b ↔ a ≠ b := dec_trivial

@[simp] lemma not_eq_bnot : ∀ {a b : bool}, ¬a = !b ↔ a = b := dec_trivial
@[simp] lemma bnot_not_eq : ∀ {a b : bool}, ¬!a = b ↔ a = b := dec_trivial

lemma ne_bnot {a b : bool} : a ≠ !b ↔ a = b := not_eq_bnot
lemma bnot_ne {a b : bool} : !a ≠ b ↔ a = b := bnot_not_eq

lemma bnot_ne_self : ∀ b : bool, !b ≠ b := dec_trivial
lemma self_ne_bnot : ∀ b : bool, b ≠ !b := dec_trivial

lemma eq_or_eq_bnot : ∀ a b, a = b ∨ a = !b := dec_trivial

@[simp] theorem bnot_iff_not : ∀ {b : bool}, !b ↔ ¬b := dec_trivial

theorem eq_tt_of_bnot_eq_ff : ∀ {a : bool}, !a = ff → a = tt := dec_trivial

theorem eq_ff_of_bnot_eq_tt : ∀ {a : bool}, !a = tt → a = ff := dec_trivial

@[simp] lemma band_bnot_self : ∀ x, x && !x = ff := dec_trivial
@[simp] lemma bnot_band_self : ∀ x, !x && x = ff := dec_trivial
@[simp] lemma bor_bnot_self : ∀ x, x || !x = tt := dec_trivial
@[simp] lemma bnot_bor_self : ∀ x, !x || x = tt := dec_trivial

theorem bxor_comm : ∀ a b, bxor a b = bxor b a := dec_trivial
@[simp] theorem bxor_assoc : ∀ a b c, bxor (bxor a b) c = bxor a (bxor b c) := dec_trivial
theorem bxor_left_comm : ∀ a b c, bxor a (bxor b c) = bxor b (bxor a c) := dec_trivial
@[simp] theorem bxor_bnot_left : ∀ a, bxor (!a) a = tt := dec_trivial
@[simp] theorem bxor_bnot_right : ∀ a, bxor a (!a) = tt := dec_trivial
@[simp] theorem bxor_bnot_bnot : ∀ a b, bxor (!a) (!b) = bxor a b := dec_trivial
@[simp] theorem bxor_ff_left : ∀ a, bxor ff a = a := dec_trivial
@[simp] theorem bxor_ff_right : ∀ a, bxor a ff = a := dec_trivial

lemma band_bxor_distrib_left (a b c : bool) : a && (bxor b c) = bxor (a && b) (a && c) :=
by cases a; simp
lemma band_bxor_distrib_right (a b c : bool) : (bxor a b) && c = bxor (a && c) (b && c) :=
by cases c; simp

lemma bxor_iff_ne : ∀ {x y : bool}, bxor x y = tt ↔ x ≠ y := dec_trivial

/-! ### De Morgan's laws for booleans-/
@[simp] lemma bnot_band : ∀ (a b : bool), !(a && b) = !a || !b := dec_trivial
@[simp] lemma bnot_bor : ∀ (a b : bool), !(a || b) = !a && !b := dec_trivial

lemma bnot_inj : ∀ {a b : bool}, !a = !b → a = b := dec_trivial

instance : linear_order bool :=
{ le := λ a b, a = ff ∨ b = tt,
  le_refl := dec_trivial,
  le_trans := dec_trivial,
  le_antisymm := dec_trivial,
  le_total := dec_trivial,
  decidable_le := infer_instance,
  decidable_eq := infer_instance,
  max := bor,
  max_def := by { funext x y, revert x y, exact dec_trivial },
  min := band,
  min_def := by { funext x y, revert x y, exact dec_trivial } }

@[simp] lemma ff_le {x : bool} : ff ≤ x := or.intro_left _ rfl

@[simp] lemma le_tt {x : bool} : x ≤ tt := or.intro_right _ rfl

lemma lt_iff : ∀ {x y : bool}, x < y ↔ x = ff ∧ y = tt := dec_trivial

@[simp] lemma ff_lt_tt : ff < tt := lt_iff.2 ⟨rfl, rfl⟩

lemma le_iff_imp : ∀ {x y : bool}, x ≤ y ↔ (x → y) := dec_trivial

lemma band_le_left : ∀ x y : bool, x && y ≤ x := dec_trivial

lemma band_le_right : ∀ x y : bool, x && y ≤ y := dec_trivial

lemma le_band : ∀ {x y z : bool}, x ≤ y → x ≤ z → x ≤ y && z := dec_trivial

lemma left_le_bor : ∀ x y : bool, x ≤ x || y := dec_trivial

lemma right_le_bor : ∀ x y : bool, y ≤ x || y := dec_trivial

lemma bor_le : ∀ {x y z}, x ≤ z → y ≤ z → x || y ≤ z := dec_trivial

/-- convert a `bool` to a `ℕ`, `false -> 0`, `true -> 1` -/
def to_nat (b : bool) : ℕ :=
cond b 1 0

/-- convert a `ℕ` to a `bool`, `0 -> false`, everything else -> `true` -/
def of_nat (n : ℕ) : bool :=
to_bool (n ≠ 0)

lemma of_nat_le_of_nat {n m : ℕ} (h : n ≤ m) : of_nat n ≤ of_nat m :=
begin
  simp [of_nat];
    cases nat.decidable_eq n 0;
    cases nat.decidable_eq m 0;
    simp only [to_bool],
  { subst m, have h := le_antisymm h (nat.zero_le _),
    contradiction },
  { left, refl }
end

lemma to_nat_le_to_nat {b₀ b₁ : bool} (h : b₀ ≤ b₁) : to_nat b₀ ≤ to_nat b₁ :=
by cases h; subst h; [cases b₁, cases b₀]; simp [to_nat,nat.zero_le]

lemma of_nat_to_nat (b : bool) : of_nat (to_nat b) = b :=
by cases b; simp only [of_nat,to_nat]; exact dec_trivial

@[simp] lemma injective_iff {α : Sort*} {f : bool → α} : function.injective f ↔ f ff ≠ f tt :=
⟨λ Hinj Heq, ff_ne_tt (Hinj Heq),
  λ H x y hxy, by { cases x; cases y, exacts [rfl, (H hxy).elim, (H hxy.symm).elim, rfl] }⟩

/-- **Kaminski's Equation** -/
theorem apply_apply_apply (f : bool → bool) (x : bool) : f (f (f x)) = f x :=
by cases x; cases h₁ : f tt; cases h₂ : f ff; simp only [h₁, h₂]

end bool
