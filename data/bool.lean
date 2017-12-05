/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/

namespace bool

@[simp] theorem coe_sort_tt : coe_sort.{1 1} tt = true := eq_true_intro rfl

@[simp] theorem coe_sort_ff : coe_sort.{1 1} ff = false := eq_false_intro ff_ne_tt

@[simp] theorem to_bool_true {h} : @to_bool true h = tt :=
show _ = to_bool true, by congr

@[simp] theorem to_bool_false {h} : @to_bool false h = ff :=
show _ = to_bool false, by congr

@[simp] theorem coe_to_bool (p : Prop) [decidable p] : to_bool p ↔ p := to_bool_iff _

theorem dichotomy (b : bool) : b = ff ∨ b = tt :=
by cases b; simp

@[simp] theorem cond_ff {A : Type} (t e : A) : cond ff t e = e := rfl

@[simp] theorem cond_tt {A : Type} (t e : A) : cond tt t e = t := rfl

theorem eq_tt_of_ne_ff {a : bool} : a ≠ ff → a = tt :=
by cases a; simp

theorem eq_ff_of_ne_tt {a : bool} : a ≠ tt → a = ff :=
by cases a; simp

theorem absurd_of_eq_ff_of_eq_tt {B : Prop} {a : bool} (H₁ : a = ff) (H₂ : a = tt) : B :=
by subst a; contradiction

@[simp] theorem bor_comm (a b : bool) : a || b = b || a :=
by cases a; cases b; simp

@[simp] theorem bor_assoc (a b c : bool) : (a || b) || c = a || (b || c) :=
by cases a; cases b; simp

@[simp] theorem bor_left_comm (a b c : bool) : a || (b || c) = b || (a || c) :=
by cases a; cases b; simp

theorem bor_inl {a b : bool} (H : a) : a || b :=
by simp [H]

theorem bor_inr {a b : bool} (H : b) : a || b :=
by simp [H]

@[simp] theorem band_comm (a b : bool) : a && b = b && a :=
by cases a; simp

@[simp] theorem band_assoc (a b c : bool) : (a && b) && c = a && (b && c) :=
by cases a; simp

@[simp] theorem band_left_comm (a b c : bool) : a && (b && c) = b && (a && c) :=
by cases a; simp

theorem band_elim_left {a b : bool} (H : a && b = tt) : a = tt :=
begin cases a, simp at H, simp [H] end

theorem band_intro {a b : bool} (H₁ : a = tt) (H₂ : b = tt) : a && b = tt :=
begin cases a, simp [H₁, H₂], simp [H₂] end

theorem band_elim_right {a b : bool} (H : a && b = tt) : b = tt :=
begin cases a, contradiction, simp at H, exact H end

@[simp] theorem bnot_false : bnot ff = tt := rfl

@[simp] theorem bnot_true : bnot tt = ff := rfl

theorem eq_tt_of_bnot_eq_ff {a : bool} : bnot a = ff → a = tt :=
by cases a; simp

theorem eq_ff_of_bnot_eq_tt {a : bool} : bnot a = tt → a = ff :=
by cases a; simp

@[simp] theorem bxor_comm (a b : bool) : bxor a b = bxor b a :=
by cases a; simp

@[simp] theorem bxor_assoc (a b c : bool) : bxor (bxor a b) c = bxor a (bxor b c) :=
by cases a; cases b; simp

@[simp] theorem bxor_left_comm (a b c : bool) : bxor a (bxor b c) = bxor b (bxor a c) :=
by cases a; cases b; simp

end bool
