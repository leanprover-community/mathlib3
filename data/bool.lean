/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/

-- TODO(Jeremy): these used to be proved by rec_simp. Write a special tactic for these, or
-- get auto or super to do them.

namespace bool

  -- TODO(Jeremy): is this right?
  @[simp] theorem coe_tt : (↑tt : Prop) := dec_trivial

  theorem band_tt (a : bool) : a && tt = a  := by cases a; refl

  theorem tt_band (a : bool) : tt && a = a  := by cases a; refl

  theorem band_ff (a : bool) : a && ff = ff := by cases a; refl

  theorem ff_band (a : bool) : ff && a = ff := by cases a; refl

  theorem bor_tt (a : bool) : a || tt = tt  := by cases a; refl

  theorem tt_bor (a : bool) : tt || a = tt  := by cases a; refl

  theorem bor_ff (a : bool) : a || ff = a   := by cases a; refl

  theorem ff_bor (a : bool) : ff || a = a   := by cases a; refl

  attribute [simp] band_tt tt_band band_ff ff_band bor_tt tt_bor bor_ff ff_bor

  theorem band_eq_tt (a b : bool) : (a && b = tt) = (a = tt ∧ b = tt) :=
  by cases a; cases b; simp

  theorem band_eq_ff (a b : bool) : (a && b = ff) = (a = ff ∨ b = ff) :=
  by cases a; cases b; simp

  theorem bor_eq_tt (a b : bool) : (a || b = tt) = (a = tt ∨ b = tt) :=
  by cases a; cases b; simp

  theorem bor_eq_ff (a b : bool) : (a || b = ff) = (a = ff ∧ b = ff) :=
  by cases a; cases b; simp

  theorem dichotomy (b : bool) : b = ff ∨ b = tt :=
  by cases b; simp

  @[simp]
  theorem cond_ff {A : Type} (t e : A) : cond ff t e = e :=
  rfl

  @[simp]
  theorem cond_tt {A : Type} (t e : A) : cond tt t e = t :=
  rfl

  theorem eq_tt_of_ne_ff {a : bool} : a ≠ ff → a = tt :=
  by cases a; simp

  theorem eq_ff_of_ne_tt {a : bool} : a ≠ tt → a = ff :=
  by cases a; simp

  theorem absurd_of_eq_ff_of_eq_tt {B : Prop} {a : bool} (H₁ : a = ff) (H₂ : a = tt) : B :=
  by cases a; contradiction

  @[simp]
  theorem bor_comm (a b : bool) : a || b = b || a :=
  by cases a; cases b; simp

  @[simp]
  theorem bor_assoc (a b c : bool) : (a || b) || c = a || (b || c) :=
  by cases a; cases b; simp

  @[simp]
  theorem bor_left_comm (a b c : bool) : a || (b || c) = b || (a || c) :=
  by cases a; cases b; simp

  theorem or_of_bor_eq {a b : bool} : a || b = tt → a = tt ∨ b = tt :=
  begin cases a, simp, intro h, simp [h], simp end

  theorem bor_inl {a b : bool} (H : a = tt) : a || b = tt :=
  by simp [H]

  theorem bor_inr {a b : bool} (H : b = tt) : a || b = tt :=
  by simp [H]

  @[simp]
  theorem band_self (a : bool) : a && a = a :=
  by cases a; simp

  @[simp]
  theorem band_comm (a b : bool) : a && b = b && a :=
  by cases a; simp

  @[simp]
  theorem band_assoc (a b c : bool) : (a && b) && c = a && (b && c) :=
  by cases a; simp

  @[simp]
  theorem band_left_comm (a b c : bool) : a && (b && c) = b && (a && c) :=
  by cases a; simp

  theorem band_elim_left {a b : bool} (H : a && b = tt) : a = tt :=
  begin cases a, simp at H, simp [H] end

  theorem band_intro {a b : bool} (H₁ : a = tt) (H₂ : b = tt) : a && b = tt :=
  begin cases a, simp [H₁, H₂], simp [H₂] end

  theorem band_elim_right {a b : bool} (H : a && b = tt) : b = tt :=
  begin cases a, contradiction, simp at H, exact H end

  @[simp]
  theorem bnot_false : bnot ff = tt :=
  rfl

  @[simp]
  theorem bnot_true : bnot tt = ff :=
  rfl

  @[simp]
  theorem bnot_bnot (a : bool) : bnot (bnot a) = a :=
  by cases a; simp

  theorem eq_tt_of_bnot_eq_ff {a : bool} : bnot a = ff → a = tt :=
  by cases a; simp

  theorem eq_ff_of_bnot_eq_tt {a : bool} : bnot a = tt → a = ff :=
  by cases a; simp

  def bxor : bool → bool → bool
  | ff ff := ff
  | ff tt := tt
  | tt ff := tt
  | tt tt := ff

  @[simp]
  theorem ff_bxor_ff : bxor ff ff = ff := rfl
  @[simp]
  theorem ff_bxor_tt : bxor ff tt = tt := rfl
  @[simp]
  theorem tt_bxor_ff : bxor tt ff = tt := rfl
  @[simp]
  theorem tt_bxor_tt : bxor tt tt = ff := rfl

  @[simp]
  theorem bxor_self (a : bool) : bxor a a = ff :=
  by cases a; simp

  @[simp]
  theorem bxor_ff (a : bool) : bxor a ff = a :=
  by cases a; simp

  @[simp]
  theorem bxor_tt (a : bool) : bxor a tt = bnot a :=
  by cases a; simp

  @[simp]
  theorem ff_bxor (a : bool) : bxor ff a = a :=
  by cases a; simp

  @[simp]
  theorem tt_bxor (a : bool) : bxor tt a = bnot a :=
  by cases a; simp

  @[simp]
  theorem bxor_comm (a b : bool) : bxor a b = bxor b a :=
  by cases a; simp

  @[simp]
  theorem bxor_assoc (a b c : bool) : bxor (bxor a b) c = bxor a (bxor b c) :=
  by cases a; cases b; simp

  @[simp]
  theorem bxor_left_comm (a b c : bool) : bxor a (bxor b c) = bxor b (bxor a c) :=
  by cases a; cases b; simp

  instance forall_decidable {P : bool → Prop} [decidable_pred P] : decidable (∀b, P b) :=
  suffices P ff ∧ P tt ↔ _, from decidable_of_decidable_of_iff (by apply_instance) this,
  ⟨λ⟨pf, pt⟩ b, bool.rec_on b pf pt, λal, ⟨al _, al _⟩⟩
end bool
