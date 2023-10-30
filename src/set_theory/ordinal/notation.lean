/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import set_theory.ordinal.principal

/-!
# Ordinal notation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Constructive ordinal arithmetic for ordinals below `ε₀`.

We define a type `onote`, with constructors `0 : onote` and `onote.oadd e n a` representing
`ω ^ e * n + a`.
We say that `o` is in Cantor normal form - `onote.NF o` - if either `o = 0` or
`o = ω ^ e * n + a` with `a < ω ^ e` and `a` in Cantor normal form.

The type `nonote` is the type of ordinals below `ε₀` in Cantor normal form.
Various operations (addition, subtraction, multiplication, power function)
are defined on `onote` and `nonote`.
-/

open ordinal order
open_locale ordinal -- get notation for `ω`

/-- Recursive definition of an ordinal notation. `zero` denotes the
  ordinal 0, and `oadd e n a` is intended to refer to `ω^e * n + a`.
  For this to be valid Cantor normal form, we must have the exponents
  decrease to the right, but we can't state this condition until we've
  defined `repr`, so it is a separate definition `NF`. -/
@[derive decidable_eq]
inductive onote : Type
| zero : onote
| oadd : onote → ℕ+ → onote → onote

namespace onote

/-- Notation for 0 -/
instance : has_zero onote := ⟨zero⟩
@[simp] theorem zero_def : zero = 0 := rfl

instance : inhabited onote := ⟨0⟩

/-- Notation for 1 -/
instance : has_one onote := ⟨oadd 0 1 0⟩

/-- Notation for ω -/
def omega : onote := oadd 1 1 0

/-- The ordinal denoted by a notation -/
@[simp] noncomputable def repr : onote → ordinal.{0}
| 0 := 0
| (oadd e n a) := ω ^ repr e * n + repr a

/-- Auxiliary definition to print an ordinal notation -/
def to_string_aux1 (e : onote) (n : ℕ) (s : string) : string :=
if e = 0 then _root_.to_string n else
(if e = 1 then "ω" else "ω^(" ++ s ++ ")") ++
if n = 1 then "" else "*" ++ _root_.to_string n

/-- Print an ordinal notation -/
def to_string : onote → string
| zero := "0"
| (oadd e n 0) := to_string_aux1 e n (to_string e)
| (oadd e n a) := to_string_aux1 e n (to_string e) ++ " + " ++ to_string a

/-- Print an ordinal notation -/
def repr' : onote → string
| zero := "0"
| (oadd e n a) := "(oadd " ++ repr' e ++ " " ++ _root_.to_string (n:ℕ) ++ " " ++ repr' a ++ ")"

instance : has_to_string onote := ⟨to_string⟩
instance : has_repr onote := ⟨repr'⟩

instance : preorder onote :=
{ le       := λ x y, repr x ≤ repr y,
  lt       := λ x y, repr x < repr y,
  le_refl  := λ a, @le_refl ordinal _ _,
  le_trans := λ a b c, @le_trans ordinal _ _ _ _,
  lt_iff_le_not_le := λ a b, @lt_iff_le_not_le ordinal _ _ _ }

theorem lt_def {x y : onote} : x < y ↔ repr x < repr y := iff.rfl
theorem le_def {x y : onote} : x ≤ y ↔ repr x ≤ repr y := iff.rfl

/-- Convert a `nat` into an ordinal -/
@[simp] def of_nat : ℕ → onote
| 0            := 0
| (nat.succ n) := oadd 0 n.succ_pnat 0

@[simp] theorem of_nat_one : of_nat 1 = 1 := rfl

@[simp] theorem repr_of_nat (n : ℕ) : repr (of_nat n) = n :=
by cases n; simp

@[simp] theorem repr_one : repr 1 = 1 :=
by simpa using repr_of_nat 1

theorem omega_le_oadd (e n a) : ω ^ repr e ≤ repr (oadd e n a) :=
begin
  unfold repr,
  refine le_trans _ (le_add_right _ _),
  simpa using (mul_le_mul_iff_left $ opow_pos (repr e) omega_pos).2 (nat_cast_le.2 n.2)
end

theorem oadd_pos (e n a) : 0 < oadd e n a :=
@lt_of_lt_of_le _ _ _ _ _ (opow_pos _ omega_pos)
  (omega_le_oadd _ _ _)

/-- Compare ordinal notations -/
def cmp : onote → onote → ordering
| 0 0 := ordering.eq
| _ 0 := ordering.gt
| 0 _ := ordering.lt
| o₁@(oadd e₁ n₁ a₁) o₂@(oadd e₂ n₂ a₂) :=
  (cmp e₁ e₂).or_else $ (_root_.cmp (n₁:ℕ) n₂).or_else (cmp a₁ a₂)

theorem eq_of_cmp_eq : ∀ {o₁ o₂}, cmp o₁ o₂ = ordering.eq → o₁ = o₂
| 0            0 h := rfl
| (oadd e n a) 0 h := by injection h
| 0 (oadd e n a) h := by injection h
| o₁@(oadd e₁ n₁ a₁) o₂@(oadd e₂ n₂ a₂) h := begin
  revert h, simp only [cmp],
  cases h₁ : cmp e₁ e₂; intro h; try {cases h},
  obtain rfl := eq_of_cmp_eq h₁,
  revert h, cases h₂ : _root_.cmp (n₁:ℕ) n₂; intro h; try {cases h},
  obtain rfl := eq_of_cmp_eq h,
  rw [_root_.cmp, cmp_using_eq_eq] at h₂,
  obtain rfl := subtype.eq (eq_of_incomp h₂),
  simp
end

protected theorem zero_lt_one : (0 : onote) < 1 :=
by rw [lt_def, repr, repr_one]; exact zero_lt_one

/-- `NF_below o b` says that `o` is a normal form ordinal notation
  satisfying `repr o < ω ^ b`. -/
inductive NF_below : onote → ordinal.{0} → Prop
| zero {b} : NF_below 0 b
| oadd' {e n a eb b} : NF_below e eb →
  NF_below a (repr e) → repr e < b → NF_below (oadd e n a) b

/-- A normal form ordinal notation has the form

     ω ^ a₁ * n₁ + ω ^ a₂ * n₂ + ... ω ^ aₖ * nₖ
  where `a₁ > a₂ > ... > aₖ` and all the `aᵢ` are
  also in normal form.

  We will essentially only be interested in normal form
  ordinal notations, but to avoid complicating the algorithms
  we define everything over general ordinal notations and
  only prove correctness with normal form as an invariant. -/
class NF (o : onote) : Prop := (out : Exists (NF_below o))
attribute [pp_nodot] NF

instance NF.zero : NF 0 := ⟨⟨0, NF_below.zero⟩⟩

theorem NF_below.oadd {e n a b} : NF e →
  NF_below a (repr e) → repr e < b → NF_below (oadd e n a) b
| ⟨⟨eb, h⟩⟩ := NF_below.oadd' h

theorem NF_below.fst {e n a b} (h : NF_below (oadd e n a) b) : NF e :=
by cases h with _ _ _ _ eb _ h₁ h₂ h₃; exact ⟨⟨_, h₁⟩⟩

theorem NF.fst {e n a} : NF (oadd e n a) → NF e
| ⟨⟨b, h⟩⟩ := h.fst

theorem NF_below.snd {e n a b} (h : NF_below (oadd e n a) b) : NF_below a (repr e) :=
by cases h with _ _ _ _ eb _ h₁ h₂ h₃; exact h₂

theorem NF.snd' {e n a} : NF (oadd e n a) → NF_below a (repr e)
| ⟨⟨b, h⟩⟩ := h.snd

theorem NF.snd {e n a} (h : NF (oadd e n a)) : NF a :=
⟨⟨_, h.snd'⟩⟩

theorem NF.oadd {e a} (h₁ : NF e) (n)
  (h₂ : NF_below a (repr e)) : NF (oadd e n a) :=
⟨⟨_, NF_below.oadd h₁ h₂ (lt_succ _)⟩⟩

instance NF.oadd_zero (e n) [h : NF e] : NF (oadd e n 0) :=
h.oadd _ NF_below.zero

theorem NF_below.lt {e n a b} (h : NF_below (oadd e n a) b) : repr e < b :=
by cases h with _ _ _ _ eb _ h₁ h₂ h₃; exact h₃

theorem NF_below_zero : ∀ {o}, NF_below o 0 ↔ o = 0
| 0            := ⟨λ _, rfl, λ _, NF_below.zero⟩
| (oadd e n a) := ⟨λ h, (not_le_of_lt h.lt).elim (ordinal.zero_le _),
                   λ e, e.symm ▸ NF_below.zero⟩

theorem NF.zero_of_zero {e n a} (h : NF (oadd e n a)) (e0 : e = 0) : a = 0 :=
by simpa [e0, NF_below_zero] using h.snd'

theorem NF_below.repr_lt {o b} (h : NF_below o b) : repr o < ω ^ b :=
begin
  induction h with _ e n a eb b h₁ h₂ h₃ _ IH,
  { exact opow_pos _ omega_pos },
  { rw repr,
    apply ((add_lt_add_iff_left _).2 IH).trans_le,
    rw ← mul_succ,
    apply (mul_le_mul_left' (succ_le_of_lt (nat_lt_omega _)) _).trans,
    rw ← opow_succ,
    exact opow_le_opow_right omega_pos (succ_le_of_lt h₃) }
end

theorem NF_below.mono {o b₁ b₂} (bb : b₁ ≤ b₂) (h : NF_below o b₁) : NF_below o b₂ :=
begin
  induction h with _ e n a eb b h₁ h₂ h₃ _ IH; constructor,
  exacts [h₁, h₂, lt_of_lt_of_le h₃ bb]
end

theorem NF.below_of_lt {e n a b} (H : repr e < b) : NF (oadd e n a) → NF_below (oadd e n a) b
| ⟨⟨b', h⟩⟩ := by cases h with _ _ _ _ eb _ h₁ h₂ h₃;
  exact NF_below.oadd' h₁ h₂ H

theorem NF.below_of_lt' : ∀ {o b}, repr o < ω ^ b → NF o → NF_below o b
| 0            b H _ := NF_below.zero
| (oadd e n a) b H h := h.below_of_lt $ (opow_lt_opow_iff_right one_lt_omega).1 $
    (lt_of_le_of_lt (omega_le_oadd _ _ _) H)

theorem NF_below_of_nat : ∀ n, NF_below (of_nat n) 1
| 0            := NF_below.zero
| (nat.succ n) := NF_below.oadd NF.zero NF_below.zero zero_lt_one

instance NF_of_nat (n) : NF (of_nat n) := ⟨⟨_, NF_below_of_nat n⟩⟩

instance NF_one : NF 1 := by rw ← of_nat_one; apply_instance

theorem oadd_lt_oadd_1 {e₁ n₁ o₁ e₂ n₂ o₂} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂) :
  oadd e₁ n₁ o₁ < oadd e₂ n₂ o₂ :=
@lt_of_lt_of_le _ _ _ _ _ ((h₁.below_of_lt h).repr_lt) (omega_le_oadd _ _ _)

theorem oadd_lt_oadd_2 {e o₁ o₂ : onote} {n₁ n₂ : ℕ+}
  (h₁ : NF (oadd e n₁ o₁)) (h : (n₁:ℕ) < n₂) : oadd e n₁ o₁ < oadd e n₂ o₂ :=
begin
  simp [lt_def],
  refine lt_of_lt_of_le ((add_lt_add_iff_left _).2 h₁.snd'.repr_lt)
    (le_trans _ (le_add_right _ _)),
  rwa [← mul_succ, mul_le_mul_iff_left (opow_pos _ omega_pos), succ_le_iff, nat_cast_lt]
end

theorem oadd_lt_oadd_3 {e n a₁ a₂} (h : a₁ < a₂) :
  oadd e n a₁ < oadd e n a₂ :=
begin
  rw lt_def, unfold repr,
  exact add_lt_add_left h _
end

theorem cmp_compares : ∀ (a b : onote) [NF a] [NF b], (cmp a b).compares a b
| 0 0 h₁ h₂ := rfl
| (oadd e n a) 0 h₁ h₂ := oadd_pos _ _ _
| 0 (oadd e n a) h₁ h₂ := oadd_pos _ _ _
| o₁@(oadd e₁ n₁ a₁) o₂@(oadd e₂ n₂ a₂) h₁ h₂ := begin
    rw cmp,
    have IHe := @cmp_compares _ _ h₁.fst h₂.fst,
    cases cmp e₁ e₂,
    case ordering.lt { exact oadd_lt_oadd_1 h₁ IHe },
    case ordering.gt { exact oadd_lt_oadd_1 h₂ IHe },
    change e₁ = e₂ at IHe, subst IHe,
    unfold _root_.cmp, cases nh : cmp_using (<) (n₁:ℕ) n₂,
    case ordering.lt
    { rw cmp_using_eq_lt at nh, exact oadd_lt_oadd_2 h₁ nh },
    case ordering.gt
    { rw cmp_using_eq_gt at nh, exact oadd_lt_oadd_2 h₂ nh },
    rw cmp_using_eq_eq at nh,
    obtain rfl := subtype.eq (eq_of_incomp nh),
    have IHa := @cmp_compares _ _ h₁.snd h₂.snd,
    cases cmp a₁ a₂,
    case ordering.lt { exact oadd_lt_oadd_3 IHa },
    case ordering.gt { exact oadd_lt_oadd_3 IHa },
    change a₁ = a₂ at IHa, subst IHa, exact rfl
  end

theorem repr_inj {a b} [NF a] [NF b] : repr a = repr b ↔ a = b :=
⟨match cmp a b, cmp_compares a b with
 | ordering.lt, (h : repr a < repr b), e := (ne_of_lt h e).elim
 | ordering.gt, (h : repr a > repr b), e := (ne_of_gt h e).elim
 | ordering.eq, h, e := h
 end, congr_arg _⟩

theorem NF.of_dvd_omega_opow {b e n a} (h : NF (oadd e n a)) (d : ω ^ b ∣ repr (oadd e n a)) :
  b ≤ repr e ∧ ω ^ b ∣ repr a :=
begin
  have := mt repr_inj.1 (λ h, by injection h : oadd e n a ≠ 0),
  have L := le_of_not_lt (λ l, not_le_of_lt (h.below_of_lt l).repr_lt (le_of_dvd this d)),
  simp at d,
  exact ⟨L, (dvd_add_iff $ (opow_dvd_opow _ L).mul_right _).1 d⟩
end

theorem NF.of_dvd_omega {e n a} (h : NF (oadd e n a)) :
   ω ∣ repr (oadd e n a) → repr e ≠ 0 ∧ ω ∣ repr a :=
by rw [← opow_one ω, ← one_le_iff_ne_zero]; exact h.of_dvd_omega_opow

/-- `top_below b o` asserts that the largest exponent in `o`, if
  it exists, is less than `b`. This is an auxiliary definition
  for decidability of `NF`. -/
def top_below (b) : onote → Prop
| 0            := true
| (oadd e n a) := cmp e b = ordering.lt

instance decidable_top_below : decidable_rel top_below :=
by intros b o; cases o; delta top_below; apply_instance

theorem NF_below_iff_top_below {b} [NF b] : ∀ {o},
  NF_below o (repr b) ↔ NF o ∧ top_below b o
| 0            := ⟨λ h, ⟨⟨⟨_, h⟩⟩, trivial⟩, λ _, NF_below.zero⟩
| (oadd e n a) :=
  ⟨λ h, ⟨⟨⟨_, h⟩⟩, (@cmp_compares _ b h.fst _).eq_lt.2 h.lt⟩,
   λ ⟨h₁, h₂⟩, h₁.below_of_lt $ (@cmp_compares _ b h₁.fst _).eq_lt.1 h₂⟩

instance decidable_NF : decidable_pred NF
| 0            := is_true NF.zero
| (oadd e n a) := begin
  have := decidable_NF e,
  have := decidable_NF a, resetI,
  apply decidable_of_iff (NF e ∧ NF a ∧ top_below e a),
  abstract
  { rw ← and_congr_right (λ h, @NF_below_iff_top_below _ h _),
    exact ⟨λ ⟨h₁, h₂⟩, NF.oadd h₁ n h₂, λ h, ⟨h.fst, h.snd'⟩⟩ },
end

/-- Addition of ordinal notations (correct only for normal input) -/
def add : onote → onote → onote
| 0            o := o
| (oadd e n a) o := match add a o with
  | 0 := oadd e n 0
  | o'@(oadd e' n' a') := match cmp e e' with
    | ordering.lt := o'
    | ordering.eq := oadd e (n + n') a'
    | ordering.gt := oadd e n o'
    end
  end

instance : has_add onote := ⟨add⟩

@[simp] theorem zero_add (o : onote) : 0 + o = o := rfl
theorem oadd_add (e n a o) : oadd e n a + o = add._match_1 e n (a + o) := rfl

/-- Subtraction of ordinal notations (correct only for normal input) -/
def sub : onote → onote → onote
| 0 o := 0
| o 0 := o
| o₁@(oadd e₁ n₁ a₁) (oadd e₂ n₂ a₂) := match cmp e₁ e₂ with
  | ordering.lt := 0
  | ordering.gt := o₁
  | ordering.eq := match (n₁:ℕ) - n₂ with
    | 0            := if n₁ = n₂ then sub a₁ a₂ else 0
    | (nat.succ k) := oadd e₁ k.succ_pnat a₁
  end
end

instance : has_sub onote := ⟨sub⟩

theorem add_NF_below {b} : ∀ {o₁ o₂}, NF_below o₁ b → NF_below o₂ b → NF_below (o₁ + o₂) b
| 0            o h₁ h₂ := h₂
| (oadd e n a) o h₁ h₂ := begin
  have h' := add_NF_below (h₁.snd.mono $ le_of_lt h₁.lt) h₂,
  simp [oadd_add], cases a + o with e' n' a',
  { exact NF_below.oadd h₁.fst NF_below.zero h₁.lt },
  simp [add], have := @cmp_compares _ _ h₁.fst h'.fst,
  cases cmp e e'; simp [add],
  { exact h' },
  { simp at this, subst e',
    exact NF_below.oadd h'.fst h'.snd h'.lt },
  { exact NF_below.oadd h₁.fst (NF.below_of_lt this ⟨⟨_, h'⟩⟩) h₁.lt }
end

instance add_NF (o₁ o₂) : ∀ [NF o₁] [NF o₂], NF (o₁ + o₂)
| ⟨⟨b₁, h₁⟩⟩ ⟨⟨b₂, h₂⟩⟩ := ⟨(le_total b₁ b₂).elim
  (λ h, ⟨b₂, add_NF_below (h₁.mono h) h₂⟩)
  (λ h, ⟨b₁, add_NF_below h₁ (h₂.mono h)⟩)⟩

@[simp] theorem repr_add : ∀ o₁ o₂ [NF o₁] [NF o₂], repr (o₁ + o₂) = repr o₁ + repr o₂
| 0            o h₁ h₂ := by simp
| (oadd e n a) o h₁ h₂ := begin
  haveI := h₁.snd, have h' := repr_add a o,
  conv at h' in (_+o) {simp [(+)]},
  have nf := onote.add_NF a o,
  conv at nf in (_+o) {simp [(+)]},
  conv in (_+o) {simp [(+), add]},
  cases add a o with e' n' a'; simp [add, h'.symm, add_assoc],
  have := h₁.fst, haveI := nf.fst, have ee := cmp_compares e e',
  cases cmp e e'; simp [add],
  { rw [← add_assoc, @add_absorp _ (repr e') (ω ^ repr e' * (n':ℕ))],
    { have := (h₁.below_of_lt ee).repr_lt, unfold repr at this,
      exact lt_of_le_of_lt (le_add_right _ _) this },
    { simpa using (mul_le_mul_iff_left $
        opow_pos (repr e') omega_pos).2 (nat_cast_le.2 n'.pos) } },
  { change e = e' at ee, substI e',
    rw [← add_assoc, ← mul_add, ← nat.cast_add] }
end

theorem sub_NF_below : ∀ {o₁ o₂ b}, NF_below o₁ b → NF o₂ → NF_below (o₁ - o₂) b
| 0            o b h₁ h₂ := by cases o; exact NF_below.zero
| (oadd e n a) 0 b h₁ h₂ := h₁
| (oadd e₁ n₁ a₁) (oadd e₂ n₂ a₂) b h₁ h₂ := begin
  have h' := sub_NF_below h₁.snd h₂.snd,
  simp [has_sub.sub, sub] at h' ⊢,
  have := @cmp_compares _ _ h₁.fst h₂.fst,
  cases cmp e₁ e₂; simp [sub],
  { apply NF_below.zero },
  { simp at this, subst e₂,
    cases mn : (n₁:ℕ) - n₂; simp [sub],
    { by_cases en : n₁ = n₂; simp [en],
      { exact h'.mono (le_of_lt h₁.lt) },
      { exact NF_below.zero } },
    { exact NF_below.oadd h₁.fst h₁.snd h₁.lt } },
  { exact h₁ }
end

instance sub_NF (o₁ o₂) : ∀ [NF o₁] [NF o₂], NF (o₁ - o₂)
| ⟨⟨b₁, h₁⟩⟩ h₂ := ⟨⟨b₁, sub_NF_below h₁ h₂⟩⟩

@[simp] theorem repr_sub : ∀ o₁ o₂ [NF o₁] [NF o₂], repr (o₁ - o₂) = repr o₁ - repr o₂
| 0            o h₁ h₂ := by cases o; exact (ordinal.zero_sub _).symm
| (oadd e n a) 0 h₁ h₂ := (ordinal.sub_zero _).symm
| (oadd e₁ n₁ a₁) (oadd e₂ n₂ a₂) h₁ h₂ := begin
  haveI := h₁.snd, haveI := h₂.snd, have h' := repr_sub a₁ a₂,
  conv at h' in (a₁-a₂) {simp [has_sub.sub]},
  have nf := onote.sub_NF a₁ a₂,
  conv at nf in (a₁-a₂) {simp [has_sub.sub]},
  conv in (_-oadd _ _ _) {simp [has_sub.sub, sub]},
  have ee := @cmp_compares _ _ h₁.fst h₂.fst,
  cases cmp e₁ e₂,
  { rw [ordinal.sub_eq_zero_iff_le.2], {refl},
    exact le_of_lt (oadd_lt_oadd_1 h₁ ee) },
  { change e₁ = e₂ at ee, substI e₂, unfold sub._match_1,
    cases mn : (n₁:ℕ) - n₂; dsimp only [sub._match_2],
    { by_cases en : n₁ = n₂,
      { simpa [en] },
      { simp [en, -repr],
        exact (ordinal.sub_eq_zero_iff_le.2 $ le_of_lt $ oadd_lt_oadd_2 h₁ $
          lt_of_le_of_ne (tsub_eq_zero_iff_le.1 mn) (mt pnat.eq en)).symm } },
    { simp [nat.succ_pnat, -nat.cast_succ],
      rw [(tsub_eq_iff_eq_add_of_le $ le_of_lt $ nat.lt_of_sub_eq_succ mn).1 mn,
          add_comm, nat.cast_add, mul_add, add_assoc, add_sub_add_cancel],
      refine (ordinal.sub_eq_of_add_eq $ add_absorp h₂.snd'.repr_lt $
        le_trans _ (le_add_right _ _)).symm,
      simpa using mul_le_mul_left' (nat_cast_le.2 $ nat.succ_pos _) _ } },
  { exact (ordinal.sub_eq_of_add_eq $ add_absorp (h₂.below_of_lt ee).repr_lt $
      omega_le_oadd _ _ _).symm }
end

/-- Multiplication of ordinal notations (correct only for normal input) -/
def mul : onote → onote → onote
| 0 _ := 0
| _ 0 := 0
| o₁@(oadd e₁ n₁ a₁) (oadd e₂ n₂ a₂) :=
  if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else
  oadd (e₁ + e₂) n₂ (mul o₁ a₂)

instance : has_mul onote := ⟨mul⟩

instance : mul_zero_class onote :=
{ mul := (*),
  zero := 0,
  zero_mul := λ o, by cases o; refl,
  mul_zero := λ o, by cases o; refl }

theorem oadd_mul (e₁ n₁ a₁ e₂ n₂ a₂) : oadd e₁ n₁ a₁ * oadd e₂ n₂ a₂ =
  if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else
  oadd (e₁ + e₂) n₂ (oadd e₁ n₁ a₁ * a₂) := rfl

theorem oadd_mul_NF_below {e₁ n₁ a₁ b₁} (h₁ : NF_below (oadd e₁ n₁ a₁) b₁) :
  ∀ {o₂ b₂}, NF_below o₂ b₂ → NF_below (oadd e₁ n₁ a₁ * o₂) (repr e₁ + b₂)
| 0 b₂ h₂ := NF_below.zero
| (oadd e₂ n₂ a₂) b₂ h₂ := begin
  have IH := oadd_mul_NF_below h₂.snd,
  by_cases e0 : e₂ = 0; simp [e0, oadd_mul],
  { apply NF_below.oadd h₁.fst h₁.snd,
    simpa using (add_lt_add_iff_left (repr e₁)).2
      (lt_of_le_of_lt (ordinal.zero_le _) h₂.lt) },
  { haveI := h₁.fst, haveI := h₂.fst,
    apply NF_below.oadd, apply_instance,
    { rwa repr_add },
    { rw [repr_add, add_lt_add_iff_left], exact h₂.lt } }
end

instance mul_NF : ∀ o₁ o₂ [NF o₁] [NF o₂], NF (o₁ * o₂)
| 0 o h₁ h₂ := by cases o; exact NF.zero
| (oadd e n a) o ⟨⟨b₁, hb₁⟩⟩ ⟨⟨b₂, hb₂⟩⟩ :=
  ⟨⟨_, oadd_mul_NF_below hb₁ hb₂⟩⟩

@[simp] theorem repr_mul : ∀ o₁ o₂ [NF o₁] [NF o₂], repr (o₁ * o₂) = repr o₁ * repr o₂
| 0               o               h₁ h₂ := by cases o; exact (zero_mul _).symm
| (oadd e₁ n₁ a₁) 0               h₁ h₂ := (mul_zero _).symm
| (oadd e₁ n₁ a₁) (oadd e₂ n₂ a₂) h₁ h₂ := begin
  have IH : repr (mul _ _) = _ := @repr_mul _ _ h₁ h₂.snd,
  conv {to_lhs, simp [(*)]},
  have ao : repr a₁ + ω ^ repr e₁ * (n₁:ℕ) = ω ^ repr e₁ * (n₁:ℕ),
  { apply add_absorp h₁.snd'.repr_lt,
    simpa using (mul_le_mul_iff_left $ opow_pos _ omega_pos).2
      (nat_cast_le.2 n₁.2) },
  by_cases e0 : e₂ = 0; simp [e0, mul],
  { cases nat.exists_eq_succ_of_ne_zero n₂.ne_zero with x xe,
    simp [h₂.zero_of_zero e0, xe, -nat.cast_succ],
    rw [nat_cast_succ x, add_mul_succ _ ao, mul_assoc] },
  { haveI := h₁.fst, haveI := h₂.fst,
    simp [IH, repr_add, opow_add, mul_add],
    rw ← mul_assoc, congr' 2,
    have := mt repr_inj.1 e0,
    rw [add_mul_limit ao (opow_is_limit_left omega_is_limit this),
        mul_assoc, mul_omega_dvd (nat_cast_pos.2 n₁.pos) (nat_lt_omega _)],
    simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 this) },
end

/-- Calculate division and remainder of `o` mod ω.
  `split' o = (a, n)` means `o = ω * a + n`. -/
def split' : onote → onote × ℕ
| 0            := (0, 0)
| (oadd e n a) := if e = 0 then (0, n) else
  let (a', m) := split' a in (oadd (e - 1) n a', m)

/-- Calculate division and remainder of `o` mod ω.
  `split o = (a, n)` means `o = a + n`, where `ω ∣ a`. -/
def split : onote → onote × ℕ
| 0            := (0, 0)
| (oadd e n a) := if e = 0 then (0, n) else
  let (a', m) := split a in (oadd e n a', m)

/-- `scale x o` is the ordinal notation for `ω ^ x * o`. -/
def scale (x : onote) : onote → onote
| 0            := 0
| (oadd e n a) := oadd (x + e) n (scale a)

/-- `mul_nat o n` is the ordinal notation for `o * n`. -/
def mul_nat : onote → ℕ → onote
| 0            m := 0
| _            0 := 0
| (oadd e n a) (m+1) := oadd e (n * m.succ_pnat) a

/-- Auxiliary definition to compute the ordinal notation for the ordinal
exponentiation in `opow` -/
def opow_aux (e a0 a : onote) : ℕ → ℕ → onote
| _     0     := 0
| 0     (m+1) := oadd e m.succ_pnat 0
| (k+1) m     := scale (e + mul_nat a0 k) a + opow_aux k m

/-- `opow o₁ o₂` calculates the ordinal notation for
  the ordinal exponential `o₁ ^ o₂`. -/
def opow (o₁ o₂ : onote) : onote :=
match split o₁ with
| (0, 0) := if o₂ = 0 then 1 else 0
| (0, 1) := 1
| (0, m+1) := let (b', k) := split' o₂ in
  oadd b' (@has_pow.pow ℕ+ _ _ m.succ_pnat k) 0
| (a@(oadd a0 _ _), m) := match split o₂ with
  | (b, 0) := oadd (a0 * b) 1 0
  | (b, k+1) := let eb := a0*b in
    scale (eb + mul_nat a0 k) a + opow_aux eb a0 (mul_nat a m) k m
  end
end

instance : has_pow onote onote := ⟨opow⟩

theorem opow_def (o₁ o₂ : onote) : o₁ ^ o₂ = opow._match_1 o₂ (split o₁) := rfl

theorem split_eq_scale_split' : ∀ {o o' m} [NF o], split' o = (o', m) → split o = (scale 1 o', m)
| 0            o' m h p := by injection p; substs o' m; refl
| (oadd e n a) o' m h p := begin
  by_cases e0 : e = 0; simp [e0, split, split'] at p ⊢,
  { rcases p with ⟨rfl, rfl⟩, exact ⟨rfl, rfl⟩ },
  { revert p, cases h' : split' a with a' m',
    haveI := h.fst, haveI := h.snd,
    simp [split_eq_scale_split' h', split, split'],
    have : 1 + (e - 1) = e,
    { refine repr_inj.1 _, simp,
      have := mt repr_inj.1 e0,
      exact ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this) },
    intros, substs o' m, simp [scale, this] }
end

theorem NF_repr_split' : ∀ {o o' m} [NF o], split' o = (o', m) → NF o' ∧ repr o = ω * repr o' + m
| 0            o' m h p := by injection p; substs o' m; simp [NF.zero]
| (oadd e n a) o' m h p := begin
  by_cases e0 : e = 0; simp [e0, split, split'] at p ⊢,
  { rcases p with ⟨rfl, rfl⟩,
    simp [h.zero_of_zero e0, NF.zero] },
  { revert p, cases h' : split' a with a' m',
    haveI := h.fst, haveI := h.snd,
    cases NF_repr_split' h' with IH₁ IH₂,
    simp [IH₂, split'],
    intros, substs o' m,
    have : (ω : ordinal.{0}) ^ repr e = ω ^ (1 : ordinal.{0}) * ω ^ (repr e - 1),
    { have := mt repr_inj.1 e0,
      rw [← opow_add, ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this)] },
    refine ⟨NF.oadd (by apply_instance) _ _, _⟩,
    { simp at this ⊢,
      refine IH₁.below_of_lt' ((mul_lt_mul_iff_left omega_pos).1 $
        lt_of_le_of_lt (le_add_right _ m') _),
      rw [← this, ← IH₂], exact h.snd'.repr_lt },
    { rw this, simp [mul_add, mul_assoc, add_assoc] } }
end

theorem scale_eq_mul (x) [NF x] : ∀ o [NF o], scale x o = oadd x 1 0 * o
| 0            h := rfl
| (oadd e n a) h := begin
  simp [(*)], simp [mul, scale],
  haveI := h.snd,
  by_cases e0 : e = 0,
  { rw scale_eq_mul, simp [e0, h.zero_of_zero, show x + 0 = x, from repr_inj.1 (by simp)] },
  { simp [e0, scale_eq_mul, (*)] }
end

instance NF_scale (x) [NF x] (o) [NF o] : NF (scale x o) :=
by rw scale_eq_mul; apply_instance

@[simp] theorem repr_scale (x) [NF x] (o) [NF o] : repr (scale x o) = ω ^ repr x * repr o :=
by simp [scale_eq_mul]

theorem NF_repr_split {o o' m} [NF o] (h : split o = (o', m)) : NF o' ∧ repr o = repr o' + m :=
begin
  cases e : split' o with a n,
  cases NF_repr_split' e with s₁ s₂, resetI,
  rw split_eq_scale_split' e at h,
  injection h, substs o' n,
  simp [repr_scale, s₂.symm],
  apply_instance
end

theorem split_dvd {o o' m} [NF o] (h : split o = (o', m)) : ω ∣ repr o' :=
begin
  cases e : split' o with a n,
  rw split_eq_scale_split' e at h,
  injection h, subst o',
  cases NF_repr_split' e, resetI, simp
end

theorem split_add_lt {o e n a m} [NF o] (h : split o = (oadd e n a, m)) : repr a + m < ω ^ repr e :=
begin
  cases NF_repr_split h with h₁ h₂,
  cases h₁.of_dvd_omega (split_dvd h) with e0 d,
  have := h₁.fst, have := h₁.snd,
  apply principal_add_omega_opow _ h₁.snd'.repr_lt (lt_of_lt_of_le (nat_lt_omega _) _),
  simpa using opow_le_opow_right omega_pos (one_le_iff_ne_zero.2 e0),
end

@[simp] theorem mul_nat_eq_mul (n o) : mul_nat o n = o * of_nat n :=
by cases o; cases n; refl

instance NF_mul_nat (o) [NF o] (n) : NF (mul_nat o n) :=
by simp; apply_instance

instance NF_opow_aux (e a0 a) [NF e] [NF a0] [NF a] : ∀ k m, NF (opow_aux e a0 a k m)
| k     0     := by cases k; exact NF.zero
| 0     (m+1) := NF.oadd_zero _ _
| (k+1) (m+1) := by haveI := NF_opow_aux k;
  simp [opow_aux, nat.succ_ne_zero]; apply_instance

instance NF_opow (o₁ o₂) [NF o₁] [NF o₂] : NF (o₁ ^ o₂) :=
begin
  cases e₁ : split o₁ with a m,
  have na := (NF_repr_split e₁).1,
  cases e₂ : split' o₂ with b' k,
  haveI := (NF_repr_split' e₂).1,
  casesI a with a0 n a',
  { cases m with m,
    { by_cases o₂ = 0; simp [pow, opow, *]; apply_instance },
    { by_cases m = 0,
      { simp only [pow, opow, *, zero_def], apply_instance },
      { simp [pow, opow, *, - npow_eq_pow], apply_instance } } },
  { simp [pow, opow, e₁, e₂, split_eq_scale_split' e₂],
    have := na.fst,
    cases k with k; simp [opow]; resetI; apply_instance }
end

theorem scale_opow_aux (e a0 a : onote) [NF e] [NF a0] [NF a] :
  ∀ k m, repr (opow_aux e a0 a k m) = ω ^ repr e * repr (opow_aux 0 a0 a k m)
| 0     m := by cases m; simp [opow_aux]
| (k+1) m := by by_cases m = 0; simp [h, opow_aux, mul_add, opow_add, mul_assoc, scale_opow_aux]

theorem repr_opow_aux₁ {e a} [Ne : NF e] [Na : NF a] {a' : ordinal} (e0 : repr e ≠ 0)
  (h : a' < (ω : ordinal.{0}) ^ repr e) (aa : repr a = a') (n : ℕ+) :
  ((ω : ordinal.{0}) ^ repr e * (n:ℕ) + a') ^ (ω : ordinal.{0}) =
  (ω ^ repr e) ^ (ω : ordinal.{0}) :=
begin
  subst aa,
  have No := Ne.oadd n (Na.below_of_lt' h),
  have := omega_le_oadd e n a, unfold repr at this,
  refine le_antisymm _ (opow_le_opow_left _ this),
  apply (opow_le_of_limit ((opow_pos _ omega_pos).trans_le this).ne' omega_is_limit).2,
  intros b l,
  have := (No.below_of_lt (lt_succ _)).repr_lt, unfold repr at this,
  apply (opow_le_opow_left b $ this.le).trans,
  rw [← opow_mul, ← opow_mul],
  apply opow_le_opow_right omega_pos,
  cases le_or_lt ω (repr e) with h h,
  { apply (mul_le_mul_left' (le_succ b) _).trans,
    rw [←add_one_eq_succ, add_mul_succ _ (one_add_of_omega_le h), add_one_eq_succ,
        succ_le_iff, mul_lt_mul_iff_left (ordinal.pos_iff_ne_zero.2 e0)],
    exact omega_is_limit.2 _ l },
  { apply (principal_mul_omega (omega_is_limit.2 _ h) l).le.trans,
    simpa using mul_le_mul_right' (one_le_iff_ne_zero.2 e0) ω }
end

section
local infixr (name := ordinal.pow) ^ := @pow ordinal.{0} ordinal ordinal.has_pow

theorem repr_opow_aux₂ {a0 a'} [N0 : NF a0] [Na' : NF a'] (m : ℕ)
  (d : ω ∣ repr a')
  (e0 : repr a0 ≠ 0) (h : repr a' + m < ω ^ repr a0) (n : ℕ+) (k : ℕ) :
  let R := repr (opow_aux 0 a0 (oadd a0 n a' * of_nat m) k m) in
  (k ≠ 0 → R < (ω ^ repr a0) ^ succ k) ∧
  (ω ^ repr a0) ^ k * (ω ^ repr a0 * (n:ℕ) + repr a') + R =
    (ω ^ repr a0 * (n:ℕ) + repr a' + m) ^ succ k :=
begin
  intro,
  haveI No : NF (oadd a0 n a') :=
    N0.oadd n (Na'.below_of_lt' $ lt_of_le_of_lt (le_add_right _ _) h),
  induction k with k IH, {cases m; simp [opow_aux, R]},
  rename R R', let R := repr (opow_aux 0 a0 (oadd a0 n a' * of_nat m) k m),
  let ω0 := ω ^ repr a0, let α' := ω0 * n + repr a',
  change (k ≠ 0 → R < ω0 ^ succ k) ∧ ω0 ^ k * α' + R = (α' + m) ^ succ k at IH,
  have RR : R' = ω0 ^ k * (α' * m) + R,
  { by_cases m = 0; simp [h, R', opow_aux, R, opow_mul],
    { cases k; simp [opow_aux] }, { refl } },
  have α0 : 0 < α', {simpa [α', lt_def, repr] using oadd_pos a0 n a'},
  have ω00 : 0 < ω0 ^ k := opow_pos _ (opow_pos _ omega_pos),
  have Rl : R < ω ^ (repr a0 * succ ↑k),
  { by_cases k0 : k = 0,
    { simp [k0],
      refine lt_of_lt_of_le _ (opow_le_opow_right omega_pos (one_le_iff_ne_zero.2 e0)),
      cases m with m; simp [k0, R, opow_aux, omega_pos],
      rw [←add_one_eq_succ, ←nat.cast_succ], apply nat_lt_omega },
    { rw opow_mul, exact IH.1 k0 } },
  refine ⟨λ_, _, _⟩,
  { rw [RR, ← opow_mul _ _ (succ k.succ)],
    have e0 := ordinal.pos_iff_ne_zero.2 e0,
    have rr0 := lt_of_lt_of_le e0 (le_add_left _ _),
    apply principal_add_omega_opow,
    { simp [opow_mul, ω0, opow_add, mul_assoc],
      rw [mul_lt_mul_iff_left ω00, ← ordinal.opow_add],
      have := (No.below_of_lt _).repr_lt, unfold repr at this,
      refine mul_lt_omega_opow rr0 this (nat_lt_omega _),
      simpa using (add_lt_add_iff_left (repr a0)).2 e0 },
    { refine lt_of_lt_of_le Rl (opow_le_opow_right omega_pos $
        mul_le_mul_left' (succ_le_succ_iff.2 (nat_cast_le.2 (le_of_lt k.lt_succ_self))) _) } },
  calc
        ω0 ^ k.succ * α' + R'
      = ω0 ^ succ k * α' + (ω0 ^ k * α' * m + R) : by rw [nat_cast_succ, RR, ← mul_assoc]
  ... = (ω0 ^ k * α' + R) * α' + (ω0 ^ k * α' + R) * m : _
  ... = (α' + m) ^ succ k.succ : by rw [← mul_add, nat_cast_succ, opow_succ, IH.2],
  congr' 1,
  { have αd : ω ∣ α' := dvd_add (dvd_mul_of_dvd_left
      (by simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 e0)) _) d,
    rw [mul_add (ω0 ^ k), add_assoc, ← mul_assoc, ← opow_succ,
        add_mul_limit _ (is_limit_iff_omega_dvd.2 ⟨ne_of_gt α0, αd⟩), mul_assoc,
        @mul_omega_dvd n (nat_cast_pos.2 n.pos) (nat_lt_omega _) _ αd],
    apply @add_absorp _ (repr a0 * succ k),
    { refine principal_add_omega_opow _ _ Rl,
      rw [opow_mul, opow_succ, mul_lt_mul_iff_left ω00],
      exact No.snd'.repr_lt },
    { have := mul_le_mul_left' (one_le_iff_pos.2 $ nat_cast_pos.2 n.pos) (ω0 ^ succ k),
      rw opow_mul, simpa [-opow_succ] } },
  { cases m,
    { have : R = 0, {cases k; simp [R, opow_aux]}, simp [this] },
    { rw [nat_cast_succ, add_mul_succ],
      apply add_absorp Rl,
      rw [opow_mul, opow_succ],
      apply mul_le_mul_left',
      simpa [α', repr] using omega_le_oadd a0 n a' } }
end

end

theorem repr_opow (o₁ o₂) [NF o₁] [NF o₂] : repr (o₁ ^ o₂) = repr o₁ ^ repr o₂ :=
begin
  cases e₁ : split o₁ with a m,
  cases NF_repr_split e₁ with N₁ r₁,
  cases a with a0 n a',
  { cases m with m,
    { by_cases o₂ = 0; simp [opow_def, opow, e₁, h, r₁],
      have := mt repr_inj.1 h, rw zero_opow this },
    { cases e₂ : split' o₂ with b' k,
      cases NF_repr_split' e₂ with _ r₂,
      by_cases m = 0; simp [opow_def, opow, e₁, h, r₁, e₂, r₂, -nat.cast_succ],
      rw [opow_add, opow_mul, opow_omega _ (nat_lt_omega _)],
      simpa using nat_cast_lt.2 (nat.succ_lt_succ $ pos_iff_ne_zero.2 h) } },
  { haveI := N₁.fst, haveI := N₁.snd,
    cases N₁.of_dvd_omega (split_dvd e₁) with a00 ad,
    have al := split_add_lt e₁,
    have aa : repr (a' + of_nat m) = repr a' + m, {simp},
    cases e₂ : split' o₂ with b' k,
    cases NF_repr_split' e₂ with _ r₂,
    simp [opow_def, opow, e₁, r₁, split_eq_scale_split' e₂],
    cases k with k; resetI,
    { simp [opow, r₂, opow_mul, repr_opow_aux₁ a00 al aa, add_assoc] },
    { simp [opow, r₂, opow_add, opow_mul, mul_assoc, add_assoc],
      rw [repr_opow_aux₁ a00 al aa, scale_opow_aux], simp [opow_mul],
      rw [← mul_add, ← add_assoc ((ω : ordinal.{0}) ^ repr a0 * (n:ℕ))], congr' 1,
      rw [← opow_succ],
      exact (repr_opow_aux₂ _ ad a00 al _ _).2 } }
end

/-- Given an ordinal, returns `inl none` for `0`, `inl (some a)` for `a+1`, and
  `inr f` for a limit ordinal `a`, where `f i` is a sequence converging to `a`. -/
def fundamental_sequence : onote → option onote ⊕ (ℕ → onote)
| zero := sum.inl none
| (oadd a m b) :=
  match fundamental_sequence b with
  | sum.inr f := sum.inr (λ i, oadd a m (f i))
  | sum.inl (some b') := sum.inl (some (oadd a m b'))
  | sum.inl none := match fundamental_sequence a, m.nat_pred with
    | sum.inl none, 0 := sum.inl (some zero)
    | sum.inl none, m+1 := sum.inl (some (oadd zero m.succ_pnat zero))
    | sum.inl (some a'), 0 := sum.inr (λ i, oadd a' i.succ_pnat zero)
    | sum.inl (some a'), m+1 := sum.inr (λ i, oadd a m.succ_pnat (oadd a' i.succ_pnat zero))
    | sum.inr f, 0 := sum.inr (λ i, oadd (f i) 1 zero)
    | sum.inr f, m+1 := sum.inr (λ i, oadd a m.succ_pnat (oadd (f i) 1 zero))
    end
  end

private theorem exists_lt_add {α} [hα : nonempty α] {o : ordinal} {f : α → ordinal}
  (H : ∀ ⦃a⦄, a < o → ∃ i, a < f i) {b : ordinal} ⦃a⦄ (h : a < b + o) : ∃ i, a < b + f i :=
begin
  cases lt_or_le a b with h h',
  { obtain ⟨i⟩ := id hα, exact ⟨i, h.trans_le (le_add_right _ _)⟩ },
  { rw [← ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left] at h,
    refine (H h).imp (λ i H, _),
    rwa [← ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left] }
end

private theorem exists_lt_mul_omega' {o : ordinal} ⦃a⦄ (h : a < o * ω) : ∃ i : ℕ, a < o * ↑i + o :=
begin
  obtain ⟨i, hi, h'⟩ := (lt_mul_of_limit omega_is_limit).1 h,
  obtain ⟨i, rfl⟩ := lt_omega.1 hi,
  exact ⟨i, h'.trans_le (le_add_right _ _)⟩
end

local infixr (name := ordinal.pow) ^ := @pow ordinal ordinal ordinal.has_pow
private theorem exists_lt_omega_opow' {α} {o b : ordinal}
  (hb : 1 < b) (ho : o.is_limit) {f : α → ordinal}
  (H : ∀ ⦃a⦄, a < o → ∃ i, a < f i) ⦃a⦄ (h : a < b ^ o) : ∃ i, a < b ^ f i :=
begin
  obtain ⟨d, hd, h'⟩ := (lt_opow_of_limit (zero_lt_one.trans hb).ne' ho).1 h,
  exact (H hd).imp (λ i hi, h'.trans $ (opow_lt_opow_iff_right hb).2 hi)
end

/-- The property satisfied by `fundamental_sequence o`:
  * `inl none` means `o = 0`
  * `inl (some a)` means `o = succ a`
  * `inr f` means `o` is a limit ordinal and `f` is a
    strictly increasing sequence which converges to `o` -/
def fundamental_sequence_prop (o : onote) : option onote ⊕ (ℕ → onote) → Prop
| (sum.inl none) := o = 0
| (sum.inl (some a)) := o.repr = succ a.repr ∧ (o.NF → a.NF)
| (sum.inr f) := o.repr.is_limit ∧
  (∀ i, f i < f (i + 1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧
  (∀ a, a < o.repr → ∃ i, a < (f i).repr)

theorem fundamental_sequence_has_prop (o) : fundamental_sequence_prop o (fundamental_sequence o) :=
begin
  induction o with a m b iha ihb, {exact rfl},
  rw [fundamental_sequence],
  rcases e : b.fundamental_sequence with ⟨_|b'⟩|f;
    simp only [fundamental_sequence, fundamental_sequence_prop];
    rw [e, fundamental_sequence_prop] at ihb,
  { rcases e : a.fundamental_sequence with ⟨_|a'⟩|f; cases e' : m.nat_pred with m';
      simp only [fundamental_sequence, fundamental_sequence_prop];
      rw [e, fundamental_sequence_prop] at iha;
      try { rw show m = 1,
        { have := pnat.nat_pred_add_one m, rw [e'] at this, exact pnat.coe_inj.1 this.symm } };
      try { rw show m = m'.succ.succ_pnat,
        { rw [← e', ← pnat.coe_inj, nat.succ_pnat_coe, ← nat.add_one, pnat.nat_pred_add_one] } };
      simp only [repr, iha, ihb, opow_lt_opow_iff_right one_lt_omega,
        add_lt_add_iff_left, add_zero, coe_coe, eq_self_iff_true, lt_add_iff_pos_right,
        lt_def, mul_one, nat.cast_zero, nat.cast_succ, nat.succ_pnat_coe, opow_succ,
        opow_zero, mul_add_one, pnat.one_coe, succ_zero, true_and, _root_.zero_add,
        zero_def],
    { apply_instance },
    { exact ⟨rfl, infer_instance⟩ },
    { have := opow_pos _ omega_pos,
      refine ⟨mul_is_limit this omega_is_limit,
        λ i, ⟨this, _, λ H, @NF.oadd_zero _ _ (iha.2 H.fst)⟩, exists_lt_mul_omega'⟩,
      rw [← mul_succ, ← nat_cast_succ, ordinal.mul_lt_mul_iff_left this],
      apply nat_lt_omega },
    { have := opow_pos _ omega_pos,
      refine ⟨
        add_is_limit _ (mul_is_limit this omega_is_limit), λ i, ⟨this, _, _⟩,
        exists_lt_add exists_lt_mul_omega'⟩,
      { rw [← mul_succ, ← nat_cast_succ, ordinal.mul_lt_mul_iff_left this],
        apply nat_lt_omega },
      { refine λ H, H.fst.oadd _ (NF.below_of_lt' _ (@NF.oadd_zero _ _ (iha.2 H.fst))),
        rw [repr, repr, add_zero, iha.1, opow_succ, ordinal.mul_lt_mul_iff_left this],
        apply nat_lt_omega } },
    { rcases iha with ⟨h1, h2, h3⟩,
      refine ⟨opow_is_limit one_lt_omega h1, λ i, _, exists_lt_omega_opow' one_lt_omega h1 h3⟩,
      obtain ⟨h4, h5, h6⟩ := h2 i, exact ⟨h4, h5, λ H, @NF.oadd_zero _ _ (h6 H.fst)⟩ },
    { rcases iha with ⟨h1, h2, h3⟩,
      refine ⟨add_is_limit _ (opow_is_limit one_lt_omega h1), λ i, _,
        exists_lt_add (exists_lt_omega_opow' one_lt_omega h1 h3)⟩,
      obtain ⟨h4, h5, h6⟩ := h2 i,
      refine ⟨h4, h5, λ H, H.fst.oadd _ (NF.below_of_lt' _ (@NF.oadd_zero _ _ (h6 H.fst)))⟩,
      rwa [repr, repr, add_zero, coe_coe, pnat.one_coe, nat.cast_one, mul_one,
        opow_lt_opow_iff_right one_lt_omega] } },
  { refine ⟨by rw [repr, ihb.1, add_succ, repr],
      λ H, H.fst.oadd _ (NF.below_of_lt' _ (ihb.2 H.snd))⟩,
    have := H.snd'.repr_lt, rw ihb.1 at this,
    exact (lt_succ _).trans this },
  { rcases ihb with ⟨h1, h2, h3⟩,
    simp only [repr],
    exact ⟨ordinal.add_is_limit _ h1,
      λ i, ⟨oadd_lt_oadd_3 (h2 i).1, oadd_lt_oadd_3 (h2 i).2.1, λ H, H.fst.oadd _
        (NF.below_of_lt' (lt_trans (h2 i).2.1 H.snd'.repr_lt) ((h2 i).2.2 H.snd))⟩,
      exists_lt_add h3⟩ }
end

/-- The fast growing hierarchy for ordinal notations `< ε₀`. This is a sequence of
functions `ℕ → ℕ` indexed by ordinals, with the definition:
* `f_0(n) = n + 1`
* `f_(α+1)(n) = f_α^[n](n)`
* `f_α(n) = f_(α[n])(n)` where `α` is a limit ordinal
   and `α[i]` is the fundamental sequence converging to `α` -/
def fast_growing : onote → ℕ → ℕ
| o :=
  match fundamental_sequence o, fundamental_sequence_has_prop o with
  | sum.inl none, _ := nat.succ
  | sum.inl (some a), h :=
    have a < o, { rw [lt_def, h.1], apply lt_succ },
    λ i, (fast_growing a)^[i] i
  | sum.inr f, h := λ i, have f i < o, from (h.2.1 i).2.1, fast_growing (f i) i
  end
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf repr ordinal.lt_wf⟩],
  dec_tac := `[assumption] }

theorem fast_growing_def
  {o : onote} {x} (e : fundamental_sequence o = x) :
    fast_growing o =
    fast_growing._match_1 o
      (λ a _ _, a.fast_growing)
      (λ f _ i _, (f i).fast_growing i)
      x (e ▸ fundamental_sequence_has_prop _) :=
by { subst x, rw [fast_growing] }

theorem fast_growing_zero' (o : onote) (h : fundamental_sequence o = sum.inl none) :
  fast_growing o = nat.succ := by { rw [fast_growing_def h], refl }
theorem fast_growing_succ (o) {a} (h : fundamental_sequence o = sum.inl (some a)) :
  fast_growing o = λ i, ((fast_growing a)^[i] i) := by { rw [fast_growing_def h], refl }
theorem fast_growing_limit (o) {f} (h : fundamental_sequence o = sum.inr f) :
  fast_growing o = λ i, fast_growing (f i) i := by { rw [fast_growing_def h], refl }

@[simp] theorem fast_growing_zero : fast_growing 0 = nat.succ := fast_growing_zero' _ rfl

@[simp] theorem fast_growing_one : fast_growing 1 = (λ n, 2 * n) :=
begin
  rw [@fast_growing_succ 1 0 rfl], funext i, rw [two_mul, fast_growing_zero],
  suffices : ∀ a b, nat.succ^[a] b = b + a, from this _ _,
  intros a b, induction a; simp [*, function.iterate_succ', nat.add_succ],
end

section
local infixr (name := pow) ^ := pow
@[simp] theorem fast_growing_two : fast_growing 2 = (λ n, 2 ^ n * n) :=
begin
  rw [@fast_growing_succ 2 1 rfl], funext i, rw [fast_growing_one],
  suffices : ∀ a b, (λ (n : ℕ), 2 * n)^[a] b = 2 ^ a * b, from this _ _,
  intros a b, induction a; simp [*, function.iterate_succ', pow_succ, mul_assoc],
end
end

/-- We can extend the fast growing hierarchy one more step to `ε₀` itself,
  using `ω^(ω^...^ω^0)` as the fundamental sequence converging to `ε₀` (which is not an `onote`).
  Extending the fast growing hierarchy beyond this requires a definition of fundamental sequence
  for larger ordinals. -/
def fast_growing_ε₀ (i : ℕ) : ℕ := fast_growing ((λ a, a.oadd 1 0)^[i] 0) i

theorem fast_growing_ε₀_zero : fast_growing_ε₀ 0 = 1 := by simp [fast_growing_ε₀]

theorem fast_growing_ε₀_one : fast_growing_ε₀ 1 = 2 :=
by simp [fast_growing_ε₀, show oadd 0 1 0 = 1, from rfl]

theorem fast_growing_ε₀_two : fast_growing_ε₀ 2 = 2048 :=
by norm_num [fast_growing_ε₀,
  show oadd 0 1 0 = 1, from rfl,
  @fast_growing_limit (oadd 1 1 0) _ rfl,
  show oadd 0 (2:nat).succ_pnat 0 = 3, from rfl,
  @fast_growing_succ 3 2 rfl]

end onote

/-- The type of normal ordinal notations. (It would have been
  nicer to define this right in the inductive type, but `NF o`
  requires `repr` which requires `onote`, so all these things
  would have to be defined at once, which messes up the VM
  representation.) -/
def nonote := {o : onote // o.NF}

instance : decidable_eq nonote := by unfold nonote; apply_instance

namespace nonote
open onote

instance NF (o : nonote) : NF o.1 := o.2

/-- Construct a `nonote` from an ordinal notation
  (and infer normality) -/
def mk (o : onote) [h : NF o] : nonote := ⟨o, h⟩

/-- The ordinal represented by an ordinal notation.
  (This function is noncomputable because ordinal
  arithmetic is noncomputable. In computational applications
  `nonote` can be used exclusively without reference
  to `ordinal`, but this function allows for correctness
  results to be stated.) -/
noncomputable def repr (o : nonote) : ordinal := o.1.repr

instance : has_to_string nonote := ⟨λ x, x.1.to_string⟩
instance : has_repr nonote := ⟨λ x, x.1.repr'⟩

instance : preorder nonote :=
{ le       := λ x y, repr x ≤ repr y,
  lt       := λ x y, repr x < repr y,
  le_refl  := λ a, @le_refl ordinal _ _,
  le_trans := λ a b c, @le_trans ordinal _ _ _ _,
  lt_iff_le_not_le := λ a b, @lt_iff_le_not_le ordinal _ _ _ }

instance : has_zero nonote := ⟨⟨0, NF.zero⟩⟩
instance : inhabited nonote := ⟨0⟩

theorem lt_wf : @well_founded nonote (<) := inv_image.wf repr ordinal.lt_wf
instance : well_founded_lt nonote := ⟨lt_wf⟩
instance : has_well_founded nonote := ⟨(<), lt_wf⟩

/-- Convert a natural number to an ordinal notation -/
def of_nat (n : ℕ) : nonote := ⟨of_nat n, ⟨⟨_, NF_below_of_nat _⟩⟩⟩

/-- Compare ordinal notations -/
def cmp (a b : nonote) : ordering :=
cmp a.1 b.1

theorem cmp_compares : ∀ a b : nonote, (cmp a b).compares a b
| ⟨a, ha⟩ ⟨b, hb⟩ := begin
  resetI,
  dsimp [cmp], have := onote.cmp_compares a b,
  cases onote.cmp a b; try {exact this},
  exact subtype.mk_eq_mk.2 this
end

instance : linear_order nonote := linear_order_of_compares cmp cmp_compares
instance : is_well_order nonote (<) := { }

/-- Asserts that `repr a < ω ^ repr b`. Used in `nonote.rec_on` -/
def below (a b : nonote) : Prop := NF_below a.1 (repr b)

/-- The `oadd` pseudo-constructor for `nonote` -/
def oadd (e : nonote) (n : ℕ+) (a : nonote) (h : below a e) : nonote := ⟨_, NF.oadd e.2 n h⟩

/-- This is a recursor-like theorem for `nonote` suggesting an
  inductive definition, which can't actually be defined this
  way due to conflicting dependencies. -/
@[elab_as_eliminator] def rec_on {C : nonote → Sort*} (o : nonote)
  (H0 : C 0)
  (H1 : ∀ e n a h, C e → C a → C (oadd e n a h)) : C o :=
begin
  cases o with o h, induction o with e n a IHe IHa,
  { exact H0 },
  { exact H1 ⟨e, h.fst⟩ n ⟨a, h.snd⟩ h.snd' (IHe _) (IHa _) }
end

/-- Addition of ordinal notations -/
instance : has_add nonote := ⟨λ x y, mk (x.1 + y.1)⟩

theorem repr_add (a b) : repr (a + b) = repr a + repr b :=
onote.repr_add a.1 b.1

/-- Subtraction of ordinal notations -/
instance : has_sub nonote := ⟨λ x y, mk (x.1 - y.1)⟩

theorem repr_sub (a b) : repr (a - b) = repr a - repr b :=
onote.repr_sub a.1 b.1

/-- Multiplication of ordinal notations -/
instance : has_mul nonote := ⟨λ x y, mk (x.1 * y.1)⟩

theorem repr_mul (a b) : repr (a * b) = repr a * repr b :=
onote.repr_mul a.1 b.1

/-- Exponentiation of ordinal notations -/
def opow (x y : nonote) := mk (x.1.opow y.1)

theorem repr_opow (a b) : repr (opow a b) = repr a ^ repr b :=
onote.repr_opow a.1 b.1

end nonote
