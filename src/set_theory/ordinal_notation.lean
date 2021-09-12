/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import set_theory.ordinal_arithmetic

/-!
# Ordinal notation

Constructive ordinal arithmetic for ordinals below `ε₀`.

We define a type `onote`, with constructors `0 : onote` and `onote.oadd e n a` representing
`ω ^ e * n + a`.
We say that `o` is in Cantor normal form - `onote.NF o` - if either `o = 0` or
`o = ω ^ e * n + a` with `a < ω ^ e` and `a` in Cantor normal form.

The type `nonote` is the type of ordinals below `ε₀` in Cantor normal form.
Various operations (addition, subtraction, multiplication, power function)
are defined on `onote` and `nonote`.
-/

open ordinal
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
  simpa using (mul_le_mul_iff_left $ power_pos (repr e) omega_pos).2 (nat_cast_le.2 n.2)
end

theorem oadd_pos (e n a) : 0 < oadd e n a :=
@lt_of_lt_of_le _ _ _ _ _ (power_pos _ omega_pos)
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
  revert h, simp [cmp],
  cases h₁ : cmp e₁ e₂; intro h; try {cases h},
  have := eq_of_cmp_eq h₁, subst e₂,
  revert h, cases h₂ : _root_.cmp (n₁:ℕ) n₂; intro h; try {cases h},
  have := eq_of_cmp_eq h, subst a₂,
  rw [_root_.cmp, cmp_using_eq_eq] at h₂,
  have := subtype.eq (eq_of_incomp h₂), subst n₂, simp
end

theorem zero_lt_one : (0 : onote) < 1 :=
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
⟨⟨_, NF_below.oadd h₁ h₂ (ordinal.lt_succ_self _)⟩⟩

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
  { exact power_pos _ omega_pos },
  { rw repr,
    refine lt_of_lt_of_le ((ordinal.add_lt_add_iff_left _).2 IH) _,
    rw ← mul_succ,
    refine le_trans (mul_le_mul_left _ $ ordinal.succ_le.2 $ nat_lt_omega _) _,
    rw ← power_succ,
    exact power_le_power_right omega_pos (ordinal.succ_le.2 h₃) }
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
| (oadd e n a) b H h := h.below_of_lt $ (power_lt_power_iff_right one_lt_omega).1 $
    (lt_of_le_of_lt (omega_le_oadd _ _ _) H)

theorem NF_below_of_nat : ∀ n, NF_below (of_nat n) 1
| 0            := NF_below.zero
| (nat.succ n) := NF_below.oadd NF.zero NF_below.zero ordinal.zero_lt_one

instance NF_of_nat (n) : NF (of_nat n) := ⟨⟨_, NF_below_of_nat n⟩⟩

instance NF_one : NF 1 := by rw ← of_nat_one; apply_instance

theorem oadd_lt_oadd_1 {e₁ n₁ o₁ e₂ n₂ o₂} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂) :
  oadd e₁ n₁ o₁ < oadd e₂ n₂ o₂ :=
@lt_of_lt_of_le _ _ _ _ _ ((h₁.below_of_lt h).repr_lt) (omega_le_oadd _ _ _)

theorem oadd_lt_oadd_2 {e o₁ o₂ : onote} {n₁ n₂ : ℕ+}
  (h₁ : NF (oadd e n₁ o₁)) (h : (n₁:ℕ) < n₂) : oadd e n₁ o₁ < oadd e n₂ o₂ :=
begin
  simp [lt_def],
  refine lt_of_lt_of_le ((ordinal.add_lt_add_iff_left _).2 h₁.snd'.repr_lt)
    (le_trans _ (le_add_right _ _)),
  rwa [← mul_succ, mul_le_mul_iff_left (power_pos _ omega_pos),
       ordinal.succ_le, nat_cast_lt]
end

theorem oadd_lt_oadd_3 {e n a₁ a₂} (h : a₁ < a₂) :
  oadd e n a₁ < oadd e n a₂ :=
begin
  rw lt_def, unfold repr,
  exact (ordinal.add_lt_add_iff_left _).2 h
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
    case ordering.lt {
      rw cmp_using_eq_lt at nh, exact oadd_lt_oadd_2 h₁ nh },
    case ordering.gt {
      rw cmp_using_eq_gt at nh, exact oadd_lt_oadd_2 h₂ nh },
    rw cmp_using_eq_eq at nh,
    have := subtype.eq (eq_of_incomp nh), subst n₂,
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

theorem NF.of_dvd_omega_power {b e n a} (h : NF (oadd e n a)) (d : ω ^ b ∣ repr (oadd e n a)) :
  b ≤ repr e ∧ ω ^ b ∣ repr a :=
begin
  have := mt repr_inj.1 (λ h, by injection h : oadd e n a ≠ 0),
  have L := le_of_not_lt (λ l, not_le_of_lt (h.below_of_lt l).repr_lt (le_of_dvd this d)),
  simp at d,
  exact ⟨L, (dvd_add_iff $ (power_dvd_power _ L).mul_right _).1 d⟩
end

theorem NF.of_dvd_omega {e n a} (h : NF (oadd e n a)) :
   ω ∣ repr (oadd e n a) → repr e ≠ 0 ∧ ω ∣ repr a :=
by rw [← power_one ω, ← one_le_iff_ne_zero]; exact h.of_dvd_omega_power

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
  abstract {
    rw ← and_congr_right (λ h, @NF_below_iff_top_below _ h _),
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
| ⟨⟨b₁, h₁⟩⟩ ⟨⟨b₂, h₂⟩⟩ := ⟨(b₁.le_total b₂).elim
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
        power_pos (repr e') omega_pos).2 (nat_cast_le.2 n'.pos) } },
  { change e = e' at ee, substI e',
    rw [← add_assoc, ← ordinal.mul_add, ← nat.cast_add] }
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
      { simp [en], rwa [add_sub_add_cancel] },
      { simp [en, -repr],
        exact (ordinal.sub_eq_zero_iff_le.2 $ le_of_lt $ oadd_lt_oadd_2 h₁ $
          lt_of_le_of_ne (nat.sub_eq_zero_iff_le.1 mn) (mt pnat.eq en)).symm } },
    { simp [nat.succ_pnat, -nat.cast_succ],
      rw [(nat.sub_eq_iff_eq_add $ le_of_lt $ nat.lt_of_sub_eq_succ mn).1 mn,
          add_comm, nat.cast_add, ordinal.mul_add, add_assoc, add_sub_add_cancel],
      refine (ordinal.sub_eq_of_add_eq $ add_absorp h₂.snd'.repr_lt $
        le_trans _ (le_add_right _ _)).symm,
      simpa using mul_le_mul_left _ (nat_cast_le.2 $ nat.succ_pos _) } },
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

@[simp] theorem zero_mul (o : onote) : 0 * o = 0 := by cases o; refl
@[simp] theorem mul_zero (o : onote) : o * 0 = 0 := by cases o; refl

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
    { rw [repr_add, ordinal.add_lt_add_iff_left], exact h₂.lt } }
end

instance mul_NF : ∀ o₁ o₂ [NF o₁] [NF o₂], NF (o₁ * o₂)
| 0 o h₁ h₂ := by cases o; exact NF.zero
| (oadd e n a) o ⟨⟨b₁, hb₁⟩⟩ ⟨⟨b₂, hb₂⟩⟩ :=
  ⟨⟨_, oadd_mul_NF_below hb₁ hb₂⟩⟩

@[simp] theorem repr_mul : ∀ o₁ o₂ [NF o₁] [NF o₂], repr (o₁ * o₂) = repr o₁ * repr o₂
| 0               o               h₁ h₂ := by cases o; exact (ordinal.zero_mul _).symm
| (oadd e₁ n₁ a₁) 0               h₁ h₂ := (ordinal.mul_zero _).symm
| (oadd e₁ n₁ a₁) (oadd e₂ n₂ a₂) h₁ h₂ := begin
  have IH : repr (mul _ _) = _ := @repr_mul _ _ h₁ h₂.snd,
  conv {to_lhs, simp [(*)]},
  have ao : repr a₁ + ω ^ repr e₁ * (n₁:ℕ) = ω ^ repr e₁ * (n₁:ℕ),
  { apply add_absorp h₁.snd'.repr_lt,
    simpa using (mul_le_mul_iff_left $ power_pos _ omega_pos).2
      (nat_cast_le.2 n₁.2) },
  by_cases e0 : e₂ = 0; simp [e0, mul],
  { cases nat.exists_eq_succ_of_ne_zero n₂.ne_zero with x xe,
    simp [h₂.zero_of_zero e0, xe, -nat.cast_succ],
    rw [← nat_cast_succ x, add_mul_succ _ ao, mul_assoc] },
  { haveI := h₁.fst, haveI := h₂.fst,
    simp [IH, repr_add, power_add, ordinal.mul_add],
    rw ← mul_assoc, congr' 2,
    have := mt repr_inj.1 e0,
    rw [add_mul_limit ao (power_is_limit_left omega_is_limit this),
        mul_assoc, mul_omega_dvd (nat_cast_pos.2 n₁.pos) (nat_lt_omega _)],
    simpa using power_dvd_power ω (one_le_iff_ne_zero.2 this) },
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
exponentiation in `power` -/
def power_aux (e a0 a : onote) : ℕ → ℕ → onote
| _     0     := 0
| 0     (m+1) := oadd e m.succ_pnat 0
| (k+1) m     := scale (e + mul_nat a0 k) a + power_aux k m

/-- `power o₁ o₂` calculates the ordinal notation for
  the ordinal exponential `o₁ ^ o₂`. -/
def power (o₁ o₂ : onote) : onote :=
match split o₁ with
| (0, 0) := if o₂ = 0 then 1 else 0
| (0, 1) := 1
| (0, m+1) := let (b', k) := split' o₂ in
  oadd b' (@has_pow.pow ℕ+ _ _ m.succ_pnat k) 0
| (a@(oadd a0 _ _), m) := match split o₂ with
  | (b, 0) := oadd (a0 * b) 1 0
  | (b, k+1) := let eb := a0*b in
    scale (eb + mul_nat a0 k) a + power_aux eb a0 (mul_nat a m) k m
  end
end

instance : has_pow onote onote := ⟨power⟩

theorem power_def (o₁ o₂ : onote) : o₁ ^ o₂ = power._match_1 o₂ (split o₁) := rfl

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
      exact add_sub_cancel_of_le (one_le_iff_ne_zero.2 this) },
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
    have : ω ^ repr e = ω ^ (1 : ordinal.{0}) * ω ^ (repr e - 1),
    { have := mt repr_inj.1 e0,
      rw [← power_add, add_sub_cancel_of_le (one_le_iff_ne_zero.2 this)] },
    refine ⟨NF.oadd (by apply_instance) _ _, _⟩,
    { simp at this ⊢,
      refine IH₁.below_of_lt' ((mul_lt_mul_iff_left omega_pos).1 $
        lt_of_le_of_lt (le_add_right _ m') _),
      rw [← this, ← IH₂], exact h.snd'.repr_lt },
    { rw this, simp [ordinal.mul_add, mul_assoc, add_assoc] } }
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
  refine add_lt_omega_power h₁.snd'.repr_lt (lt_of_lt_of_le (nat_lt_omega _) _),
  simpa using power_le_power_right omega_pos (one_le_iff_ne_zero.2 e0),
end

@[simp] theorem mul_nat_eq_mul (n o) : mul_nat o n = o * of_nat n :=
by cases o; cases n; refl

instance NF_mul_nat (o) [NF o] (n) : NF (mul_nat o n) :=
by simp; apply_instance

instance NF_power_aux (e a0 a) [NF e] [NF a0] [NF a] : ∀ k m, NF (power_aux e a0 a k m)
| k     0     := by cases k; exact NF.zero
| 0     (m+1) := NF.oadd_zero _ _
| (k+1) (m+1) := by haveI := NF_power_aux k;
  simp [power_aux, nat.succ_ne_zero]; apply_instance

instance NF_power (o₁ o₂) [NF o₁] [NF o₂] : NF (o₁ ^ o₂) :=
begin
  cases e₁ : split o₁ with a m,
  have na := (NF_repr_split e₁).1,
  cases e₂ : split' o₂ with b' k,
  haveI := (NF_repr_split' e₂).1,
  casesI a with a0 n a',
  { cases m with m,
    { by_cases o₂ = 0; simp [pow, power, *]; apply_instance },
    { by_cases m = 0,
      { simp only [pow, power, *, zero_def], apply_instance },
      { simp [pow, power, *, - npow_eq_pow], apply_instance } } },
  { simp [pow, power, e₁, e₂, split_eq_scale_split' e₂],
    have := na.fst,
    cases k with k; simp [succ_eq_add_one, power]; resetI; apply_instance }
end

theorem scale_power_aux (e a0 a : onote) [NF e] [NF a0] [NF a] :
  ∀ k m, repr (power_aux e a0 a k m) = ω ^ repr e * repr (power_aux 0 a0 a k m)
| 0     m := by cases m; simp [power_aux]
| (k+1) m := by by_cases m = 0; simp [h, power_aux,
  ordinal.mul_add, power_add, mul_assoc, scale_power_aux]

theorem repr_power_aux₁ {e a} [Ne : NF e] [Na : NF a] {a' : ordinal}
  (e0 : repr e ≠ 0) (h : a' < ω ^ repr e) (aa : repr a = a') (n : ℕ+) :
  (ω ^ repr e * (n:ℕ) + a') ^ ω = (ω ^ repr e) ^ ω :=
begin
  subst aa,
  have No := Ne.oadd n (Na.below_of_lt' h),
  have := omega_le_oadd e n a, unfold repr at this,
  refine le_antisymm _ (power_le_power_left _ this),
  apply (power_le_of_limit
    (ne_of_gt $ lt_of_lt_of_le (power_pos _ omega_pos) this) omega_is_limit).2,
  intros b l,
  have := (No.below_of_lt (lt_succ_self _)).repr_lt, unfold repr at this,
  apply le_trans (power_le_power_left b $ le_of_lt this),
  rw [← power_mul, ← power_mul],
  apply power_le_power_right omega_pos,
  cases le_or_lt ω (repr e) with h h,
  { apply le_trans (mul_le_mul_left _ $ le_of_lt $ lt_succ_self _),
    rw [succ, add_mul_succ _ (one_add_of_omega_le h), ← succ,
        succ_le, mul_lt_mul_iff_left (ordinal.pos_iff_ne_zero.2 e0)],
    exact omega_is_limit.2 _ l },
  { refine le_trans (le_of_lt $ mul_lt_omega (omega_is_limit.2 _ h) l) _,
    simpa using mul_le_mul_right ω (one_le_iff_ne_zero.2 e0) }
end

section
local infixr ^ := @pow ordinal.{0} ordinal ordinal.has_pow

theorem repr_power_aux₂ {a0 a'} [N0 : NF a0] [Na' : NF a'] (m : ℕ)
  (d : ω ∣ repr a')
  (e0 : repr a0 ≠ 0) (h : repr a' + m < ω ^ repr a0) (n : ℕ+) (k : ℕ) :
  let R := repr (power_aux 0 a0 (oadd a0 n a' * of_nat m) k m) in
  (k ≠ 0 → R < (ω ^ repr a0) ^ succ k) ∧
  (ω ^ repr a0) ^ k * (ω ^ repr a0 * (n:ℕ) + repr a') + R =
    (ω ^ repr a0 * (n:ℕ) + repr a' + m) ^ succ k :=
begin
  intro,
  haveI No : NF (oadd a0 n a') :=
    N0.oadd n (Na'.below_of_lt' $ lt_of_le_of_lt (le_add_right _ _) h),
  induction k with k IH, {cases m; simp [power_aux, R]},
  rename R R', let R := repr (power_aux 0 a0 (oadd a0 n a' * of_nat m) k m),
  let ω0 := ω ^ repr a0, let α' := ω0 * n + repr a',
  change (k ≠ 0 → R < ω0 ^ succ k) ∧ ω0 ^ k * α' + R = (α' + m) ^ succ k at IH,
  have RR : R' = ω0 ^ k * (α' * m) + R,
  { by_cases m = 0; simp [h, R', power_aux, R, power_mul],
    { cases k; simp [power_aux] }, { refl } },
  have α0 : 0 < α', {simpa [α', lt_def, repr] using oadd_pos a0 n a'},
  have ω00 : 0 < ω0 ^ k := power_pos _ (power_pos _ omega_pos),
  have Rl : R < ω ^ (repr a0 * succ ↑k),
  { by_cases k0 : k = 0,
    { simp [k0],
      refine lt_of_lt_of_le _ (power_le_power_right omega_pos (one_le_iff_ne_zero.2 e0)),
      cases m with m; simp [k0, R, power_aux, omega_pos],
      rw [← nat.cast_succ], apply nat_lt_omega },
    { rw power_mul, exact IH.1 k0 } },
  refine ⟨λ_, _, _⟩,
  { rw [RR, ← power_mul _ _ (succ k.succ)],
    have e0 := ordinal.pos_iff_ne_zero.2 e0,
    have rr0 := lt_of_lt_of_le e0 (le_add_left _ _),
    apply add_lt_omega_power,
    { simp [power_mul, ω0, power_add, mul_assoc],
      rw [mul_lt_mul_iff_left ω00, ← ordinal.power_add],
      have := (No.below_of_lt _).repr_lt, unfold repr at this,
      refine mul_lt_omega_power rr0 this (nat_lt_omega _),
      simpa using (add_lt_add_iff_left (repr a0)).2 e0 },
    { refine lt_of_lt_of_le Rl (power_le_power_right omega_pos $
        mul_le_mul_left _ $ succ_le_succ.2 $ nat_cast_le.2 $ le_of_lt k.lt_succ_self) } },
  refine calc
        ω0 ^ k.succ * α' + R'
      = ω0 ^ succ k * α' + (ω0 ^ k * α' * m + R) : by rw [nat_cast_succ, RR, ← mul_assoc]
  ... = (ω0 ^ k * α' + R) * α' + (ω0 ^ k * α' + R) * m : _
  ... = (α' + m) ^ succ k.succ : by rw [← ordinal.mul_add, ← nat_cast_succ, power_succ, IH.2],
  congr' 1,
  { have αd : ω ∣ α' := dvd_add (dvd_mul_of_dvd_left
      (by simpa using power_dvd_power ω (one_le_iff_ne_zero.2 e0)) _) d,
    rw [ordinal.mul_add (ω0 ^ k), add_assoc, ← mul_assoc, ← power_succ,
        add_mul_limit _ (is_limit_iff_omega_dvd.2 ⟨ne_of_gt α0, αd⟩), mul_assoc,
        @mul_omega_dvd n (nat_cast_pos.2 n.pos) (nat_lt_omega _) _ αd],
    apply @add_absorp _ (repr a0 * succ k),
    { refine add_lt_omega_power _ Rl,
      rw [power_mul, power_succ, mul_lt_mul_iff_left ω00],
      exact No.snd'.repr_lt },
    { have := mul_le_mul_left (ω0 ^ succ k) (one_le_iff_pos.2 $ nat_cast_pos.2 n.pos),
      rw power_mul, simpa [-power_succ] } },
  { cases m,
    { have : R = 0, {cases k; simp [R, power_aux]}, simp [this] },
    { rw [← nat_cast_succ, add_mul_succ],
      apply add_absorp Rl,
      rw [power_mul, power_succ],
      apply ordinal.mul_le_mul_left,
      simpa [α', repr] using omega_le_oadd a0 n a' } }
end

end

theorem repr_power (o₁ o₂) [NF o₁] [NF o₂] : repr (o₁ ^ o₂) = repr o₁ ^ repr o₂ :=
begin
  cases e₁ : split o₁ with a m,
  cases NF_repr_split e₁ with N₁ r₁,
  cases a with a0 n a',
  { cases m with m,
    { by_cases o₂ = 0; simp [power_def, power, e₁, h, r₁],
      have := mt repr_inj.1 h, rw zero_power this },
    { cases e₂ : split' o₂ with b' k,
      cases NF_repr_split' e₂ with _ r₂,
      by_cases m = 0; simp [power_def, power, e₁, h, r₁, e₂, r₂, -nat.cast_succ],
      rw [power_add, power_mul, power_omega _ (nat_lt_omega _)],
      simpa using nat_cast_lt.2 (nat.succ_lt_succ $ pos_iff_ne_zero.2 h) } },
  { haveI := N₁.fst, haveI := N₁.snd,
    cases N₁.of_dvd_omega (split_dvd e₁) with a00 ad,
    have al := split_add_lt e₁,
    have aa : repr (a' + of_nat m) = repr a' + m, {simp},
    cases e₂ : split' o₂ with b' k,
    cases NF_repr_split' e₂ with _ r₂,
    simp [power_def, power, e₁, r₁, split_eq_scale_split' e₂],
    cases k with k; resetI,
    { simp [power, r₂, power_mul, repr_power_aux₁ a00 al aa, add_assoc] },
    { simp [succ_eq_add_one, power, r₂, power_add, power_mul, mul_assoc, add_assoc],
      rw [repr_power_aux₁ a00 al aa, scale_power_aux], simp [power_mul],
      rw [← ordinal.mul_add, ← add_assoc (ω ^ repr a0 * (n:ℕ))], congr' 1,
      rw [← power_succ],
      exact (repr_power_aux₂ _ ad a00 al _ _).2 } }
end

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
def power (x y : nonote) := mk (x.1.power y.1)

theorem repr_power (a b) : repr (power a b) = (repr a).power (repr b) :=
onote.repr_power a.1 b.1

end nonote
