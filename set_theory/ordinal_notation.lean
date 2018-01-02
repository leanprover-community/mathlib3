/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Ordinal notations (constructive ordinal arithmetic).
-/
import set_theory.ordinal data.pnat
open ordinal

local infixr ` ^ ` := power
local notation `ω` := omega

@[derive decidable_eq]
inductive onote : Type
| zero : onote
| oadd : onote → ℕ+ → onote → onote

namespace onote

instance : has_zero onote := ⟨zero⟩
@[simp] theorem zero_def : zero = 0 := rfl

instance : has_one onote := ⟨oadd 0 1 0⟩

@[simp] noncomputable def repr : onote → ordinal
| 0 := 0
| (oadd e n o) := ω ^ repr e * n.1 + repr o

instance : preorder onote :=
{ le       := λ x y, repr.{0} x ≤ repr y,
  lt       := λ x y, repr.{0} x < repr y,
  le_refl  := λ a, @le_refl ordinal _ _,
  le_trans := λ a b c, @le_trans ordinal _ _ _ _,
  lt_iff_le_not_le := λ a b, @lt_iff_le_not_le ordinal _ _ _ }

theorem lt_def {x y : onote} : x < y ↔ repr.{0} x < repr y := iff.rfl
theorem le_def {x y : onote} : x ≤ y ↔ repr.{0} x ≤ repr y := iff.rfl

@[simp] def of_nat : ℕ → onote
| 0            := 0
| (nat.succ n) := oadd 0 n.succ_pnat 0

@[simp] theorem of_nat_one : of_nat 1 = 1 := rfl

@[simp] theorem repr_of_nat (n : ℕ) : repr (of_nat n) = n :=
by cases n; simp [nat.succ_pnat]

@[simp] theorem repr_one : repr 1 = 1 :=
by simpa using repr_of_nat 1
/-
@[simp] def add_nat : onote → ℕ → onote
| 0            n := of_nat n
| (oadd e m o) n :=
  if e = 0 then oadd 0 (m + n) 0 else oadd e m (add_nat o n)

@[simp] theorem repr_add_nat (o n) : repr (add_nat o n) = repr o + n :=
by induction o; simp *

def succ (o : onote) : onote := add_nat o 1

@[simp] theorem succ_zero : succ 0 = 1 := rfl

@[simp] theorem repr_succ (o) : repr (succ o) = (repr o).succ :=
by simpa [succ, ordinal.succ]

theorem lt_succ_self (o : onote) : o < succ o :=
by simp [lt_def, ordinal.lt_succ_self]

theorem succ_le {a b : onote} : succ a ≤ b ↔ a < b :=
by simp [lt_def, le_def, succ_le]
-/
theorem omega_le_oadd (e n o) : ω ^ repr e ≤ repr (oadd e n o) :=
le_trans
  (by simpa using (mul_le_mul_iff_left $
     power_pos (repr e) omega_pos).2 (nat_cast_le.2 n.2))
  (le_add_right _ _)

theorem oadd_pos (e n o) : 0 < oadd e n o :=
@lt_of_lt_of_le _ _ _ _ _ (power_pos _ omega_pos)
  (omega_le_oadd _ _ _)

def cmp : onote → onote → ordering
| 0 0 := ordering.eq
| _ 0 := ordering.gt
| 0 _ := ordering.lt
| o₁@(oadd e₁ n₁ a₁) o₂@(oadd e₂ n₂ a₂) :=
  (cmp e₁ e₂).or_else $ (_root_.cmp n₁.1 n₂.1).or_else (cmp a₁ a₂)

theorem eq_of_cmp_eq : ∀ {o₁ o₂}, cmp o₁ o₂ = ordering.eq → o₁ = o₂
| 0            0 h := rfl
| (oadd e n a) 0 h := by injection h
| 0 (oadd e n a) h := by injection h
| o₁@(oadd e₁ n₁ a₁) o₂@(oadd e₂ n₂ a₂) h := begin
  revert h, simp [cmp],
  cases h₁ : cmp e₁ e₂; intro h; try {cases h},
  have := eq_of_cmp_eq h₁, subst e₂,
  revert h, cases h₂ : _root_.cmp n₁.1 n₂.1; intro h; try {cases h},
  have := eq_of_cmp_eq h, subst a₂,
  rw [_root_.cmp, cmp_using_eq_eq] at h₂,
  have := subtype.eq (eq_of_incomp h₂), subst n₂
end

theorem zero_lt_one : (0 : onote) < 1 :=
by rw [lt_def, repr, repr_one]; exact zero_lt_one

inductive NF_below : onote → ordinal.{0} → Prop
| zero {b} : NF_below 0 b
| oadd' {e n o eb b} : NF_below e eb →
  NF_below o (repr e) → repr e < b → NF_below (oadd e n o) b

def NF (o : onote) := Exists (NF_below o)

theorem NF.zero : NF 0 := ⟨0, NF_below.zero⟩

theorem NF_below.oadd {e n o b} : NF e →
  NF_below o (repr e) → repr e < b → NF_below (oadd e n o) b
| ⟨eb, h⟩ := NF_below.oadd' h

theorem NF_below.fst {e n o b} (h : NF_below (oadd e n o) b) : NF e :=
by cases h with _ _ _ _ eb _ h₁ h₂ h₃; exact ⟨_, h₁⟩

theorem NF.fst {e n o} : NF (oadd e n o) → NF e
| ⟨b, h⟩ := h.fst

theorem NF_below.snd {e n o b} (h : NF_below (oadd e n o) b) : NF_below o (repr e) :=
by cases h with _ _ _ _ eb _ h₁ h₂ h₃; exact h₂

theorem NF.snd' {e n o} : NF (oadd e n o) → NF_below o (repr e)
| ⟨b, h⟩ := h.snd

theorem NF.snd {e n o} (h : NF (oadd e n o)) : NF o :=
⟨_, h.snd'⟩

theorem NF.oadd {e n o} (h₁ : NF e)
  (h₂ : NF_below o (repr e)) : NF (oadd e n o) :=
⟨_, NF_below.oadd h₁ h₂ (ordinal.lt_succ_self _)⟩

theorem NF_below.lt {e n o b} (h : NF_below (oadd e n o) b) : repr e < b :=
by cases h with _ _ _ _ eb _ h₁ h₂ h₃; exact h₃

theorem NF_below_zero : ∀ {o}, NF_below o 0 ↔ o = 0
| 0            := ⟨λ _, rfl, λ _, NF_below.zero⟩
| (oadd e n a) := ⟨λ h, (not_le_of_lt h.lt).elim (zero_le _),
                   λ e, e.symm ▸ NF_below.zero⟩

theorem NF_below.repr_lt {o b} (h : NF_below o b) : repr.{0} o < ω ^ b :=
begin
  induction h with _ e n o eb b h₁ h₂ h₃ _ IH,
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
  induction h with _ e n o eb b h₁ h₂ h₃ _ IH; constructor,
  exacts [h₁, h₂, lt_of_lt_of_le h₃ bb]
end

theorem NF.below_of_lt {e n o b} (H : repr e < b) : NF (oadd e n o) → NF_below (oadd e n o) b
| ⟨b, h⟩ := by cases h with _ _ _ _ eb _ h₁ h₂ h₃;
  exact NF_below.oadd' h₁ h₂ H

theorem NF_below_of_nat : ∀ n, NF_below (of_nat n) 1
| 0            := NF_below.zero
| (nat.succ n) := NF_below.oadd NF.zero NF_below.zero ordinal.zero_lt_one

theorem NF_of_nat (n) : NF (of_nat n) := ⟨_, NF_below_of_nat n⟩

/-
theorem NF_below_add_nat : ∀ {o b} n, 0 < b → NF_below o b → NF_below (add_nat o n) b
| 0            b n b0 h := (NF_below_of_nat _).mono $ by rwa [← succ_zero, succ_le]
| (oadd e m a) b n b0 h := by simp [add_nat]; exact
  NF_below.oadd' h.fst (NF_below_add_nat _ _ _) _

theorem NF_add_nat : ∀ {o} n, NF o → NF (add_nat o n)
| 0            n h := NF_of_nat _
| (oadd e m a) n h := by simp [add_nat]; exact NF.oadd h.fst _
-/

theorem oadd_lt_oadd_1 {e₁ n₁ o₁ e₂ n₂ o₂}
  (h₁ : NF (oadd e₁ n₁ o₁)) (h₂ : NF (oadd e₂ n₂ o₂))
  (h : e₁ < e₂) : oadd e₁ n₁ o₁ < oadd e₂ n₂ o₂ :=
@lt_of_lt_of_le _ _ _ _ _ ((h₁.below_of_lt h).repr_lt) (omega_le_oadd _ _ _)

theorem oadd_lt_oadd_2 {e n₁ o₁ n₂ o₂}
  (h₁ : NF (oadd e n₁ o₁)) (h₂ : NF (oadd e n₂ o₂))
  (h : n₁.1 < n₂.1) : oadd e n₁ o₁ < oadd e n₂ o₂ :=
begin
  simp [lt_def],
  refine lt_of_lt_of_le ((ordinal.add_lt_add_iff_left _).2 h₁.snd'.repr_lt)
    (le_trans _ (le_add_right _ _)),
  rwa [← mul_succ, mul_le_mul_iff_left (power_pos _ omega_pos),
       ordinal.succ_le, nat_cast_lt]
end

theorem oadd_lt_oadd_3 {e n o₁ o₂}
  (h₁ : NF (oadd e n o₁)) (h₂ : NF (oadd e n o₂))
  (h : o₁ < o₂) : oadd e n o₁ < oadd e n o₂ :=
(ordinal.add_lt_add_iff_left _).2 h

theorem cmp_compares : ∀ {a b : onote}, NF a → NF b →
  (cmp a b).compares a b
| 0 0 h₁ h₂ := rfl
| (oadd e n a) 0 h₁ h₂ := oadd_pos _ _ _
| 0 (oadd e n a) h₁ h₂ := oadd_pos _ _ _
| o₁@(oadd e₁ n₁ a₁) o₂@(oadd e₂ n₂ a₂) h₁ h₂ := begin
    rw cmp,
    have IHe := cmp_compares h₁.fst h₂.fst,
    cases cmp e₁ e₂,
    case ordering.lt { exact oadd_lt_oadd_1 h₁ h₂ IHe },
    case ordering.gt { exact oadd_lt_oadd_1 h₂ h₁ IHe },
    change e₁ = e₂ at IHe, subst IHe,
    unfold _root_.cmp, cases nh : cmp_using (<) n₁.1 n₂.1,
    case ordering.lt {
      rw cmp_using_eq_lt at nh, exact oadd_lt_oadd_2 h₁ h₂ nh },
    case ordering.gt {
      rw cmp_using_eq_gt at nh, exact oadd_lt_oadd_2 h₂ h₁ nh },
    rw cmp_using_eq_eq at nh,
    have := subtype.eq (eq_of_incomp nh), subst n₂,
    have IHa := cmp_compares h₁.snd h₂.snd,
    cases cmp a₁ a₂,
    case ordering.lt { exact oadd_lt_oadd_3 h₁ h₂ IHa },
    case ordering.gt { exact oadd_lt_oadd_3 h₂ h₁ IHa },
    change a₁ = a₂ at IHa, subst IHa, exact rfl
  end

theorem repr_inj {a b} (ha : NF a) (hb : NF b) : repr.{0} a = repr b ↔ a = b :=
⟨match cmp a b, cmp_compares ha hb with
 | ordering.lt, (h : repr a < repr b), e := (ne_of_lt h e).elim
 | ordering.gt, (h : repr a > repr b), e := (ne_of_gt h e).elim
 | ordering.eq, h, e := h
 end, congr_arg _⟩

def top_below (b) : onote → Prop
| 0            := true
| (oadd e n a) := cmp e b = ordering.lt

instance decidable_top_below : decidable_rel top_below :=
by intros b o; cases o; delta top_below; apply_instance

theorem NF_below_iff_top_below {b} (hb : NF b) : ∀ {o},
  NF_below o (repr b) ↔ NF o ∧ top_below b o
| 0            := ⟨λ h, ⟨⟨_, h⟩, trivial⟩, λ _, NF_below.zero⟩
| (oadd e n a) :=
  ⟨λ h, ⟨⟨_, h⟩, (cmp_compares h.fst hb).eq_lt.2 h.lt⟩,
   λ ⟨h₁, h₂⟩, h₁.below_of_lt $ (cmp_compares h₁.fst hb).eq_lt.1 h₂⟩

instance decidable_NF : decidable_pred NF
| 0            := is_true NF.zero
| (oadd e n a) := begin
  have := decidable_NF e,
  have := decidable_NF a,
  apply decidable_of_iff (NF e ∧ NF a ∧ top_below e a),
  abstract {
    rw ← and_congr_right (λ h, NF_below_iff_top_below h),
    exact ⟨λ ⟨h₁, h₂⟩, NF.oadd h₁ h₂, λ h, ⟨h.fst, h.snd'⟩⟩ },
end

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

def sub : onote → onote → onote
| 0 o := 0
| o 0 := o
| o₁@(oadd e₁ n₁ a₁) (oadd e₂ n₂ a₂) := match cmp e₁ e₂ with
  | ordering.lt := 0
  | ordering.gt := o₁
  | ordering.eq := match n₁.1 - n₂.1 with
    | 0            := if n₁.1 = n₂.1 then sub a₁ a₂ else 0
    | (nat.succ k) := oadd e₁ k.succ_pnat a₁
  end
end

instance : has_add onote := ⟨add⟩
instance : has_sub onote := ⟨sub⟩

theorem add_NF_below {b} : ∀ {o₁ o₂}, NF_below o₁ b → NF_below o₂ b → NF_below (o₁ + o₂) b
| 0            o h₁ h₂ := h₂
| (oadd e n a) o h₁ h₂ := begin
  have h' := add_NF_below (h₁.snd.mono $ le_of_lt h₁.lt) h₂,
  simp [(+), add] at h' ⊢,
  cases add a o with e' n' a',
  { exact NF_below.oadd h₁.fst NF_below.zero h₁.lt },
  simp [add], have := cmp_compares h₁.fst h'.fst,
  cases cmp e e'; simp [add],
  { exact h' },
  { simp at this, subst e',
    exact NF_below.oadd h'.fst h'.snd h'.lt },
  { exact NF_below.oadd h₁.fst (NF.below_of_lt this ⟨_, h'⟩) h₁.lt }
end

theorem add_NF {o₁ o₂} : NF o₁ → NF o₂ → NF (o₁ + o₂)
| ⟨b₁, h₁⟩ ⟨b₂, h₂⟩ := (b₁.le_total b₂).elim
  (λ h, ⟨b₂, add_NF_below (h₁.mono h) h₂⟩)
  (λ h, ⟨b₁, add_NF_below h₁ (h₂.mono h)⟩)

theorem repr_add : ∀ {o₁ o₂}, NF o₁ → NF o₂ → repr.{0} (o₁ + o₂) = repr o₁ + repr o₂
| 0            o h₁ h₂ := (zero_add _).symm
| (oadd e n a) o h₁ h₂ := begin
  have h' := repr_add h₁.snd h₂,
  conv at h' in (_+o) {simp [(+)]},
  have nf := add_NF h₁.snd h₂,
  conv at nf in (_+o) {simp [(+)]},
  conv in (_+o) {simp [(+), add]},
  cases add a o with e' n' a'; simp [add, h'.symm],
  have := cmp_compares h₁.fst nf.fst,
  cases cmp e e'; simp [add],
  { rw [← add_assoc, @add_absorp _ (repr e') (ω ^ repr e' * n'.1)],
    { exact lt_of_le_of_lt (le_add_right _ _) (h₁.below_of_lt this).repr_lt },
    { simpa using (mul_le_mul_iff_left $
        power_pos (repr e') omega_pos).2 (nat_cast_le.2 n'.2) } },
  { change e = e' at this, subst e',
    rw [← add_assoc, ← ordinal.mul_add, ← nat.cast_add], refl }
end

def mul : onote → onote → onote
| 0 _ := 0
| _ 0 := 0
| o₁@(oadd e₁ n₁ a₁) (oadd e₂ n₂ a₂) :=
  if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else
  oadd (e₁ + e₂) n₂ (mul o₁ a₂)

instance : has_mul onote := ⟨mul⟩

theorem oadd_mul_NF_below {e₁ n₁ a₁ b₁} (h₁ : NF_below (oadd e₁ n₁ a₁) b₁) :
  ∀ {o₂ b₂}, NF_below o₂ b₂ → NF_below (oadd e₁ n₁ a₁ * o₂) (repr e₁ + b₂)
| 0 b₂ h₂ := NF_below.zero
| (oadd e₂ n₂ a₂) b₂ h₂ := begin
  have IH := oadd_mul_NF_below h₂.snd,
  simp [(*)] at IH ⊢,
  by_cases e0 : e₂ = 0; simp [e0, mul],
  { apply NF_below.oadd h₁.fst h₁.snd,
    simpa using (add_lt_add_iff_left (repr e₁)).2
      (lt_of_le_of_lt (ordinal.zero_le _) h₂.lt) },
  { apply NF_below.oadd (add_NF h₁.fst h₂.fst),
    { rwa repr_add h₁.fst h₂.fst },
    { rw [repr_add h₁.fst h₂.fst, ordinal.add_lt_add_iff_left],
      exact h₂.lt } }
end

theorem mul_NF : ∀ {o₁ o₂}, NF o₁ → NF o₂ → NF (o₁ * o₂)
| 0 o h₁ h₂ := by cases o; exact NF.zero
| (oadd e n a) o ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ :=
  ⟨_, oadd_mul_NF_below hb₁ hb₂⟩

theorem repr_mul : ∀ {o₁ o₂}, NF o₁ → NF o₂ → repr.{0} (o₁ * o₂) = repr o₁ * repr o₂
| 0               o               h₁ h₂ := by cases o; exact (ordinal.zero_mul _).symm
| (oadd e₁ n₁ a₁) 0               h₁ h₂ := (ordinal.mul_zero _).symm
| (oadd e₁ n₁ a₁) (oadd e₂ n₂ a₂) h₁ h₂ := begin
  have IH := repr_mul h₁ h₂.snd,
  change repr (mul _ _) = _ at IH,
  conv {to_lhs, simp [(*)]},
  have ao : repr a₁ + ω ^ repr e₁ * n₁.1 = ω ^ repr e₁ * n₁.1,
  { apply add_absorp h₁.snd'.repr_lt,
    simpa using (mul_le_mul_iff_left $ power_pos _ omega_pos).2
      (nat_cast_le.2 n₁.2) },
  by_cases e0 : e₂ = 0; simp [e0, mul],
  { have := h₂.snd', simp [e0, NF_below_zero] at this,
    change (n₁*n₂).1 with n₁.1 * n₂.1,
    cases nat.exists_eq_succ_of_ne_zero n₂.ne_zero with x xe,
    simp [this, xe, -nat.cast_succ],
    rw [← succ_nat_cast x, add_mul_succ _ ao, ordinal.mul_assoc] },
  { simp [IH, repr_add h₁.fst h₂.fst, power_add, ordinal.mul_add],
    rw ← ordinal.mul_assoc, congr_n 2,
    have : repr e₂ ≠ 0 := mt (repr_inj h₂.fst NF.zero).1 e0,
    rw [add_mul_limit ao (power_is_limit_left omega_is_limit this),
        ordinal.mul_assoc, mul_omega_power (nat_cast_pos.2 n₁.2)
          (nat_lt_omega _) (pos_iff_ne_zero.2 this)] },
end

def split' : onote → onote × nat
| 0            := (0, 0)
| (oadd e n a) := if e = 0 then (0, n) else
  let (a', m) := split' a in (oadd (e - 1) n a', m)

def split : onote → onote × nat
| 0            := (0, 0)
| (oadd e n a) := if e = 0 then (0, n) else
  let (a', m) := split a in (oadd e n a', m)

def scale (E : onote) : onote → ℕ+ → onote
| 0            m := 0
| (oadd e n a) m := oadd (E + e) (n * m) (scale a m)

def power_aux (m : nat) (e a0 a : onote) : nat → nat → onote
| 0     x := oadd e x 0
| (k+1) x := scale (e + scale 0 a0 k) a x + power_aux k (x * m)

def power (o₁ o₂ : onote) : onote :=
match split o₁ with
| (0, m) := let (b', k) := split' o₂ in oadd b' (m.pow k) 0
| (o@(oadd e _ _), m) :=
  let (b, k) := split o₂ in power_aux m (e * b) e o k 1
end

end onote

def nonote := {o : onote // o.NF}

instance : decidable_eq nonote := by unfold nonote; apply_instance

namespace nonote
open onote

noncomputable def repr (o : nonote) : ordinal := o.1.repr

instance : preorder nonote :=
{ le       := λ x y, repr.{0} x ≤ repr y,
  lt       := λ x y, repr.{0} x < repr y,
  le_refl  := λ a, @le_refl ordinal _ _,
  le_trans := λ a b c, @le_trans ordinal _ _ _ _,
  lt_iff_le_not_le := λ a b, @lt_iff_le_not_le ordinal _ _ _ }

instance : has_zero nonote := ⟨⟨0, NF.zero⟩⟩

def of_nat (n : ℕ) : nonote := ⟨of_nat n, _, NF_below_of_nat _⟩

def cmp (a b : nonote) : ordering :=
cmp a.1 b.1 

theorem cmp_compares : ∀ a b : nonote, (cmp a b).compares a b
| ⟨a, ha⟩ ⟨b, hb⟩ := begin
  dsimp [cmp], have := onote.cmp_compares ha hb,
  cases onote.cmp a b; try {exact this},
  exact subtype.mk_eq_mk.2 this
end

instance : linear_order nonote :=
{ le_antisymm := λ a b, match cmp a b, cmp_compares a b with
    | ordering.lt, h, h₁, h₂ := (not_lt_of_le h₂).elim h
    | ordering.eq, h, h₁, h₂ := h
    | ordering.gt, h, h₁, h₂ := (not_lt_of_le h₁).elim h
    end,
  le_total := λ a b, match cmp a b, cmp_compares a b with
    | ordering.lt, h := or.inl (le_of_lt h)
    | ordering.eq, h := or.inl (le_of_eq h)
    | ordering.gt, h := or.inr (le_of_lt h)
    end,
  ..nonote.preorder }

instance decidable_lt : @decidable_rel nonote (<)
| a b := decidable_of_iff _ (cmp_compares a b).eq_lt

instance : decidable_linear_order nonote :=
{ decidable_le := λ a b, decidable_of_iff _ not_lt,
  decidable_lt := nonote.decidable_lt,
  ..nonote.linear_order }

instance : has_add nonote := ⟨λ x y, ⟨_, add_NF x.2 y.2⟩⟩

theorem repr_add : ∀ {o₁ o₂}, repr.{0} (o₁ + o₂) = repr o₁ + repr o₂
| ⟨a, ha⟩ ⟨b, hb⟩ := onote.repr_add ha hb

instance : has_mul nonote := ⟨λ x y, ⟨_, mul_NF x.2 y.2⟩⟩

theorem repr_mul : ∀ {o₁ o₂}, repr.{0} (o₁ * o₂) = repr o₁ * repr o₂
| ⟨a, ha⟩ ⟨b, hb⟩ := onote.repr_mul ha hb

end nonote
