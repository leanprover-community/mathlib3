/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

More about finite numbers.
-/
import data.nat.basic

open fin nat

/-- `fin 0` is empty -/
def fin_zero_elim {C : Sort*} : fin 0 → C :=
λ x, false.elim $ nat.not_lt_zero x.1 x.2

namespace fin
variables {n m : ℕ} {a b : fin n}

@[simp] protected lemma eta (a : fin n) (h : a.1 < n) : (⟨a.1, h⟩ : fin n) = a :=
by cases a; refl

protected lemma ext_iff (a b : fin n) : a = b ↔ a.val = b.val :=
iff.intro (congr_arg _) fin.eq_of_veq

lemma eq_iff_veq (a b : fin n) : a = b ↔ a.1 = b.1 :=
⟨veq_of_eq, eq_of_veq⟩

instance fin_to_nat (n : ℕ) : has_coe (fin n) nat := ⟨fin.val⟩

instance {n : ℕ} : decidable_linear_order (fin n) :=
{ le_refl := λ a, @le_refl ℕ _ _,
  le_trans := λ a b c, @le_trans ℕ _ _ _ _,
  le_antisymm := λ a b ha hb, fin.eq_of_veq $ le_antisymm ha hb,
  le_total := λ a b, @le_total ℕ _ _ _,
  lt_iff_le_not_le := λ a b, @lt_iff_le_not_le ℕ _ _ _,
  decidable_le := fin.decidable_le,
  ..fin.has_le,
  ..fin.has_lt }

lemma zero_le (a : fin (n + 1)) : 0 ≤ a := zero_le a.1

lemma lt_iff_val_lt_val : a < b ↔ a.val < b.val := iff.refl _

lemma le_iff_val_le_val : a ≤ b ↔ a.val ≤ b.val := iff.refl _

@[simp] lemma succ_val (j : fin n) : j.succ.val = j.val.succ :=
by cases j; simp [fin.succ]

protected theorem succ.inj (p : fin.succ a = fin.succ b) : a = b :=
by cases a; cases b; exact eq_of_veq (nat.succ.inj (veq_of_eq p))

@[simp] lemma pred_val (j : fin (n+1)) (h : j ≠ 0) : (j.pred h).val = j.val.pred :=
by cases j; simp [fin.pred]

@[simp] lemma succ_pred : ∀(i : fin (n+1)) (h : i ≠ 0), (i.pred h).succ = i
| ⟨0,     h⟩ hi := by contradiction
| ⟨n + 1, h⟩ hi := rfl

@[simp] lemma pred_succ (i : fin n) {h : i.succ ≠ 0} : i.succ.pred h = i :=
by cases i; refl

@[simp] lemma pred_inj :
  ∀ {a b : fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a.pred ha = b.pred hb ↔ a = b
| ⟨0,   _⟩  b         ha hb := by contradiction
| ⟨i+1, _⟩  ⟨0,   _⟩  ha hb := by contradiction
| ⟨i+1, hi⟩ ⟨j+1, hj⟩ ha hb := by simp [fin.eq_iff_veq]

/-- The greatest value of `fin (n+1)` -/
def last (n : ℕ) : fin (n+1) := ⟨_, n.lt_succ_self⟩

/-- `cast_lt i h` embeds `i` into a `fin` where `h` proves it belongs into.  -/
def cast_lt (i : fin m) (h : i.1 < n) : fin n := ⟨i.1, h⟩

/-- `cast_le h i` embeds `i` into a larger `fin` type.  -/
def cast_le (h : n ≤ m) (a : fin n) : fin m := cast_lt a (lt_of_lt_of_le a.2 h)

/-- `cast eq i` embeds `i` into a equal `fin` type. -/
def cast (eq : n = m): fin n → fin m := cast_le $ le_of_eq eq

/-- `cast_add m i` embedds `i` in `fin (n+m)`. -/
def cast_add (m) : fin n → fin (n + m) := cast_le $ le_add_right n m

/-- `cast_succ i` embedds `i` in `fin (n+1)`. -/
def cast_succ : fin n → fin (n + 1) := cast_add 1

/-- `succ_above p i` embeds into `fin (n + 1)` with a hole around `p`. -/
def succ_above (p : fin (n+1)) (i : fin n) : fin (n+1) :=
if i.1 < p.1 then i.cast_succ else i.succ

/-- `pred_above p i h` embeds `i` into `fin n` by ignoring `p`. -/
def pred_above (p : fin (n+1)) (i : fin (n+1)) (hi : i ≠ p) : fin n :=
if h : i < p
then i.cast_lt (lt_of_lt_of_le h $ nat.le_of_lt_succ p.2)
else i.pred $
  have p < i, from lt_of_le_of_ne (le_of_not_gt h) hi.symm,
  ne_of_gt (lt_of_le_of_lt (zero_le p) this)

/-- `sub_nat i h` subtracts `m` from `i`, generalizes `fin.pred`. -/
def sub_nat (m) (i : fin (n + m)) (h : i.val ≥ m) : fin n :=
⟨i.val - m, by simp [nat.sub_lt_right_iff_lt_add h, i.is_lt]⟩

/-- `add_nat i h` adds `m` on `i`, generalizes `fin.succ`. -/
def add_nat (m) (i : fin n) : fin (n + m) :=
⟨i.1 + m, add_lt_add_right i.2 _⟩

theorem le_last (i : fin (n+1)) : i ≤ last n :=
le_of_lt_succ i.is_lt

@[simp] lemma cast_succ_val (k : fin n) : k.cast_succ.val = k.val := rfl

@[simp] lemma cast_lt_val (k : fin m) (h : k.1 < n) : (k.cast_lt h).val = k.val := rfl

@[simp] lemma cast_succ_cast_lt (i : fin (n + 1)) (h : i.val < n): cast_succ (cast_lt i h) = i :=
fin.eq_of_veq rfl

@[simp] lemma sub_nat_val (i : fin (n + m)) (h : i.val ≥ m) : (i.sub_nat m h).val = i.val - m :=
rfl

@[simp] lemma add_nat_val (i : fin (n + m)) (h : i.val ≥ m) : (i.add_nat m).val = i.val + m :=
rfl

@[simp] lemma cast_succ_inj {a b : fin n} : a.cast_succ = b.cast_succ ↔ a = b :=
by simp [eq_iff_veq]

theorem succ_above_ne (p : fin (n+1)) (i : fin n) : p.succ_above i ≠ p :=
begin
  assume eq,
  unfold fin.succ_above at eq,
  split_ifs at eq with h;
    simpa [lt_irrefl, nat.lt_succ_self, eq.symm] using h
end

@[simp] lemma succ_above_descend : ∀(p i : fin (n+1)) (h : i ≠ p), p.succ_above (p.pred_above i h) = i
| ⟨p, hp⟩ ⟨0,   hi⟩ h := fin.eq_of_veq $ by simp [succ_above, pred_above]; split_ifs; simp * at *
| ⟨p, hp⟩ ⟨i+1, hi⟩ h := fin.eq_of_veq
  begin
    have : i + 1 ≠ p, by rwa [(≠), fin.ext_iff] at h,
    unfold succ_above pred_above,
    split_ifs with h1 h2; simp at *,
    exact (this (le_antisymm h2 (le_of_not_gt h1))).elim
  end

@[simp] lemma pred_above_succ_above (p : fin (n+1)) (i : fin n) (h : p.succ_above i ≠ p) :
  p.pred_above (p.succ_above i) h = i :=
begin
  unfold fin.succ_above,
  apply eq_of_veq,
  split_ifs with h₀,
  { simp [pred_above, h₀, lt_iff_val_lt_val], },
  { unfold pred_above,
    split_ifs with h₁,
    { exfalso,
      rw [lt_iff_val_lt_val, succ_val] at h₁,
      exact h₀ (lt_trans (nat.lt_succ_self _) h₁) },
    { rw [pred_succ] } }
end

section rec

@[elab_as_eliminator] def succ_rec
  {C : ∀ n, fin n → Sort*}
  (H0 : ∀ n, C (succ n) 0)
  (Hs : ∀ n i, C n i → C (succ n) i.succ) : ∀ {n : ℕ} (i : fin n), C n i
| 0        i           := i.elim0
| (succ n) ⟨0, _⟩      := H0 _
| (succ n) ⟨succ i, h⟩ := Hs _ _ (succ_rec ⟨i, lt_of_succ_lt_succ h⟩)

@[elab_as_eliminator] def succ_rec_on {n : ℕ} (i : fin n)
  {C : ∀ n, fin n → Sort*}
  (H0 : ∀ n, C (succ n) 0)
  (Hs : ∀ n i, C n i → C (succ n) i.succ) : C n i :=
i.succ_rec H0 Hs

@[simp] theorem succ_rec_on_zero {C : ∀ n, fin n → Sort*} {H0 Hs} (n) :
  @fin.succ_rec_on (succ n) 0 C H0 Hs = H0 n :=
rfl

@[simp] theorem succ_rec_on_succ {C : ∀ n, fin n → Sort*} {H0 Hs} {n} (i : fin n) :
  @fin.succ_rec_on (succ n) i.succ C H0 Hs = Hs n i (fin.succ_rec_on i H0 Hs) :=
by cases i; refl

@[elab_as_eliminator] def cases
  {C : fin (succ n) → Sort*} (H0 : C 0) (Hs : ∀ i : fin n, C (i.succ)) :
  ∀ (i : fin (succ n)), C i
| ⟨0, h⟩ := H0
| ⟨succ i, h⟩ := Hs ⟨i, lt_of_succ_lt_succ h⟩

@[simp] theorem cases_zero {n} {C : fin (succ n) → Sort*} {H0 Hs} : @fin.cases n C H0 Hs 0 = H0 :=
rfl

@[simp] theorem cases_succ {n} {C : fin (succ n) → Sort*} {H0 Hs} (i : fin n) :
  @fin.cases n C H0 Hs i.succ = Hs i :=
by cases i; refl

end rec

end fin
