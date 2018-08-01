import data.nat.basic

open fin nat

namespace fin

variable {n : ℕ}

/-- Embedding of `fin n` in `fin (n+1)` -/
def raise (k : fin n) : fin (n + 1) := ⟨val k, lt_succ_of_lt (is_lt k)⟩

def add_nat {n} (i : fin n) (k) : fin (n + k) :=
⟨i.1 + k, nat.add_lt_add_right i.2 _⟩

@[simp] lemma succ_val (j : fin n) : j.succ.val = j.val.succ :=
by cases j; simp [fin.succ]

@[simp] lemma pred_val (j : fin (n+1)) (h : j ≠ 0) : (j.pred h).val = j.val.pred :=
by cases j; simp [fin.pred]

@[simp] protected lemma eta (a : fin n) (h : a.1 < n) : (⟨a.1, h⟩ : fin n) = a :=
by cases a; refl

instance {n : ℕ} : linear_order (fin n) :=
{ le_refl := λ a, @le_refl ℕ _ _,
  le_trans := λ a b c, @le_trans ℕ _ _ _ _,
  le_antisymm := λ a b ha hb, fin.eq_of_veq $ le_antisymm ha hb,
  le_total := λ a b, @le_total ℕ _ _ _,
  lt_iff_le_not_le := λ a b, @lt_iff_le_not_le ℕ _ _ _,
  ..fin.has_le,
  ..fin.has_lt }

end fin

theorem eq_of_lt_succ_of_not_lt {a b : ℕ} (h1 : a < b + 1) (h2 : ¬ a < b) : a = b :=
have h3 : a ≤ b, from le_of_lt_succ h1,
or.elim (eq_or_lt_of_not_lt h2) (λ h, h) (λ h, absurd h (not_lt_of_ge h3))

instance fin_to_nat (n : ℕ) : has_coe (fin n) nat := ⟨fin.val⟩
instance fin_to_int (n : ℕ) : has_coe (fin n) int := ⟨λ k, ↑(fin.val k)⟩

variables {n : ℕ} {a b : fin n}

protected theorem fin.succ.inj (p : fin.succ a = fin.succ b) : a = b :=
by cases a; cases b; exact eq_of_veq (nat.succ.inj (veq_of_eq p))

@[elab_as_eliminator] def fin.succ_rec
  {C : ∀ n, fin n → Sort*}
  (H0 : ∀ n, C (succ n) 0)
  (Hs : ∀ n i, C n i → C (succ n) i.succ) : ∀ {n : ℕ} (i : fin n), C n i
| 0        i           := i.elim0
| (succ n) ⟨0, _⟩      := H0 _
| (succ n) ⟨succ i, h⟩ := Hs _ _ (fin.succ_rec ⟨i, lt_of_succ_lt_succ h⟩)

@[elab_as_eliminator] def fin.succ_rec_on {n : ℕ} (i : fin n)
  {C : ∀ n, fin n → Sort*}
  (H0 : ∀ n, C (succ n) 0)
  (Hs : ∀ n i, C n i → C (succ n) i.succ) : C n i :=
i.succ_rec H0 Hs

@[simp] theorem fin.succ_rec_on_zero
  {C : ∀ n, fin n → Sort*} {H0 Hs} (n) :
  @fin.succ_rec_on (succ n) 0 C H0 Hs = H0 n := rfl

@[simp] theorem fin.succ_rec_on_succ
  {C : ∀ n, fin n → Sort*} {H0 Hs} {n} (i : fin n) :
  @fin.succ_rec_on (succ n) i.succ C H0 Hs = Hs n i (fin.succ_rec_on i H0 Hs) :=
by cases i; refl

@[elab_as_eliminator] def fin.cases {n} {C : fin (succ n) → Sort*}
  (H0 : C 0) (Hs : ∀ i : fin n, C (i.succ)) :
  ∀ (i : fin (succ n)), C i
| ⟨0, h⟩ := H0
| ⟨succ i, h⟩ := Hs ⟨i, lt_of_succ_lt_succ h⟩

@[simp] theorem fin.cases_zero
  {n} {C : fin (succ n) → Sort*} {H0 Hs} :
  @fin.cases n C H0 Hs 0 = H0 := rfl

@[simp] theorem fin.cases_succ
  {n} {C : fin (succ n) → Sort*} {H0 Hs} (i : fin n) :
  @fin.cases n C H0 Hs i.succ = Hs i :=
by cases i; refl
