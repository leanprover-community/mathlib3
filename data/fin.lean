import data.nat.basic

open fin nat

/-- Embedding of `fin n` in `fin (n+1)` -/
def raise_fin {n : ℕ} (k : fin n) : fin (n + 1) := ⟨val k, lt_succ_of_lt (is_lt k)⟩

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
