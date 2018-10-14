import data.nat.basic

open fin nat

namespace fin

variable {n : ℕ}

/-- The greatest value of `fin (n+1)` -/
def last (n : ℕ) : fin (n+1) := ⟨_, n.lt_succ_self⟩

theorem le_last (i : fin (n+1)) : i ≤ last n :=
le_of_lt_succ i.is_lt

def add_nat {n} (i : fin n) (k) : fin (n + k) :=
⟨i.1 + k, nat.add_lt_add_right i.2 _⟩

def nat_add {n} (k) (i : fin n) : fin (k + n) :=
⟨k + i.1, nat.add_lt_add_left i.2 _⟩

@[simp] lemma succ_val (j : fin n) : j.succ.val = j.val.succ :=
by cases j; simp [fin.succ]

@[simp] lemma pred_val (j : fin (n+1)) (h : j ≠ 0) : (j.pred h).val = j.val.pred :=
by cases j; simp [fin.pred]

@[simp] protected lemma eta (a : fin n) (h : a.1 < n) : (⟨a.1, h⟩ : fin n) = a :=
by cases a; refl

instance {n : ℕ} : decidable_linear_order (fin n) :=
{ le_refl := λ a, @le_refl ℕ _ _,
  le_trans := λ a b c, @le_trans ℕ _ _ _ _,
  le_antisymm := λ a b ha hb, fin.eq_of_veq $ le_antisymm ha hb,
  le_total := λ a b, @le_total ℕ _ _ _,
  lt_iff_le_not_le := λ a b, @lt_iff_le_not_le ℕ _ _ _,
  decidable_le := fin.decidable_le,
  ..fin.has_le,
  ..fin.has_lt }

instance fin_to_nat (n : ℕ) : has_coe (fin n) nat := ⟨fin.val⟩
instance fin_to_int (n : ℕ) : has_coe (fin n) int := ⟨λ k, ↑(fin.val k)⟩

variables {a b : fin n}

protected theorem succ.inj (p : fin.succ a = fin.succ b) : a = b :=
by cases a; cases b; exact eq_of_veq (nat.succ.inj (veq_of_eq p))

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

@[simp] theorem succ_rec_on_zero
  {C : ∀ n, fin n → Sort*} {H0 Hs} (n) :
  @fin.succ_rec_on (succ n) 0 C H0 Hs = H0 n := rfl

@[simp] theorem succ_rec_on_succ
  {C : ∀ n, fin n → Sort*} {H0 Hs} {n} (i : fin n) :
  @succ_rec_on (succ n) i.succ C H0 Hs = Hs n i (succ_rec_on i H0 Hs) :=
by cases i; refl

@[elab_as_eliminator] def cases {n} {C : fin (succ n) → Sort*}
  (H0 : C 0) (Hs : ∀ i : fin n, C (i.succ)) :
  ∀ (i : fin (succ n)), C i
| ⟨0, h⟩ := H0
| ⟨succ i, h⟩ := Hs ⟨i, lt_of_succ_lt_succ h⟩

@[simp] theorem cases_zero
  {n} {C : fin (succ n) → Sort*} {H0 Hs} :
  @fin.cases n C H0 Hs 0 = H0 := rfl

@[simp] theorem cases_succ
  {n} {C : fin (succ n) → Sort*} {H0 Hs} (i : fin n) :
  @fin.cases n C H0 Hs i.succ = Hs i :=
by cases i; refl

def lower_left {n m} (i : fin (n + m)) (h : i.val < n) : fin n :=
⟨i.val, h⟩

def lower_right {n m} (i : fin (n + m)) (h: i.val >= n) : fin m :=
⟨i.val - n, by simp [nat.sub_lt_right_iff_lt_add h, i.is_lt]⟩

def raise_le {m n} (h : m ≤ n) (i : fin m) : fin n :=
⟨i.val, lt_of_lt_of_le (i.is_lt) h⟩

def cast {m n} (h : m = n) (i : fin m) : fin n :=
raise_le (by simp [h]) i

/-- Embedding of `fin n` in `fin (n+1)` -/
def raise_one (i : fin n) : fin (n + 1) :=
raise_le (by simp [le_succ]) i

/-- Embedding of `fin n` in `fin (n+k)` -/
def raise_nat {n} (i : fin n) (k) : fin (n + k) :=
raise_le (by rw nat.add_comm; apply nat.le_add_left) i

def swap_add {m n} (i : fin (m + n)) : fin (n + m) :=
raise_le (by rw nat.add_comm) i

end fin
