import data.nat.basic data.equiv.basic

open fin nat

namespace fin

variable {n : ℕ}

/-- The greatest value of `fin (n+1)` -/
def last (n : ℕ) : fin (n+1) := ⟨_, n.lt_succ_self⟩

theorem le_last (i : fin (n+1)) : i ≤ last n :=
le_of_lt_succ i.is_lt

def add_nat {n} (i : fin n) (k) : fin (n + k) :=
⟨i.1 + k, nat.add_lt_add_right i.2 _⟩

@[simp] lemma succ_val (j : fin n) : j.succ.val = j.val.succ :=
by cases j; simp [fin.succ]

@[simp] lemma pred_val (j : fin (n+1)) (h : j ≠ 0) : (j.pred h).val = j.val.pred :=
by cases j; simp [fin.pred]

@[simp] lemma fin.succ_pred (i : fin (n+1)) (H : i ≠ 0) :
  (i.pred H).succ = i :=
begin
  apply fin.eq_of_veq,
  cases i with i hi,
  cases i,
  { exfalso, apply H, apply fin.eq_of_veq, refl },
  refl
end

@[simp] lemma fin.pred_succ (i : fin n) (H : i.succ ≠ 0) :
  i.succ.pred H = i :=
by cases i; refl

/-- Embedding of `fin n` in `fin (n+1)` -/
def raise (k : fin n) : fin (n + 1) := ⟨val k, lt_succ_of_lt (is_lt k)⟩

@[simp] lemma fin.raise_val (k : fin n) : k.raise.val = k.val := rfl

def lower : Π i : fin (n+1), i.1 < n → fin n := λ i h, ⟨i.1, h⟩

@[simp] lemma lower_val (k : fin (n+1)) (H : k.1 < n) : (k.lower H).val = k.val := rfl

def ascend (pivot : fin (n+1)) (i : fin n) : fin (n+1) :=
if i.1 < pivot.1 then i.raise else i.succ

def descend (pivot : fin (n+1)) (i : fin (n+1)) (H : i ≠ pivot) : fin n :=
if h : i.1 < pivot.1
  then i.lower (lt_of_lt_of_le h $ nat.le_of_lt_succ pivot.2)
  else i.pred (λ H1, H $ by subst H1;
    replace h := nat.eq_zero_of_le_zero (le_of_not_gt h);
    from fin.eq_of_veq h.symm)

theorem ascend_ne (pivot : fin (n+1)) (i : fin n) :
  pivot.ascend i ≠ pivot :=
λ H, begin
  unfold fin.ascend at H,
  split_ifs at H;
  rw ← H at h;
  simp [lt_irrefl, nat.lt_succ_self] at h;
  exact h
end

@[simp] lemma ascend_descend (pivot i : fin (n+1))
  (H : i ≠ pivot) : pivot.ascend (pivot.descend i H) = i :=
begin
  unfold fin.descend fin.ascend,
  split_ifs with H1 H2 H3; apply fin.eq_of_veq; simp at *,
  { cases pivot with p hp,
    cases i with i hi,
    cases i with i, { simp at * },
    exfalso, apply H, apply fin.eq_of_veq,
    apply le_antisymm, { apply nat.succ_le_of_lt H2 },
    simpa using H1 }
end

@[simp] lemma descend_ascend (pivot : fin (n+1))
  (i : fin n) (H : pivot.ascend i ≠ pivot) :
  pivot.descend (pivot.ascend i) H = i :=
begin
  unfold fin.descend fin.ascend,
  apply fin.eq_of_veq,
  split_ifs,
  { simp [h] },
  { split_ifs,
    cases nat.decidable_lt ((ite (i.val < pivot.val) (fin.raise i) (fin.succ i)).val) (pivot.val) with h1 h1,
    { cases nat.decidable_lt (i.val) (pivot.val),
      { split_ifs, simp },
      { cc } },
    { cases nat.decidable_lt (i.val) (pivot.val) with h2 h2,
      { simp [h2] at h1,
        simp at *,
        exfalso, apply lt_asymm (nat.lt_succ_self i.1),
        apply lt_of_lt_of_le h1 h2 },
      { split_ifs, exfalso, exact h h2 } } }
end

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

end fin

theorem eq_of_lt_succ_of_not_lt {a b : ℕ} (h1 : a < b + 1) (h2 : ¬ a < b) : a = b :=
have h3 : a ≤ b, from le_of_lt_succ h1,
or.elim (eq_or_lt_of_not_lt h2) (λ h, h) (λ h, absurd h (not_lt_of_ge h3))

instance fin_to_nat (n : ℕ) : has_coe (fin n) nat := ⟨fin.val⟩
instance fin_to_int (n : ℕ) : has_coe (fin n) int := ⟨λ k, ↑(fin.val k)⟩

namespace fin

variables {n : ℕ} {a b : fin n}

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
  @fin.succ_rec_on (succ n) i.succ C H0 Hs = Hs n i (fin.succ_rec_on i H0 Hs) :=
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

def fin_zero_elim {C : Sort*} : fin 0 → C :=
λ x, false.elim $ nat.not_lt_zero x.1 x.2

end fin

section sum_and_prod

variables {m n : ℕ}

def fin_sum : (fin m ⊕ fin n) ≃ fin (m + n) :=
{ to_fun := λ x, sum.rec_on x
    (λ y, ⟨y.1, nat.lt_of_lt_of_le y.2 $ nat.le_add_right m n⟩)
    (λ y, ⟨m + y.1, nat.add_lt_add_left y.2 m⟩),
  inv_fun := λ x, if H : x.1 < m
    then sum.inl ⟨x.1, H⟩
    else sum.inr ⟨x.1 - m, nat.lt_of_add_lt_add_left $
      show m + (x.1 - m) < m + n,
      from (nat.add_sub_of_le $ le_of_not_gt H).symm ▸ x.2⟩,
  left_inv := λ x, sum.cases_on x
    (λ y, by simp [y.2]; from fin.eq_of_veq rfl)
    (λ y, have H : ¬m + y.val < m, by simpa using nat.add_le_add_left (nat.zero_le y.val) m,
       by simp [H, nat.add_sub_cancel_left];
       from fin.eq_of_veq rfl),
  right_inv := λ x, begin
    by_cases H : x.1 < m,
    { dsimp; rw [dif_pos H]; simp },
    { dsimp; rw [dif_neg H]; simp,
      apply fin.eq_of_veq; simp,
      rw [nat.add_sub_of_le (le_of_not_gt H)] }
  end }

def fin_prod : (fin m × fin n) ≃ fin (m * n) :=
{ to_fun := λ x, ⟨x.2.1 + n * x.1.1, calc
          x.2.1 + n * x.1.1 + 1
        = x.1.1 * n + x.2.1 + 1 : by ac_refl
    ... ≤ x.1.1 * n + n : nat.add_le_add_left x.2.2 _
    ... = (x.1.1 + 1) * n : eq.symm $ nat.succ_mul _ _
    ... ≤ m * n : nat.mul_le_mul_right _ x.1.2⟩,
  inv_fun := λ x, have H : n > 0,
      from nat.pos_of_ne_zero $ λ H,
        nat.not_lt_zero x.1 $ by subst H; from x.2,
    (⟨x.1 / n, (nat.div_lt_iff_lt_mul _ _ H).2 x.2⟩,
     ⟨x.1 % n, nat.mod_lt _ H⟩),
  left_inv := λ ⟨x, y⟩, have H : n > 0,
      from nat.pos_of_ne_zero $ λ H,
        nat.not_lt_zero y.1 $ H ▸ y.2,
    prod.ext
    (fin.eq_of_veq $ calc
            (y.1 + n * x.1) / n
          = y.1 / n + x.1 : nat.add_mul_div_left _ _ H
      ... = 0 + x.1 : by rw nat.div_eq_of_lt y.2
      ... = x.1 : nat.zero_add x.1)
    (fin.eq_of_veq $ calc
            (y.1 + n * x.1) % n
          = y.1 % n : nat.add_mul_mod_self_left _ _ _
      ... = y.1 : nat.mod_eq_of_lt y.2),
    right_inv := λ x, fin.eq_of_veq $ nat.mod_add_div _ _ }

end sum_and_prod

instance {n : ℕ} : preorder (fin n) :=
by apply_instance
