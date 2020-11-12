import data.fin tactic linear_algebra.multilinear

variables {α : Type*}
namespace fin

@[simp] lemma coe_nat_fin_succ {m : ℕ} :
  ((m : fin m.succ) : ℕ) = m :=
begin
  rw coe_of_nat_eq_mod,
  rw nat.mod_eq_of_lt (nat.lt_succ_self _),
end

lemma snoc_mk_apply {α : Type*} {n : ℕ} (i : fin n → α) (x : α) :
  (fin.snoc i x : fin n.succ → α) n = x :=
begin
  unfold fin.snoc, split_ifs,
  exfalso, refine @irrefl _ (<) _ n _,
  convert h, rw ←fin.coe_eq_val, rw fin.coe_nat_fin_succ,
  refl,
end

lemma snoc_mk_apply' {α : Type*} {n : ℕ} (i : fin n → α) (x : α) (y : fin n) :
  (fin.snoc i x : fin n.succ → α) y = i y :=
begin
  unfold fin.snoc,
  split_ifs,
  simp only [fin.coe_eq_cast_succ, fin.cast_lt_cast_succ, cast_eq],
  exfalso,
  apply h, rw fin.coe_eq_cast_succ, exact y.2,
end


lemma snoc_succ {α : Type*} {n : ℕ} (i : fin n.succ → α) :
  (fin.snoc (fin.init i) (i n) : fin n.succ → α) = i :=
begin
  ext y,
  unfold fin.snoc,
  split_ifs,
  unfold init,
  rw cast_succ_cast_lt,
  rw cast_eq,
  convert rfl,
    ext, rw coe_nat_fin_succ,
    refine nat.eq_of_lt_succ_of_not_lt y.2 h,
end

lemma snoc_eq_ite {α : Type*} {n : ℕ} (i : fin n → α) (x : α) (m : fin n.succ) :
  (fin.snoc i x : fin n.succ → α) m = if h : (m : ℕ) < n then i ⟨m, h⟩ else x :=
begin
  cases classical.em ((m : ℕ) < n),
  rw dif_pos h,
  rw ←snoc_mk_apply' i x ⟨m, h⟩,
  congr,
  rw fin.coe_eq_cast_succ,
  erw fin.cast_succ_cast_lt,
  rw dif_neg h,
  conv_rhs {rw ←snoc_mk_apply i x},
  congr,
  ext,
  rw coe_nat_fin_succ,
  exact nat.eq_of_lt_succ_of_not_lt m.2 h,
end

variables {R : Type*} [comm_semiring R] {M : Type*} [add_comm_monoid M] [semimodule R M]

@[simp] lemma snoc_update_last_ne {m : ℕ} (f : fin m → M) (x y : M) (i : fin m) :
  function.update (fin.snoc f x : fin m.succ → M) m y i =
  (fin.snoc f x : fin m.succ → M) i :=
begin
  convert function.update_noteq _ _ _,
  refl,
  intro h,
  refine nat.lt_irrefl m _,
  convert i.2,
  rw fin.ext_iff at h,
  rw coe_nat_fin_succ at h,
  rw coe_eq_cast_succ at h,
  convert h.symm,
end

@[simp] lemma snoc_update_init_ne {m : ℕ} (f : fin m → M) (x y : M)
  (i : fin m) :
  function.update (fin.snoc f x : fin m.succ → M) i y m = x :=
begin
  conv_rhs {rw ←snoc_mk_apply f x},
  convert function.update_noteq _ _ _,
  refl,
  intro h,
  refine nat.lt_irrefl m _,
  convert i.2,
  rw fin.ext_iff at h,
  rw coe_nat_fin_succ at h,
  rw coe_eq_cast_succ at h,
  convert h,
end

@[simp] lemma init_update_last' {m : ℕ} (f : fin m.succ → M) (x : M) :
  fin.init (function.update f m x) = fin.init f :=
begin
  ext j,
  unfold init,
  rw function.update_noteq,
  intro h,
  refine nat.lt_irrefl m _,
  convert j.2,
  rw fin.ext_iff at h,
  rw coe_nat_fin_succ at h,
  convert h.symm,
end


lemma succ_lt_of_ne {m : ℕ} (i : fin m.succ) (h : (i : ℕ) ≠ m) :
  (i : ℕ) < m :=
nat.lt_of_le_and_ne (nat.le_of_lt_succ i.2) h

lemma cast_succ_eq_iff_eq_mk {m : ℕ} {i : fin m.succ} {j : fin m}
  (h : (i : ℕ) ≠ m) : (j : fin m.succ) = i ↔ j = ⟨i, succ_lt_of_ne i h⟩ :=
begin
  rw ext_iff, rw ext_iff,
  rw coe_eq_cast_succ, rw coe_cast_succ,
  refl,
end

@[simp] lemma init_update {m : ℕ} (f : fin m.succ → M) (x : M)
  (i : fin m.succ) (h : (i : ℕ) ≠ m) :
  function.update (fin.init f) ⟨i, succ_lt_of_ne i h⟩ x = fin.init (function.update f i x) :=
begin
  ext j,
  cases classical.em (i = j) with hj hj,
  convert function.update_same _ _ _,
  ext,
  rw coe_mk, rw hj,
  rw fin.coe_eq_cast_succ,
  rw fin.coe_cast_succ,
  rw hj,
  unfold fin.init,
  rw fin.coe_eq_cast_succ,
  rw function.update_same,
  unfold fin.init,
  rw function.update_noteq,
  rw function.update_noteq, refl,
  rw ← coe_eq_cast_succ,
  exact (ne.symm hj),
  exact (λ hnot, hj $ ((cast_succ_eq_iff_eq_mk h).2 hnot).symm),
end


def append {m : ℕ} (f : fin m → α) : Π {n : ℕ} (g : fin n → α), fin (m + n) → α
| 0 g := f
| (n + 1) g := fin.snoc (append (fin.init g)) (g n)

variables {m n : ℕ} (f : fin m → α) (g : fin n → α)

lemma append_apply_fst (k : fin (m + n)) (h : (k : ℕ) < m) :
  append f g k = f ⟨k, h⟩ :=
begin
  induction n with n hn,
  unfold append,
  rw fin.eta,
  unfold append,
  have := snoc_mk_apply' (append f (λ (x : fin n), g ↑x)) (g ↑n) ⟨k, by linarith⟩,
  rw hn (λ i, g i) ⟨k, by linarith⟩ h at this,
  simp only [coe_mk] at this,
  rw ←this,
  congr, ext, rw coe_eq_cast_succ, refl,
  ext,
  simp only [coe_cast_succ, coe_mk, coe_eq_cast_succ],
end

lemma append_apply_fst' (k : fin m) :
  append f g ⟨k, by cases k; linarith⟩ = f k :=
begin
  rw append_apply_fst,
  simp only [coe_mk, fin.eta],
  cases k,
  linarith,
end

lemma append_apply_snd (k : fin (m + n)) (h : m ≤ (k : ℕ)) :
  append f g k = g ⟨k - m, (nat.sub_lt_left_iff_lt_add h).2 k.2⟩ :=
begin
  induction n with n hn,
  exfalso, cases k, linarith,
  unfold append,
  cases classical.em ((k : ℕ) < m + n) with hk hk,
  have := snoc_mk_apply' (append f (λ x : fin n, g x)) (g n) ⟨k, hk⟩,
  rw hn (λ i, g i) ⟨k, hk⟩ h at this,
  convert this,
  ext,
  rw coe_eq_cast_succ,
  refl,
  ext, simp only [coe_cast_succ, coe_mk, coe_eq_cast_succ],
    ext, simp only [coe_cast_succ, coe_mk, coe_eq_cast_succ],
  have hnk : (k : ℕ) = m + n, from
    le_antisymm (nat.le_of_lt_succ k.2) (not_lt.1 hk),
  convert snoc_mk_apply _ _,
  ext, rw hnk,
  rw fin.coe_of_nat_eq_mod,
  rw nat.mod_eq_of_lt (nat.lt_succ_self _), refl,
  ext,
  rw coe_of_nat_eq_mod,
  rw nat.mod_eq_of_lt (nat.lt_succ_self _),
  rw coe_mk, rw hnk,
  rw nat.add_sub_cancel_left,
end

lemma append_apply_snd' (k : fin n) :
  append f g ⟨k + m, by cases k; linarith⟩ = g k :=
begin
  rw append_apply_snd, congr,
  simp only [coe_mk, nat.add_sub_cancel, fin.eta],
  simp only [add_zero, coe_mk, int.coe_nat_add, ge_iff_le, zero_le, zero_add, le_add_iff_nonneg_left, neg_zero],
  exact nat.zero_le _,
end

lemma append_default : append f (default (fin 0 → α)) = f :=
rfl

lemma append_default_apply (i : fin m) :
  append f (default (fin 0 → α)) i = f i :=
rfl

lemma default_append (i : fin m) :
  append (default (fin 0 → α)) f ⟨i, by cases i; linarith⟩ = f i :=
begin
  sorry,
end


lemma append_one {x : α} :
  append f (λ i : fin 1, x) = fin.snoc f x := rfl

lemma append_add {m n : ℕ} (f : fin m → M) (g : fin n → M) (i : fin n) (x y : M) :
  append f (function.update g i (x + y)) ⟨i + m, have (i : ℕ) < n := i.2, by linarith⟩ = append f (function.update g i x) ⟨i + m, have (i : ℕ) < n := i.2, by linarith⟩ +
    append f (function.update g i y) ⟨i + m, have (i : ℕ) < n := i.2, by linarith⟩ :=
begin
  induction n with k hk,
  { exact i.elim0 },
  { cases classical.em (i = k),
    rw h,
    simp only [append_apply_snd', function.update_same],
    simp only [append_apply_snd', function.update_same],
    }
end

lemma append_update {m n : ℕ} (f : fin m → M) (g : fin n → M) (i : fin n) (x : M) :
  append f (function.update g i x) = function.update (append f g) ⟨m + i, have (i : ℕ) < n := i.2, by linarith⟩ x :=
begin
  have aux : ∀ {m n : ℕ}, (((m + n) : fin (m + n).succ) : ℕ) = m + n :=
  by {intros, rw coe_add, simp only [coe_of_nat_eq_mod, nat.add_mod_mod, nat.mod_add_mod],
     exact nat.mod_eq_of_lt (nat.lt_succ_self _)},
  induction n with n hn,
  exact fin.elim0 i,
  unfold append,
  cases classical.em (i = n),
  rw h,
  have : (⟨m + (n : fin n.succ), by {rw coe_nat_fin_succ, exact nat.lt_succ_self _}⟩ : fin (m + n).succ) =
    (m + n : fin (m + n).succ),
  by {ext, simp only [coe_mk, coe_nat_fin_succ], exact aux.symm},
  rw this,
  rw function.update_same,
  rw init_update_last',
  ext (y : fin (m + n).succ),
  cases classical.em (y = m + n) with hy hy,
  rw hy,
  rw function.update_same,
  convert snoc_mk_apply _ _,
  ext,
  rw coe_nat_fin_succ, exact aux,
  have Hy : y = (⟨(y : ℕ), succ_lt_of_ne y $ λ hnot, hy $ ext $ by {rw hnot, exact aux.symm}⟩ : fin (m + n)) :=
  by {ext, simp only [coe_cast_succ, coe_mk, coe_eq_cast_succ], },
  rw Hy,
  rw snoc_mk_apply',
  convert (snoc_update_last_ne (append f (init g)) _ _ _).symm,
  rw snoc_mk_apply',
  {ext, simp only [coe_mk, coe_nat_fin_succ], rw coe_add, simp only [nat.add_mod_mod, coe_of_nat_eq_mod, nat.mod_add_mod],
   rw nat.mod_eq_of_lt (nat.lt_succ_self _)},
  have Hn := hn (init g) ⟨i, succ_lt_of_ne i $ λ hnot, h $ ext $ by {rw hnot, rw coe_nat_fin_succ}⟩,
  rw init_update at Hn, rw Hn,
  rw snoc_update,
  congr,
  rw function.update_noteq (ne.symm h),
end



end fin