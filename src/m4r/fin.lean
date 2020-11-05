import data.fin tactic

variables {α : Type*}
namespace fin


lemma snoc_mk_apply {α : Type*} {n : ℕ} (i : fin n → α) (x : α) :
  (fin.snoc i x : fin n.succ → α) n = x :=
begin
  unfold fin.snoc, split_ifs,
  exfalso, refine @irrefl _ (<) _ n _,
  convert h, rw ←fin.coe_eq_val, rw fin.coe_of_nat_eq_mod, rw nat.mod_eq_of_lt (nat.lt_succ_self _),
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
  (fin.snoc (λ y : fin n, i y) (i n) : fin n.succ → α) = i :=
begin
  ext y,
  unfold fin.snoc,
  split_ifs,
  rw fin.coe_eq_cast_succ,
  rw fin.cast_succ_cast_lt,
  rw cast_eq,
  simp only [fin.coe_eq_cast_succ, fin.cast_succ_cast_lt, cast_eq],
  convert rfl,
    ext, rw fin.coe_of_nat_eq_mod,
    rw nat.mod_eq_of_lt (nat.lt_succ_self _),
    refine nat.eq_of_lt_succ_of_not_lt y.2 h,
end
def append {m : ℕ} (f : fin m → α) : Π {n : ℕ} (g : fin n → α), fin (m + n) → α
| 0 g := f
| (n + 1) g := fin.snoc (append (λ x : fin n, g x)) (g n)

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
  congr, ext, simp only [coe_cast_succ, coe_mk, coe_eq_cast_succ],
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

lemma default_append (i : fin m) :
  append f (default (fin 0 → α)) i = f i :=
rfl

end fin