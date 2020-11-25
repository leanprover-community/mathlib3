import data.fin tactic linear_algebra.multilinear

variables {α : Type*}
namespace fin


@[simp] lemma coe_nat_fin_succ {m : ℕ} :
  ((m : fin m.succ) : ℕ) = m :=
begin
  rw coe_of_nat_eq_mod,
  rw nat.mod_eq_of_lt (nat.lt_succ_self _),
end

--lemma snoc_mk_apply becomes cons_zero
--lemma snoc_mk_apply' becomes cons_succ
--lemma snoc_succ becomes cons_self_tail
--lemma snoc_eq_ite becomes silly

variables {R : Type*} [comm_semiring R] {M : Type*} [add_comm_monoid M] [semimodule R M]

--@[simp] lemma snoc_update_last_ne update_cons_zero is better
--etc
-- init_update_last'becomes tail_update_zero

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

-- init_update not got exact equivalent

def append2 {n : ℕ} (g : fin n → α) : Π {m : ℕ} (f : fin m → α), fin (m + n) → α
| 0 f := g ∘ fin.cast (nat.zero_add _)
| (m + 1) f := (@fin.cons (m + n) (λ _, α) (f 0)
  (append2 (fin.tail f))) ∘ (fin.cast (nat.succ_add m n))

variables {m n : ℕ} (f : fin m → α) (g : fin n → α)

lemma cast_eq_iff_eq_cast {m n : ℕ} (h : m = n) (x : fin m) (y : fin n) :
  cast h x = y ↔ x = cast h.symm y :=
by simp only [fin.ext_iff, coe_cast]

lemma append2_apply_fst (k : fin (m + n)) (h : (k : ℕ) < m) :
  append2 g f k = f (fin.cast_lt k h) :=
begin
  induction m with m hm,
    exfalso, linarith,
  unfold append2,
  rw function.comp_app,
  cases classical.em (k.cast (nat.succ_add m n) = 0) with hk hk,
    rw [hk, cons_zero],
    exact (congr_arg _ $ fin.ext $ ((fin.ext_iff _ _).1 hk).symm),
  rw [←fin.succ_pred (k.cast (nat.succ_add m n)) hk, cons_succ, hm (fin.tail f)
      ((k.cast (nat.succ_add m n)).pred hk) (nat.pred_lt_pred (λ hnot, hk $ fin.ext hnot) h)],
  unfold tail, congr, ext,
  have hk1 : 1 ≤ (k : ℕ) := nat.succ_le_of_lt (nat.pos_of_ne_zero $ λ hnot, hk $ fin.ext hnot),
  simp only [nat.sub_add_cancel hk1, coe_pred, coe_cast, coe_cast_lt, coe_succ],
end

lemma append2_apply_snd (k : fin (m + n)) (h : m ≤ (k : ℕ)) :
  append2 g f k = g (fin.sub_nat m (k.cast $ add_comm _ _) h) :=
begin
  induction m with m hm,
    refl,
  unfold append2,
  have hk0 : k.cast (nat.succ_add m n) ≠ 0 := λ hnot, h.not_lt $ ((fin.ext_iff _ _).1 hnot).symm ▸ nat.zero_lt_succ m,
  rw [function.comp_app, ←fin.succ_pred (k.cast (nat.succ_add m n)) hk0, cons_succ,
      hm (tail f) ((k.cast (nat.succ_add m n)).pred hk0) (nat.pred_le_pred h)],
  congr' 1,
  ext,
  simp only [coe_sub_nat, coe_pred, coe_cast, nat.sub_sub, add_comm],
end

lemma append2_apply_snd' (k : fin n) :
  append2 g f (fin.nat_add m k) = g k :=
begin
  convert append2_apply_snd f g (fin.nat_add m k) _,
  ext,
  simp only [nat_add, coe_cast, coe_mk, nat.add_sub_cancel_left, coe_sub_nat],
  simp only [nat_add, coe_mk, zero_le, le_add_iff_nonneg_right],
  exact nat.zero_le _,
end

lemma append2_default_apply (x) : append2 f (default (fin 0 → α)) (cast (zero_add m).symm x) = f x :=
begin
  unfold append2,
  rw function.comp_app,
  congr, ext, refl,
end

lemma default_append2 : append2 (default (fin 0 → α)) f = f :=
begin
  ext,
  induction m with m hm,
    exact fin.elim0 x,
  rcases classical.em (x = 0) with ⟨rfl, hx⟩,
  exact cons_zero _ _,
  rw append2_apply_fst f (default (fin 0 → α)) x x.2,
  congr, ext, refl,
end

lemma append2_one {x : α} :
  append2 f (λ i : fin 1, x) = @fin.cons m (λ _, α) x f ∘ cast (add_comm 1 m) :=
begin
  ext y,
  unfold append2,
  rcases classical.em (y = cast (add_comm m 1) 0) with ⟨rfl, hy⟩,
  simp only [function.comp_app, val_zero'],
  erw cons_zero,
  simp,
  congr',
  { simp },
  ext, simp, simp, simp,ext, simp, simp, swap, simp,
  intros,
  ext,
  apply (fin.heq_ext_iff (zero_add m)).1 a_1,
end

lemma append2_update (i : fin n) (x : α) :
  append2 (function.update g i x) f = function.update (append2 g f) (nat_add m i) x :=
begin
  induction m with m hm,
    unfold append2,
    dunfold nat_add,
    ext y,
    rw function.comp_app,
    rcases classical.em ((cast (zero_add n) y) = i) with ⟨rfl, hi⟩,
    erw function.update_same,
    convert (function.update_same _ _ _).symm,
    refl,
    refl,
    ext, simp only [val_eq_coe, coe_mk, zero_add],
    sorry, sorry,
end


lemma update_append2 (i : fin m) (x : α) :
  append2 g (function.update f i x) = function.update (append2 g f) (cast_add n i) x :=
begin
   sorry,
end

lemma append2_assoc {k : ℕ} (h : fin k → α) (x) :
  append2 (append2 f g) h x = append2 f (append2 g h) (cast (add_assoc _ _ _).symm x) :=
begin
  sorry
end

lemma append2_assoc' {k : ℕ} (h : fin k → α) (x) :
  append2 f (append2 g h) x = append2 (append2 f g) h (cast (add_assoc _ _ _) x) :=
begin
  convert (append2_assoc f g h (cast (add_assoc _ _ _) x)).symm,
  ext,
  refl,
end

end fin
