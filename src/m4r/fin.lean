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

lemma snoc_mk_apply'' {α : Type*} {n : ℕ} (i : fin n → α) (x : α)
  (y : fin n.succ) (h : (y : ℕ) < n) :
  (fin.snoc i x : fin n.succ → α) y = i ⟨y, h⟩ :=
begin
  rw ←snoc_mk_apply' i x ⟨y, h⟩,
  congr,
  ext,
  simp only [coe_cast_succ, coe_mk, coe_eq_cast_succ],
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

variables {m n o : ℕ} (f : fin m → α) (g : fin n → α)

lemma append_apply_fst (ho : o = m + n) (k : fin o) (h : (k : ℕ) < m) :
  append ho f g k = f (k.cast_lt h) :=
dif_pos h

lemma append_apply_fst' (ho : o = m + n) (k : fin m) :
  append ho f g (cast ho.symm (cast_add n k)) = f k :=
begin
  rw append_apply_fst _ _ ho (cast ho.symm (cast_add n k)) k.2,
  congr,
  ext,
  refl,
end

lemma append_apply_snd (ho : o = m + n) (k : fin o) (h : ¬(k : ℕ) < m) :
  append ho f g k = g ⟨(k : ℕ) - m, (nat.sub_lt_left_iff_lt_add $ le_of_not_lt h).2 (ho ▸ k.2)⟩ :=
dif_neg h
/-begin
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
end-/

lemma append_apply_snd' (ho : o = m + n) (k : fin n) :
  append ho f g (cast ho.symm (nat_add m k)) = g k :=
begin
  rw append_apply_snd,
  congr,
  ext,
  exact nat.add_sub_cancel_left _ _,
  rw not_lt,
  exact le_add_right (le_refl _),
end

lemma append_default (d : fin 0 → α) (ho : o = m) (x : fin o) :
  append (show o = m + 0, from ho) f d x = f (cast ho x) :=
begin
  rw append_apply_fst _ _ (show o = m + 0, from ho) x (ho ▸ x.2),
  congr,
end

lemma append_default' (d :  fin 0 → α) :
  append rfl f d = f :=
begin
  ext,
  rw append_default,
  congr,
  ext,
  refl,
end


lemma init_apply {n : ℕ} (f : fin n.succ → α) (i : fin n.succ)
  (h : (i : ℕ) < n) : init f ⟨i, h⟩ = f i :=
begin
  unfold init,
  congr,
  convert cast_succ_cast_lt i h,
end

lemma default_append (d : fin 0 → α) (ho : o = m) (i : fin o) :
  append (show o = 0 + m, by rwa zero_add) d f i = f (cast ho i) :=
begin
  rw append_apply_snd _ _ _ _ (nat.not_lt_zero _),
  congr,
end

lemma default_append' (d : fin 0 → α) (i : fin m) :
  append (zero_add _).symm d f i = f i :=
begin
  rw append_apply_snd _ _ _ _ (nat.not_lt_zero _),
  congr,
  ext,
  refl,
end

lemma append_one {x : α} :
  append rfl f (λ i : fin 1, x) = fin.snoc f x := rfl

lemma one_append {x : α} (i : fin (1 + m)) :
  append rfl (λ i : fin 1, x) f i = (fin.cons x f : fin m.succ → α) (cast (add_comm 1 m) i):=
begin
  cases classical.em (cast (add_comm _ _) i = 0) with hy hy,
    rw hy,
    rw cons_zero,
    rw append_apply_fst,
    rw ext_iff at hy,
    erw hy,
    rw coe_zero, linarith,
  rw ←fin.succ_pred (cast (add_comm _ _) i) hy,
  rw cons_succ,
  rw append_apply_snd,
    congr,
  contrapose! hy,
  ext,
  show (i : ℕ) = 0,
  linarith,
end

lemma append_update_add (ho : o = m + n) (f : fin m → M) (g : fin n → M) (i : fin n) (x y : M) :
  append ho f (function.update g i (x + y)) (cast ho.symm (nat_add m i)) =
    append ho f (function.update g i x) (cast ho.symm (nat_add m i)) +
      append ho f (function.update g i y) (cast ho.symm (nat_add m i)) :=
begin
  induction n with k hk,
  { exact i.elim0 },
  { cases classical.em (i = k),
    rw h,
    simp only [append_apply_snd', function.update_same],
    simp only [append_apply_snd', function.update_same],
    }
end

lemma append_add (ho : o = m + n) (f1 f2 : fin m → M) (g1 g2 : fin n → M) :
  append ho (f1 + f2) (g1 + g2) = append ho f1 g1 + append ho f2 g2 :=
begin
  ext,
  cases classical.em ((x : ℕ) < m),
  { simp only [pi.add_apply, append_apply_fst, h] },
  { simp only [pi.add_apply, append_apply_snd, h, not_false_iff] },
end

lemma append_smul (ho : o = m + n) (f : fin m → M) (g : fin n → M) (r : R) :
  r • append ho f g = append ho (r • f) (r • g) :=
begin
  ext,
  cases classical.em ((x : ℕ) < m),
  { simp only [pi.smul_apply, append_apply_fst, h] },
  { simp only [pi.smul_apply, append_apply_snd, h, not_false_iff] },
end

lemma append_update (ho : o = m + n) (i : fin n) (x : α) :
  append ho f (function.update g i x) =
    function.update (append ho f g) (cast ho.symm (nat_add m i)) x :=
begin
  ext y,
  cases classical.em ((y : ℕ) < m),
  { rw append_apply_fst _ _ ho y h,
    rw function.update_noteq _ _ _,
    rw append_apply_fst,
    contrapose! h,
    rw h,
    exact nat.le_add_right _ _ },
  rw append_apply_snd,
  cases classical.em (y = (cast ho.symm (nat_add m i))) with hi hi,
  { have hy : (⟨(y : ℕ) - m, (nat.sub_lt_left_iff_lt_add $ le_of_not_lt h).2 (ho ▸ y.2)⟩ : fin n) = i :=
    fin.ext (by rw [coe_mk, hi]; exact nat.add_sub_cancel_left _ _),
    rw hy,
    rw function.update_same,
    rw hi, rw function.update_same },
  rw function.update_noteq hi,
  rw function.update_noteq,
  rw append_apply_snd _ _ ho _ h,
  contrapose! hi,
  rw ←hi,
  ext,
  exact (nat.add_sub_of_le (not_lt.1 h)).symm,
end

lemma update_append (ho : o = m + n) (i : fin m) (x : α) :
  append ho (function.update f i x) g =
    function.update (append ho f g) (cast_lt i $ ho.symm ▸ nat.lt_add_right i m n i.2) x :=
begin
  ext y,
  cases classical.em ((y : ℕ) < m),
  rw append_apply_fst _ _ ho _ h,
  rcases classical.em (y = cast ho.symm (cast_add n i)) with ⟨rfl, hi⟩,
  erw function.update_same,
  convert function.update_same _ _ _,
  refl,
  ext, refl,
  rw function.update_noteq,
  rw function.update_noteq,
  rw append_apply_fst _ _ ho _ h,
  contrapose! h_1, rw h_1, ext, refl,
  contrapose! h_1, rw ←h_1, ext, refl,
  rw append_apply_snd _ _ ho _ h,
  rw function.update_noteq,
  rw append_apply_snd _ _ ho _ h,
  contrapose! h, exact h.symm ▸ i.2,
end

lemma append_assoc {k p r s : ℕ} (h : fin k → α) (ho : o = m + n)
  (hp : p = o + k) (hr : r = n + k) (hs : s = m + r) (x) :
  append hp (append ho f g) h x = append hs f (append hr g h) (cast (by rw [hp, hs, hr, ho, add_assoc]) x) :=
begin
  cases classical.em ((x : ℕ) < o) with hx hx,
  rw append_apply_fst _ _ hp _ hx,
  cases classical.em ((x : ℕ) < m) with hmx hmx,
  rw append_apply_fst _ _ hs,
  rw append_apply_fst _ _ ho,
  congr,
  exact hmx,
  rw append_apply_snd _ _ ho,
  rw append_apply_snd _ _ hs,
  rw append_apply_fst _ _ hr,
  congr,
  exact hmx,
  exact hmx,
  rw append_apply_snd _ _ hp,
  rw append_apply_snd _ _ hs,
  rw append_apply_snd _ _ hr,
  congr' 1,
  ext,
  rw coe_mk,
  rw coe_mk, rw coe_mk,
  rw nat.sub_sub,
  exact congr_arg _ ho,
  rw coe_mk,
  contrapose! hx,
  rw ho,
  exact nat.lt_add_of_sub_lt_left hx,
  contrapose! hx,
  rw ho,
  change (x : ℕ) < m at hx,
  exact lt_of_lt_of_le hx (le_add_right $ le_refl _),
  exact hx,
end

lemma append_assoc'  {k p r s : ℕ} (h : fin k → α) (ho : o = m + n)
  (hp : p = o + k) (hr : r = n + k) (hs : s = m + r) (x) :
  append hs f (append hr g h) x = append hp (append ho f g) h (cast (by rw [hp, hs, hr, ho, add_assoc]) x) :=
(append_assoc f g h ho hp hr hs (cast (by rw [hp, hs, hr, ho, add_assoc]) x)).symm

lemma init_tail {n : ℕ} (f : fin n.succ.succ → α) :
  init (tail f) = tail (init f) :=
begin
  ext,
  unfold tail,
  unfold init,
  congr,
  ext,
  simp only [coe_cast_succ, coe_succ],
end

theorem list.of_fn_succ' {n : ℕ} (f : fin n.succ → α) :
  list.of_fn f = list.concat (list.of_fn (fin.init f)) (f n) :=
begin
  induction n with n hn,
    simp,
  rw list.of_fn_succ, conv_rhs {rw list.of_fn_succ},
  unfold list.concat,
  have h0 : (0 : fin n.succ) = ⟨(0 : fin n.succ.succ), nat.succ_pos _⟩ :=
    by {ext, refl,},
  rw h0,
  rw init_apply,
  congr,
  erw hn (tail f),
  congr,
  ext,
  rw init_tail, refl,
  unfold tail,
  congr,
  ext,
  rw coe_nat_fin_succ,
  rw coe_succ,
  rw coe_nat_fin_succ,
end

lemma list.of_fn_succ_of_eq {m n : ℕ} (h : m = n.succ) (f : fin m → α) :
  list.of_fn f = f ⟨0, h.symm ▸ nat.succ_pos n⟩ :: list.of_fn (fin.tail (λ x, f (fin.cast h.symm x))) :=
begin
  convert list.of_fn_succ (λ i, f (fin.cast h.symm i)),
  rw fin.heq_fun_iff h,
  intro i,
  congr,
  ext, refl,
end

variables (x : α)

lemma cons_append {p : ℕ} (ho : o = m.succ + n) (hp : p = m + n) (x : α) (i : fin o):
  (append ho (cons x f : fin m.succ → α) g) i = (cons x (append hp f g) : fin p.succ → α) (cast (by rw [ho, nat.succ_add, ←hp]) i) :=
begin
  cases classical.em ((i : ℕ) < m.succ),
  rw append_apply_fst _ _ ho _ h,
  cases classical.em (cast (by rw [ho, nat.succ_add, ←hp]) i = 0) with hi hi,
  rw hi,
  rw cons_zero,
  convert cons_zero _ _,
  refl,
  ext,
  show (i : ℕ) = 0,
  exact (ext_iff _ _).1 hi,
  rw ←succ_pred _ hi,
  rw cons_succ,
  rw ←succ_pred (i.cast_lt h),
  rw cons_succ,
  rw append_apply_fst,
  congr,
  contrapose! hi,
  ext,
  show (i : ℕ) = 0,
  convert (ext_iff _ _).1 hi,
  rw append_apply_snd,
  rw ←succ_pred (cast (by rw [ho, nat.succ_add, ←hp]) i)
    (by {contrapose! h, convert nat.succ_pos _, exact (fin.ext_iff _ _).1 h}),
  rw cons_succ,
  rw append_apply_snd,
  congr' 1,
  ext,
  simp only [coe_pred, coe_cast, coe_mk],
  rw nat.succ_eq_add_one, rw add_comm, rw nat.sub_sub,
  intro hnot, apply h,
  convert nat.succ_lt_succ hnot,
  convert (nat.succ_pred_eq_of_pos _).symm,
  exact lt_of_lt_of_le (nat.succ_pos m) (not_lt.1 h),
  exact h,
end

lemma append_comp {β : Type*} (ho : o = m + n)
  (F : α → β) : append ho (F ∘ f) (F ∘ g) = F ∘ append ho f g :=
begin
  ext,
  cases classical.em ((x : ℕ) < m),
  rw append_apply_fst _ _ ho _ h,
  simp only [function.comp_app],
  rw append_apply_fst _ _ ho _ h,
  rw append_apply_snd _ _ ho _ h,
  simp only [function.comp_app],
  rw append_apply_snd _ _ ho _ h,
end

lemma list.of_fn_congr (h : n = m) :
  list.of_fn f = list.of_fn (f ∘ cast h) :=
begin
  congr,
  rw h,
  rw fin.heq_fun_iff h.symm,
  intro i,
  congr,
  ext,
  refl,
end

lemma of_fn_append (ho : o = m + n) :
  list.of_fn (append ho f g) = list.of_fn f ++ list.of_fn g :=
begin
  revert o f g ho,
  induction m with j hj,
  intros o f g ho,
  rw zero_add at ho,
  rw list.of_fn_zero,
  rw list.nil_append,
  congr, exact ho,
  rw fin.heq_fun_iff ho, intro i,
  exact fin.default_append _ _ ho _,
  intros o f g ho,
  have hjn : o.pred = j + n := by rw [ho, nat.succ_add_eq_succ_add]; refl,
  rw list.of_fn_succ,
  rw list.cons_append,
  erw ←hj (fin.tail f) g hjn,
  rw list.of_fn_congr _ ((nat.succ_add_eq_succ_add _ _).symm.trans ho.symm),
  rw list.of_fn_succ,
  congr,
  rw hjn,
  rw fin.heq_fun_iff hjn.symm,
  intro i,
  rw function.comp_app,
  conv_lhs {rw ←fin.cons_self_tail f},
  rw cons_append _ _ ho hjn,
  convert cons_succ _ _ _,
  refl,
  ext,
  simp only [coe_cast, coe_mk, coe_succ],
end

end fin
