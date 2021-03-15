import group_theory.perm.sign group_theory.group_action.basic m4r.fin

universes u v
variables {M : Type u} [add_comm_monoid M] {R : Type v} [ring R]
  (f : M →+ R) (q : ℕ)

lemma of_fn_prod_split (v : fin q.succ → M) :
  (list.of_fn (f ∘ v)).prod = f (v 0) * (list.of_fn (f ∘ fin.tail v)).prod :=
begin
  rw [list.of_fn_succ, list.prod_cons],
  refl
end

lemma of_fn_prod_self_adj_aux (v : fin q.succ → M) {j : fin q.succ}
  (hj : j.val = 1) (hv : v 0 = v j) (hf : ∀ x, f x * f x = 0) :
  f (v 0) * (list.of_fn (f ∘ fin.tail v)).prod = 0 :=
begin
  induction q with q hq,
  { exfalso,
    exact not_lt_of_le (le_of_eq (eq_comm.mp hj)) j.2 },
  { rw of_fn_prod_split,
    have hj1 : j = 1, by ext; exact hj,
    have fact : v (0 : fin q.succ).succ = v 1, by congr,
    rw hj1 at hv,
    rw [hv, ←mul_assoc],
    erw hf,
    rw zero_mul },
end

lemma of_fn_prod_self_adj (v : fin q → M) (i j : fin q) (hij : ↑i + 1 = ↑j) (hv : v i = v j)
  (hf : ∀ x, f x * f x = 0) :
  (list.of_fn (f ∘ v)).prod = 0 :=
begin
  induction q with q hq,
  { exfalso,
    exact nat.not_lt_zero ↑i i.property },
  rw of_fn_prod_split,
  cases classical.em (i = 0) with hem hem,
  { rw hem at hv,
    rw hem at hij,
    norm_num at hij,
    rw eq_comm at hij,
    exact of_fn_prod_self_adj_aux f _ v hij hv hf },
  { have hj : j ≠ 0 :=
    begin
      intro cj,
      rw cj at hij,
      simp only [fin.coe_zero, add_eq_zero_iff, one_ne_zero, and_false] at hij,
      assumption,
    end,
    have hij1 : ↑(i.pred hem) + 1 = ↑(j.pred hj) :=
      by rw [←fin.coe_succ, fin.succ_pred, fin.coe_pred, ←hij, nat.add_sub_cancel],
    have hv1 : (v ∘ fin.succ) (i.pred hem) = (v ∘ fin.succ) (j.pred hj) := by simp [hv],
    erw hq (v ∘ fin.succ) (i.pred hem) (j.pred hj) hij1 hv1,
    rw mul_zero },
end

lemma of_fn_prod_update {ι : Type v} [add_comm_monoid ι] {S : Type u} [ring S]
  (f : ι →+ S) {n : ℕ} (v : fin n → ι) {x y : ι} {i : fin n} :
  (list.of_fn (f ∘ function.update v i x)).prod + (list.of_fn (f ∘ function.update v i y)).prod =
    (list.of_fn (f ∘ function.update v i (x + y))).prod :=
begin
  induction n with n hn,
  { exact fin.elim0 i },
  { simp only [function.comp_app, list.of_fn_succ, list.prod_cons],
    cases classical.em (i = 0),
    { rw h,
      simp only [function.update_same, add_monoid_hom.map_add],
      rw add_mul,
      congr,
      any_goals { ext j,
        rw [function.update_noteq (fin.succ_ne_zero _),
            function.update_noteq (fin.succ_ne_zero _)] }},
      { have Hn := @hn (fin.tail v) (i.pred h),
        rw ←fin.succ_pred i h,
        repeat {rw [←fin.tail_update_succ, fin.comp_tail] at Hn},
        erw ←Hn,
        repeat {rw function.update_noteq},
        rw mul_add,
        refl,
        all_goals {rw fin.succ_pred _ h, exact (ne.symm h)}}},
end

lemma of_fn_prod_add_swap_adj (v : fin q → M) {i j : fin q} (hij : i.val + 1 = j.val)
  (hf : ∀ x, f x * f x = 0) :
  (list.of_fn (f ∘ v)).prod + (list.of_fn (f ∘ v ∘ equiv.swap i j)).prod = 0 :=
begin
  have hij1 : i ≠ j :=
  begin
    intro h,
    rw h at hij,
    exact nat.succ_ne_self j.val hij,
  end,
  have key : (list.of_fn (f ∘ function.update (function.update v i (v i + v j))
    j (v i + v j))).prod = 0 :=
  by rw of_fn_prod_self_adj f _ (function.update (function.update v i (v i + v j))
    j (v i + v j)) i j hij
    (begin
      rw [function.update_same, function.update_noteq hij1, function.update_same],
    end) hf,
  rw [←of_fn_prod_update, function.update_comm hij1 (v i + v j) (v i) v, ←of_fn_prod_update,
      of_fn_prod_self_adj f _ (function.update (function.update v j (v i)) i (v i)) i j hij
      begin
        rw [function.update_same, function.update_comm
          (ne_comm.mp hij1) (v i) (v i) v, function.update_same],
      end, zero_add, function.update_comm hij1 (v i + v j) (v j) v, ←of_fn_prod_update,
      of_fn_prod_self_adj f _ (function.update (function.update v j (v j)) i (v j)) i j hij
      begin
        rw [function.update_same, function.update_comm
        (ne_comm.mp hij1) (v j) (v j) v, function.update_same],
      end, add_zero, add_comm] at key,
  convert key,
  erw [function.update_eq_self, function.update_eq_self],
  ext x,
  { cases classical.em (x = i) with hx hx,
    { rw hx,
      simp only [equiv.swap_apply_left, function.comp_app],
      erw function.update_same },
    { cases classical.em (x = j) with hx1 hx1,
      { rw hx1,
        simp only [equiv.swap_apply_left, function.comp_app],
        rw function.update_noteq (ne_comm.mp hij1),
        erw function.update_same,
        simp only [equiv.swap_apply_right] },
      { simp only [hx, hx1, function.comp_app],
        rw [equiv.swap_apply_of_ne_of_ne hx hx1, function.update_noteq hx,
            function.update_noteq hx1] }}},
  all_goals {exact hf},
end

lemma of_fn_prod_swap_adj (v : fin q → M) {i j : fin q} (hij : i.val + 1 = j.val)
  (hf : ∀ x, f x * f x = 0) :
  (list.of_fn (f ∘ v ∘ equiv.swap i j)).prod = -(list.of_fn (f ∘ v)).prod  :=
begin
  apply eq_neg_of_add_eq_zero,
  rw add_comm,
  exact of_fn_prod_add_swap_adj f _ v hij hf,
end

lemma of_fn_prod_perm (v : fin q → M) (σ : equiv.perm (fin q))
  (hf : ∀ x, f x * f x = 0) :
  (list.of_fn (f ∘ v)).prod = (equiv.perm.sign σ) • (list.of_fn (f ∘ v ∘ σ)).prod :=
begin
  apply equiv.perm.swap_adj_induction_on' σ,
  rw [equiv.perm.sign_one, one_smul], congr,
  intros g x y hxy hI,
  have hxy1 : x ≠ y :=
  begin
    intro h,
    rw h at hxy,
    exact (nat.succ_ne_self y.val) hxy,
  end,
  have assoc : v ∘ (g * equiv.swap x y : equiv.perm (fin q)) = (v ∘ g ∘ equiv.swap x y) := rfl,
  rw [assoc, of_fn_prod_swap_adj _ _ (v ∘ g) hxy, ←neg_one_smul ℤ (list.of_fn (f ∘ v ∘ g)).prod],
  { have h1 : (-1 : ℤ) = equiv.perm.sign (equiv.swap x y) := by simp only [hxy1,
      equiv.perm.sign_swap', units.coe_neg_one, if_false],
    rw h1,
    have hack : ∀ z : R,
    (equiv.perm.sign (g * equiv.swap x y) : units ℤ) • z =
    (equiv.perm.sign (g * equiv.swap x y) : ℤ) • z := λ z, rfl,
    rw [hack, smul_smul, ←units.coe_mul, ←equiv.perm.sign_mul,
        mul_assoc, equiv.swap_mul_self, mul_one],
    assumption },
  { assumption },
end

lemma of_fn_prod_perm' (v : fin q → M) (σ : equiv.perm (fin q))
  (hf : ∀ x, f x * f x = 0) :
  σ.sign • (list.of_fn (f ∘ v)).prod = (list.of_fn (f ∘ v ∘ σ)).prod :=
begin
  cases int.units_eq_one_or σ.sign with h1 h1,
  { rw [h1, one_smul, of_fn_prod_perm _ _ _ σ hf, h1, one_smul] },
  { rw h1,
    erw neg_one_smul,
    rw [neg_eq_iff_neg_eq, of_fn_prod_perm _ _ v σ hf, h1],
    erw neg_one_smul },
end

lemma prod_eq_zero_of_ne_eq_aux {ι : Type v} [add_comm_monoid ι] {S : Type u} [ring S]
  (f : ι →+ S) (h : ∀ x, f x * f x = 0)
  {m n : ℕ} (hmn : m = n.succ.succ) (v : fin m → ι)
    (hv : v ⟨0, hmn.symm ▸ nat.succ_pos n.succ⟩ = v ⟨1, by
      rw hmn; exact nat.succ_lt_succ (nat.succ_pos _)⟩) :
  (list.of_fn (f ∘ v)).prod = 0 :=
begin
  rw [fin.list.of_fn_succ_of_eq hmn, list.of_fn_succ, list.prod_cons, list.prod_cons, ←mul_assoc],
  simp only [function.comp_app],
  rw hv,
  erw h,
  rw zero_mul,
end

lemma units_smul_eq_zero_iff {α : Type u} [semiring α] {β : Type v} [add_comm_monoid β]
  [distrib_mul_action α β] (u : units α) (x : β) :
  u • x = 0 ↔ x = 0 :=
begin
  rw ←smul_zero (↑u : α),
  show (↑u : α) • x = (↑u : α) • 0 ↔ _,
  rw [units.smul_left_cancel, smul_zero],
end

lemma prod_eq_zero_map {ι : Type u} [add_comm_monoid ι] {S : Type v} [ring S]
  (f : ι →+ S) (h : ∀ x : ι, f x * f x = 0)
  {i : ℕ} (v : fin i → ι) (j k : fin i) (hjk : j ≠ k) (hv : v j = v k) :
  (list.of_fn (f ∘ v)).prod = 0 :=
begin
  induction i with i hi,
  { exact fin.elim0 j },
  { induction i with i hi,
    { exact false.elim (hjk $ by rw [fin.unique.2 j, fin.unique.2 k]) },
    { suffices : ∃ (σ : equiv.perm (fin i.succ.succ)), (list.of_fn (f ∘ v ∘ σ)).prod = 0, by
      {  cases this with σ hσ,
         rw ←of_fn_prod_perm' _ _ _ _ h at hσ,
         rwa units_smul_eq_zero_iff at hσ },
    cases classical.em (j = 0) with hj0 hj0,
    { use (equiv.swap 1 k),
      simp only [equiv.swap_apply_left, function.comp_app, fin.succ_zero_eq_one,
        list.of_fn_succ, list.prod_cons],
      rw [equiv.swap_apply_of_ne_of_ne fin.zero_ne_one (by rw ←hj0; exact hjk),
          ←hj0, hv, ←mul_assoc, h, zero_mul] },
    { cases classical.em (j = 1) with hj1 hj1,
      { use (equiv.swap 0 k),
        simp only [equiv.swap_apply_left, function.comp_app, fin.succ_zero_eq_one,
          list.of_fn_succ, list.prod_cons],
        rw [equiv.swap_apply_of_ne_of_ne (ne.symm fin.zero_ne_one) (by rw ←hj1; exact hjk),
            ←hj1, hv, ←mul_assoc, h, zero_mul] },
      { cases classical.em (k = 0) with hk0 hk0,
        { use (equiv.swap 1 j),
          simp only [equiv.swap_apply_left, function.comp_app, fin.succ_zero_eq_one,
            list.of_fn_succ, list.prod_cons],
          rw [equiv.swap_apply_of_ne_of_ne fin.zero_ne_one (by rw ←hk0; exact ne.symm hjk),
              ←hk0, hv, ←mul_assoc, h, zero_mul] },
        { cases classical.em (k = 1) with hk1 hk1,
          { use (equiv.swap 0 j),
            simp only [equiv.swap_apply_left, function.comp_app, fin.succ_zero_eq_one,
              list.of_fn_succ, list.prod_cons],
            rw [equiv.swap_apply_of_ne_of_ne (ne.symm fin.zero_ne_one) (ne.symm hj1),
                ←hk1, hv, ←mul_assoc, h, zero_mul] },
          { use (equiv.swap 0 j).trans (equiv.swap 1 k),
            simp only [equiv.swap_apply_left, function.comp_app, fin.succ_zero_eq_one,
              list.of_fn_succ, equiv.coe_trans, list.prod_cons],
            rw [equiv.swap_apply_of_ne_of_ne hj1 hjk, equiv.swap_apply_of_ne_of_ne
                (ne.symm fin.zero_ne_one) (ne.symm hj1),
                equiv.swap_apply_left, hv, ←mul_assoc, h, zero_mul] }}}}}},
end
