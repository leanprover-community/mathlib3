/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Tim Baanen
-/
import algebra.algebra.basic
import data.equiv.fin
import data.fintype.card
import data.matrix.pequiv
import group_theory.perm.sign
import tactic.ring

universes u v w z
open equiv equiv.perm finset function

namespace matrix
open_locale matrix big_operators

variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [comm_ring R]

local notation `ε` σ:max := ((sign σ : ℤ ) : R)

/-- The determinant of a matrix given by the Leibniz formula. -/
definition det (M : matrix n n R) : R :=
∑ σ : perm n, ε σ * ∏ i, M (σ i) i

@[simp] lemma det_diagonal {d : n → R} : det (diagonal d) = ∏ i, d i :=
begin
  refine (finset.sum_eq_single 1 _ _).trans _,
  { intros σ h1 h2,
    cases not_forall.1 (mt equiv.ext h2) with x h3,
    convert mul_zero _,
    apply finset.prod_eq_zero,
    { change x ∈ _, simp },
    exact if_neg h3 },
  { simp },
  { simp }
end

@[simp] lemma det_zero (h : nonempty n) : det (0 : matrix n n R) = 0 :=
by rw [← diagonal_zero, det_diagonal, finset.prod_const, ← fintype.card,
  zero_pow (fintype.card_pos_iff.2 h)]

@[simp] lemma det_one : det (1 : matrix n n R) = 1 :=
by rw [← diagonal_one]; simp [-diagonal_one]

lemma det_eq_one_of_card_eq_zero {A : matrix n n R} (h : fintype.card n = 0) : det A = 1 :=
begin
  have perm_eq : (univ : finset (perm n)) = {1} :=
  univ_eq_singleton_of_card_one (1 : perm n) (by simp [card_univ, fintype.card_perm, h]),
  simp [det, card_eq_zero.mp h, perm_eq],
end

lemma det_mul_aux {M N : matrix n n R} {p : n → n} (H : ¬bijective p) :
  ∑ σ : perm n, (ε σ) * ∏ x, (M (σ x) (p x) * N (p x) x) = 0 :=
begin
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j,
  { rw [← fintype.injective_iff_bijective, injective] at H,
    push_neg at H,
    exact H },
  exact sum_involution
    (λ σ _, σ * swap i j)
    (λ σ _,
      have ∀ a, p (swap i j a) = p a := λ a, by simp only [swap_apply_def]; split_ifs; cc,
      have ∏ x, M (σ x) (p x) = ∏ x, M ((σ * swap i j) x) (p x),
        from prod_bij (λ a _, swap i j a) (λ _ _, mem_univ _) (by simp [this])
          (λ _ _ _ _ h, (swap i j).injective h)
          (λ b _, ⟨swap i j b, mem_univ _, by simp⟩),
      by simp [sign_mul, this, sign_swap hij, prod_mul_distrib])
    (λ σ _ _ h, hij (σ.injective $ by conv {to_lhs, rw ← h}; simp))
    (λ _ _, mem_univ _)
    (λ _ _, equiv.ext $ by simp)
end

@[simp] lemma det_mul (M N : matrix n n R) : det (M ⬝ N) = det M * det N :=
calc det (M ⬝ N) = ∑ p : n → n, ∑ σ : perm n, ε σ * ∏ i, (M (σ i) (p i) * N (p i) i) :
  by simp only [det, mul_apply, prod_univ_sum, mul_sum,
    fintype.pi_finset_univ]; rw [finset.sum_comm]
... = ∑ p in (@univ (n → n) _).filter bijective, ∑ σ : perm n,
    ε σ * ∏ i, (M (σ i) (p i) * N (p i) i) :
  eq.symm $ sum_subset (filter_subset _)
    (λ f _ hbij, det_mul_aux $ by simpa using hbij)
... = ∑ τ : perm n, ∑ σ : perm n, ε σ * ∏ i, (M (σ i) (τ i) * N (τ i) i) :
  sum_bij (λ p h, equiv.of_bijective p (mem_filter.1 h).2) (λ _ _, mem_univ _)
    (λ _ _, rfl) (λ _ _ _ _ h, by injection h)
    (λ b _, ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, injective_coe_fn rfl⟩)
... = ∑ σ : perm n, ∑ τ : perm n, (∏ i, N (σ i) i) * ε τ * (∏ j, M (τ j) (σ j)) :
  by simp [mul_sum, det, mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
... = ∑ σ : perm n, ∑ τ : perm n, (((∏ i, N (σ i) i) * (ε σ * ε τ)) * ∏ i, M (τ i) i) :
  sum_congr rfl (λ σ _, sum_bij (λ τ _, τ * σ⁻¹) (λ _ _, mem_univ _)
    (λ τ _,
      have ∏ j, M (τ j) (σ j) = ∏ j, M ((τ * σ⁻¹) j) j,
        by rw ← σ⁻¹.prod_comp; simp [mul_apply],
      have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
        calc ε σ * ε (τ * σ⁻¹) = ε ((τ * σ⁻¹) * σ) :
          by rw [mul_comm, sign_mul (τ * σ⁻¹)]; simp [sign_mul]
        ... = ε τ : by simp,
      by rw h; simp [this, mul_comm, mul_assoc, mul_left_comm])
    (λ _ _ _ _, mul_right_cancel) (λ τ _, ⟨τ * σ, by simp⟩))
... = det M * det N : by simp [det, mul_assoc, mul_sum, mul_comm, mul_left_comm]

instance : is_monoid_hom (det : matrix n n R → R) :=
{ map_one := det_one,
  map_mul := det_mul }

/-- Transposing a matrix preserves the determinant. -/
@[simp] lemma det_transpose (M : matrix n n R) : Mᵀ.det = M.det :=
begin
  apply sum_bij (λ σ _, σ⁻¹),
  { intros σ _, apply mem_univ },
  { intros σ _,
    rw [sign_inv],
    congr' 1,
    apply prod_bij (λ i _, σ i),
    { intros i _, apply mem_univ },
    { intros i _, simp },
    { intros i j _ _ h, simp at h, assumption },
    { intros i _, use σ⁻¹ i, finish } },
  { intros σ σ' _ _ h, simp at h, assumption },
  { intros σ _, use σ⁻¹, finish }
end

/-- The determinant of a permutation matrix equals its sign. -/
@[simp] lemma det_permutation (σ : perm n) :
  matrix.det (σ.to_pequiv.to_matrix : matrix n n R) = σ.sign := begin
  suffices : matrix.det (σ.to_pequiv.to_matrix) = ↑σ.sign * det (1 : matrix n n R), { simp [this] },
  unfold det,
  rw mul_sum,
  apply sum_bij (λ τ _, σ * τ),
  { intros τ _, apply mem_univ },
  { intros τ _,
    conv_lhs { rw [←one_mul (sign τ), ←int.units_pow_two (sign σ)] },
    conv_rhs { rw [←mul_assoc, coe_coe, sign_mul, units.coe_mul, int.cast_mul, ←mul_assoc] },
    congr,
    { simp [pow_two] },
    { ext i, apply pequiv.equiv_to_pequiv_to_matrix } },
  { intros τ τ' _ _, exact (mul_right_inj σ).mp },
  { intros τ _, use σ⁻¹ * τ, use (mem_univ _), exact (mul_inv_cancel_left _ _).symm }
end

/-- Permuting the columns changes the sign of the determinant. -/
lemma det_permute (σ : perm n) (M : matrix n n R) : matrix.det (λ i, M (σ i)) = σ.sign * M.det :=
by rw [←det_permutation, ←det_mul, pequiv.to_pequiv_mul_matrix]

@[simp] lemma det_smul {A : matrix n n R} {c : R} : det (c • A) = c ^ fintype.card n * det A :=
calc det (c • A) = det (matrix.mul (diagonal (λ _, c)) A) : by rw [smul_eq_diagonal_mul]
             ... = det (diagonal (λ _, c)) * det A        : det_mul _ _
             ... = c ^ fintype.card n * det A             : by simp [card_univ]

section hom_map

variables {S : Type w} [comm_ring S]

lemma ring_hom.map_det {M : matrix n n R} {f : R →+* S} :
  f M.det = matrix.det (f.map_matrix M) :=
by simp [matrix.det, f.map_sum, f.map_prod]

lemma alg_hom.map_det [algebra R S] {T : Type z} [comm_ring T] [algebra R T]
  {M : matrix n n S} {f : S →ₐ[R] T} :
  f M.det = matrix.det ((f : S →+* T).map_matrix M) :=
by rw [← alg_hom.coe_to_ring_hom, ring_hom.map_det]

end hom_map

section det_zero
/-!
### `det_zero` section

Prove that a matrix with a repeated column has determinant equal to zero.
-/

lemma det_eq_zero_of_row_eq_zero {A : matrix n n R} (i : n) (h : ∀ j, A i j = 0) : det A = 0 :=
begin
  rw [← det_transpose, det],
  convert @sum_const_zero _ _ (univ : finset (perm n)) _,
  ext σ,
  convert mul_zero ↑(sign σ),
  exact prod_eq_zero (mem_univ i) (h (σ i))
end

lemma det_eq_zero_of_column_eq_zero {A : matrix n n R} (j : n) (h : ∀ i, A i j = 0) : det A = 0 :=
by { rw ← det_transpose, exact det_eq_zero_of_row_eq_zero j h, }

/--
  `mod_swap i j` contains permutations up to swapping `i` and `j`.

  We use this to partition permutations in the expression for the determinant,
  such that each partitions sums up to `0`.
-/
def mod_swap {n : Type u} [decidable_eq n] (i j : n) : setoid (perm n) :=
⟨ λ σ τ, σ = τ ∨ σ = swap i j * τ,
  λ σ, or.inl (refl σ),
  λ σ τ h, or.cases_on h (λ h, or.inl h.symm) (λ h, or.inr (by rw [h, swap_mul_self_mul])),
  λ σ τ υ hστ hτυ, by cases hστ; cases hτυ; try {rw [hστ, hτυ, swap_mul_self_mul]}; finish⟩

instance (i j : n) : decidable_rel (mod_swap i j).r := λ σ τ, or.decidable

variables {M : matrix n n R} {i j : n}

/-- If a matrix has a repeated row, the determinant will be zero. -/
theorem det_zero_of_row_eq (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
begin
  have swap_invariant : ∀ k, M (swap i j k) = M k,
  { intros k,
    rw [swap_apply_def],
    by_cases k = i, { rw [if_pos h, h, ←hij] },
    rw [if_neg h],
    by_cases k = j, { rw [if_pos h, h, hij] },
    rw [if_neg h] },

  have : ∀ σ, _root_.disjoint {σ} {swap i j * σ},
  { intros σ,
    rw [disjoint_singleton, mem_singleton],
    exact (not_congr swap_mul_eq_iff).mpr i_ne_j },

  apply finset.sum_cancels_of_partition_cancels (mod_swap i j),
  intros σ _,
  erw [filter_or, filter_eq', filter_eq', if_pos (mem_univ σ), if_pos (mem_univ (swap i j * σ)),
    sum_union (this σ), sum_singleton, sum_singleton],
  convert add_right_neg (↑↑(sign σ) * ∏ i, M (σ i) i),
  rw [neg_mul_eq_neg_mul],
  congr,
  { rw [sign_mul, sign_swap i_ne_j], norm_num },
  ext j, rw [perm.mul_apply, swap_invariant]
end

end det_zero

lemma det_update_column_add (M : matrix n n R) (j : n) (u v : n → R) :
  det (update_column M j $ u + v) = det (update_column M j u) + det (update_column M j v) :=
begin
  simp only [det],
  have : ∀ σ : perm n, ∏ i, M.update_column j (u + v) (σ i) i =
                       ∏ i, M.update_column j u (σ i) i + ∏ i, M.update_column j v (σ i) i,
  { intros σ,
    simp only [update_column_apply, prod_ite, filter_eq',
               finset.prod_singleton, finset.mem_univ, if_true, pi.add_apply, add_mul] },
  rw [← sum_add_distrib],
  apply sum_congr rfl,
  intros x _,
  rw [this, mul_add]
end

lemma det_update_row_add (M : matrix n n R) (j : n) (u v : n → R) :
  det (update_row M j $ u + v) = det (update_row M j u) + det (update_row M j v) :=
begin
  rw [← det_transpose, ← update_column_transpose, det_update_column_add],
  simp [update_column_transpose, det_transpose]
end

lemma det_update_column_smul (M : matrix n n R) (j : n) (s : R) (u : n → R) :
  det (update_column M j $ s • u) = s * det (update_column M j u) :=
begin
  simp only [det],
  have : ∀ σ : perm n, ∏ i, M.update_column j (s • u) (σ i) i = s * ∏ i, M.update_column j u (σ i) i,
  { intros σ,
    simp only [update_column_apply, prod_ite, filter_eq', finset.prod_singleton, finset.mem_univ,
               if_true, algebra.id.smul_eq_mul, pi.smul_apply],
    ring },
  rw mul_sum,
  apply sum_congr rfl,
  intros x _,
  rw this,
  ring
end

lemma det_update_row_smul (M : matrix n n R) (j : n) (s : R) (u : n → R) :
  det (update_row M j $ s • u) = s * det (update_row M j u) :=
begin
  rw [← det_transpose, ← update_column_transpose, det_update_column_smul],
  simp [update_column_transpose, det_transpose]
end

@[simp] lemma det_block_diagonal {o : Type*} [fintype o] [decidable_eq o] (M : o → matrix n n R) :
  (block_diagonal M).det = ∏ k, (M k).det :=
begin
  -- Rewrite the determinants as a sum over permutations.
  unfold det,
  -- The right hand side is a product of sums, rewrite it as a sum of products.
  rw finset.prod_sum,
  simp_rw [finset.mem_univ, finset.prod_attach_univ, finset.univ_pi_univ],
  -- We claim that the only permutations contributing to the sum are those that
  -- preserve their second component.
  let preserving_snd : finset (equiv.perm (n × o)) :=
    finset.univ.filter (λ σ, ∀ x, (σ x).snd = x.snd),
  have mem_preserving_snd : ∀ {σ : equiv.perm (n × o)},
    σ ∈ preserving_snd ↔ ∀ x, (σ x).snd = x.snd :=
    λ σ, finset.mem_filter.trans ⟨λ h, h.2, λ h, ⟨finset.mem_univ _, h⟩⟩,
  rw ← finset.sum_subset (finset.subset_univ preserving_snd) _,
  -- And that these are in bijection with `o → equiv.perm m`.
  rw (finset.sum_bij (λ (σ : ∀ (k : o), k ∈ finset.univ → equiv.perm n) _,
                        prod_congr_left (λ k, σ k (finset.mem_univ k))) _ _ _ _).symm,
  { intros σ _,
    rw mem_preserving_snd,
    rintros ⟨k, x⟩,
    simp },
  { intros σ _,
    rw finset.prod_mul_distrib,
    congr,
    { convert congr_arg (λ (x : units ℤ), (↑x : R)) (sign_prod_congr_left (λ k, σ k _)).symm,
      simp, congr, ext, congr },
    rw [← finset.univ_product_univ, finset.prod_product, finset.prod_comm],
    simp },
  { intros σ σ' _ _ eq,
    ext x hx k,
    simp only at eq,
    have : ∀ k x, prod_congr_left (λ k, σ k (finset.mem_univ _)) (k, x) =
                  prod_congr_left (λ k, σ' k (finset.mem_univ _)) (k, x) :=
      λ k x, by rw eq,
    simp only [prod_congr_left_apply, prod.mk.inj_iff] at this,
    exact (this k x).1 },
  { intros σ hσ,
    rw mem_preserving_snd at hσ,
    have hσ' : ∀ x, (σ⁻¹ x).snd = x.snd,
    { intro x, conv_rhs { rw [← perm.apply_inv_self σ x, hσ] } },
    have mk_apply_eq : ∀ k x, ((σ (x, k)).fst, k) = σ (x, k),
    { intros k x,
      ext; simp [hσ] },
    have mk_inv_apply_eq : ∀ k x, ((σ⁻¹ (x, k)).fst, k) = σ⁻¹ (x, k),
    { intros k x,
      conv_lhs { rw ← perm.apply_inv_self σ (x, k) },
      ext; simp [hσ'] },
    refine ⟨λ k _, ⟨λ x, (σ (x, k)).fst, λ x, (σ⁻¹ (x, k)).fst, _, _⟩, _, _⟩,
    { intro x,
      simp [mk_apply_eq, mk_inv_apply_eq] },
    { intro x,
      simp [mk_apply_eq, mk_inv_apply_eq] },
    { apply finset.mem_univ },
    { ext ⟨k, x⟩; simp [hσ] } },
  { intros σ _ hσ,
    rw mem_preserving_snd at hσ,
    obtain ⟨⟨k, x⟩, hkx⟩ := not_forall.mp hσ,
    rw [finset.prod_eq_zero (finset.mem_univ (k, x)), mul_zero],
    rw [← @prod.mk.eta _ _ (σ (k, x)), block_diagonal_apply_ne],
    exact hkx }
end

lemma apply_zero_ne_zero_of_succ_eq_zero {n : ℕ} {σ : equiv.perm (fin n.succ)} {i : fin n}
  (h : σ i.succ = 0) : σ 0 ≠ 0 :=
mt (λ (h0 : σ 0 = 0), σ.injective (trans h h0.symm)) i.succ_ne_zero

/-- Turns a permutation on `fin n.succ` into a map on `fin n` by skipping `(0 : fin n.succ)`. -/
def perm_fin_succ_aux_aux {n : ℕ} (σ : equiv.perm (fin n.succ)) (hσ : σ 0 = 0) (i : fin n) : fin n :=
(σ i.succ).pred (mt (λ h, σ.injective (trans h hσ.symm)) i.succ_ne_zero)

lemma fin.pred_eq_iff {n : ℕ} {i : fin n.succ} {h : i ≠ 0} {j : fin n} :
  i.pred h = j ↔ i = j.succ :=
begin
  split; intro h,
  { rw [← h, fin.succ_pred] },
  { cases h, rw fin.pred_succ },
end

lemma succ_perm_fin_succ_aux_aux_eq_iff {n : ℕ} {σ : equiv.perm (fin n.succ)}
  {hσ : σ 0 = 0} {i : fin n} {j : fin n.succ} :
  (perm_fin_succ_aux_aux σ hσ i).succ = j ↔ σ i.succ = j :=
by { unfold perm_fin_succ_aux_aux, rw fin.succ_pred }

lemma perm_fin_succ_aux_aux_eq_iff {n : ℕ} {σ : equiv.perm (fin n.succ)}
  {hσ : σ 0 = 0} {i j : fin n} :
  perm_fin_succ_aux_aux σ hσ i = j ↔ σ i.succ = j.succ :=
by { unfold perm_fin_succ_aux_aux, rw fin.pred_eq_iff }

lemma inv_apply_eq_self {α : Type*} {σ : equiv.perm α} {x : α} (hσ : σ x = x) : σ⁻¹ x = x :=
σ.injective (trans (σ.apply_inv_self x) hσ.symm)

/-- Turns a permutation on `fin n.succ` into a permutation on `fin n` by skipping `(0 : fin n.succ)`. -/
def perm_fin_succ_aux {n : ℕ} (σ : equiv.perm (fin n.succ)) (hσ : σ 0 = 0) :
  equiv.perm (fin n) :=
{ to_fun := perm_fin_succ_aux_aux σ hσ,
  inv_fun := perm_fin_succ_aux_aux σ⁻¹ (inv_apply_eq_self hσ),
  left_inv := λ i,
    by rw [perm_fin_succ_aux_aux_eq_iff, inv_eq_iff_eq, succ_perm_fin_succ_aux_aux_eq_iff],
  right_inv := λ i,
    by rw [perm_fin_succ_aux_aux_eq_iff, ← eq_inv_iff_eq, succ_perm_fin_succ_aux_aux_eq_iff] }

lemma succ_perm_fin_succ_aux_eq_iff {n : ℕ} {σ : equiv.perm (fin n.succ)}
  {hσ : σ 0 = 0} {i : fin n} {j : fin n.succ} :
  (perm_fin_succ_aux σ hσ i).succ = j ↔ σ i.succ = j :=
succ_perm_fin_succ_aux_aux_eq_iff

lemma perm_fin_succ_aux_eq_iff {n : ℕ} {σ : equiv.perm (fin n.succ)}
  {hσ : σ 0 = 0} {i j : fin n} :
  perm_fin_succ_aux σ hσ i = j ↔ σ i.succ = j.succ :=
perm_fin_succ_aux_aux_eq_iff

@[simp] lemma sign_perm_fin_succ_aux {n : ℕ} (σ : equiv.perm (fin n.succ)) (hσ : σ 0 = 0) :
  sign (perm_fin_succ_aux σ hσ) = sign σ :=
sign_bij
  (λ i _, i.succ)
  (λ i _ _, by rw succ_perm_fin_succ_aux_eq_iff)
  (λ i j _ _ hij, fin.succ_injective _ hij)
  (λ i, by { refine fin.cons _ _ i,
             { contradiction },
             { intros i hi, exact ⟨i, mt perm_fin_succ_aux_eq_iff.mp hi, rfl⟩ } })

/-- Turns a permutation on `fin n` into a map on `fin n.succ` by inserting `0 ↦ 0`. -/
def perm_fin_succ_inv_aux {n : ℕ} (σ : equiv.perm (fin n)) :
  fin n.succ → fin n.succ :=
@fin.cons _ (λ _, fin n.succ) 0 (λ j, (σ j).succ)

@[simp] lemma perm_fin_succ_inv_aux_zero {n : ℕ} {σ : equiv.perm (fin n)} :
  perm_fin_succ_inv_aux σ 0 = 0 :=
by rw [perm_fin_succ_inv_aux, fin.cons_zero]

@[simp] lemma perm_fin_succ_inv_aux_succ {n : ℕ} {j : fin n} {σ : equiv.perm (fin n)} :
  perm_fin_succ_inv_aux σ j.succ = (σ j).succ :=
by rw [perm_fin_succ_inv_aux, fin.cons_succ]

lemma perm_fin_succ_inv_aux_eq_iff {n : ℕ} {i j : fin n.succ} {σ : equiv.perm (fin n)} :
  perm_fin_succ_inv_aux σ i = j ↔ (i = 0 ∧ j = 0) ∨ (∃ h : i ≠ 0, (σ (i.pred h)).succ = j) :=
begin
  refine fin.cons _ (λ i, _) i,
  { rw perm_fin_succ_inv_aux_zero,
    simp only [ne.def, eq_self_iff_true, eq_comm,
               true_and, not_true, or_false, not_false_iff, exists_prop_of_false] },
  { rw perm_fin_succ_inv_aux_succ,
    simp only [fin.pred_succ, exists_prop, i.succ_ne_zero,
               ne.def, true_and, false_and, false_or, not_false_iff] }
end

/-- Turns a permutation on `fin n` into a permutation on `fin n.succ` by inserting `0 ↦ 0`. -/
def perm_fin_succ_inv {n : ℕ} (σ : equiv.perm (fin n)) : equiv.perm (fin n.succ) :=
{ to_fun := perm_fin_succ_inv_aux σ,
  inv_fun := perm_fin_succ_inv_aux σ⁻¹,
  left_inv := λ i, begin
    refine fin.cases _ (λ i, _) i,
    { simp only [perm_fin_succ_inv_aux_zero] },
    { simp only [perm_fin_succ_inv_aux_succ, σ.inv_apply_self] },
  end,
  right_inv := λ i, begin
    refine fin.cases _ (λ i, _) i,
    { simp only [perm_fin_succ_inv_aux_zero] },
    { simp only [perm_fin_succ_inv_aux_succ, σ.apply_inv_self] },
  end }

@[simp] lemma perm_fin_succ_inv_zero {n : ℕ} {σ : equiv.perm (fin n)} :
  perm_fin_succ_inv σ 0 = 0 :=
@perm_fin_succ_inv_aux_zero n σ

@[simp] lemma perm_fin_succ_inv_succ {n : ℕ} {j : fin n} {σ : equiv.perm (fin n)} :
  perm_fin_succ_inv σ j.succ = (σ j).succ :=
perm_fin_succ_inv_aux_succ

lemma perm_fin_succ_inv_eq_iff {n : ℕ} {i j : fin n.succ} {σ : equiv.perm (fin n)} :
  perm_fin_succ_inv_aux σ i = j ↔ (i = 0 ∧ j = 0) ∨ (∃ h : i ≠ 0, (σ (i.pred h)).succ = j) :=
perm_fin_succ_inv_aux_eq_iff

/-- Permutations on `fin n.succ` can be given by their image of `0` and how they permute the rest. -/
def perm_fin_succ_equiv (n : ℕ) : equiv.perm (fin n.succ) ≃ fin n.succ × equiv.perm (fin n) :=
{ to_fun := λ σ, (σ 0, perm_fin_succ_aux (swap 0 (σ 0) * σ) (by simp)),
  inv_fun := λ iσ, swap 0 iσ.1 * perm_fin_succ_inv iσ.2,
  left_inv := λ σ, begin
    ext1 j,
    refine @fin.cons _ _ _ (λ j, _) j,
    { simp only [equiv.perm.mul_apply, perm_fin_succ_inv_zero, swap_apply_left] },
    { simp only [equiv.perm.mul_apply, perm_fin_succ_inv_succ, ← eq_inv_iff_eq, swap_inv,
                 succ_perm_fin_succ_aux_eq_iff, swap_apply_self, inv_apply_self] },
  end,
  right_inv := λ iσ, begin
    cases iσ with i σ,
    ext1,
    { simp only [equiv.perm.mul_apply, ← @eq_inv_iff_eq _ (swap _ _), swap_inv,
                 perm_fin_succ_inv_zero, swap_apply_right] },
    { ext1 j,
      simp only [equiv.perm.mul_apply, perm_fin_succ_inv_zero, swap_apply_left, swap_mul_self_mul,
                 perm_fin_succ_aux_eq_iff, perm_fin_succ_inv_succ] }
  end }

@[simp] lemma fst_perm_fin_succ {n : ℕ} (σ : equiv.perm (fin n.succ)) :
  (perm_fin_succ_equiv n σ).fst = σ 0 :=
rfl

lemma snd_perm_fin_succ {n : ℕ} (σ : equiv.perm (fin n.succ)) :
  (perm_fin_succ_equiv n σ).snd = perm_fin_succ_aux (swap 0 (σ 0) * σ) (by simp) :=
rfl

lemma snd_perm_fin_succ_eq_iff {n : ℕ} {σ : equiv.perm (fin n.succ)} {i j : fin n} :
  (perm_fin_succ_equiv n σ).snd i = j ↔ equiv.swap 0 (σ 0) (σ i.succ) = j.succ :=
perm_fin_succ_aux_eq_iff

lemma succ_snd_perm_fin_succ_equiv_eq_iff {n : ℕ} {σ : equiv.perm (fin n.succ)}
  {i : fin n} {j : fin n.succ} :
  ((perm_fin_succ_equiv n σ).snd i).succ = j ↔ equiv.swap 0 (σ 0) (σ i.succ) = j :=
succ_perm_fin_succ_aux_eq_iff

@[simp] lemma sign_snd_perm_fin_succ {n : ℕ} {σ : equiv.perm (fin n.succ)} :
  sign (perm_fin_succ_equiv n σ).snd = if σ 0 = 0 then sign σ else - sign σ :=
by simp [snd_perm_fin_succ, sign_swap', eq_comm]

/-- Expand a `n+1` by `n+1` matrix along a row.

This version of `det_succ` gives a minor matrix with one column swapped compared to `M`.
The version `det_succ_eq_sum_ite` has a separate term for `M 0 0`.
For the more traditional version, see `det_succ`.
-/
lemma det_succ_eq_sum_swap {n : ℕ} (M : matrix (fin n.succ) (fin n.succ) R) :
  det M =
    ∑ (j : fin n.succ), (if j = 0 then M j 0 else -M j 0) *
      det (λ (i' j' : fin n), M (swap 0 j i'.succ) j'.succ) :=
begin
  unfold det,
  simp_rw [mul_sum, ← sum_product', univ_product_univ],
  apply sum_bij' (λ σ _, perm_fin_succ_equiv n σ) _ _ (λ jσ _, (perm_fin_succ_equiv n).symm jσ),
  { simp },
  { simp },
  { intros, apply finset.mem_univ },
  { intros, apply finset.mem_univ },
  intros σ hσ,
  simp_rw [fst_perm_fin_succ, sign_snd_perm_fin_succ, fin.prod_univ_succ],
  push_cast,
  split_ifs with h;
    { simp only [one_mul, neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg,
                mul_assoc, mul_left_comm],
      congr,
      ext i,
      congr' 1,
      symmetry,
      rw [← eq_inv_iff_eq, swap_inv, succ_snd_perm_fin_succ_equiv_eq_iff] }
end

/-- Expand a `n+1` by `n+1` matrix along a row.

This version of `det_succ` gives a minor matrix with one column swapped compared to `M`.
The version `det_succ_eq_sum_swap` sums over `j : fin n.succ` using an extra `if`.
For the more traditional version, see `det_succ`.
-/
lemma det_succ_eq_sum_ite {n : ℕ} (M : matrix (fin n.succ) (fin n.succ) R) :
  det M = M 0 0 * det (λ (i' j' : fin n), M i'.succ j'.succ) +
    ∑ (j : fin n), - M j.succ 0 * det (λ (i' j' : fin n), M (if i' = j then 0 else i'.succ) j'.succ) :=
begin
  convert det_succ_eq_sum_swap M,
  simp_rw [fin.sum_univ_succ, if_pos rfl, swap_self, equiv.refl_apply],
  congr,
  ext j,
  rw if_neg j.succ_ne_zero,
  congr,
  ext i' j',
  split_ifs with hi'j,
  { rw [hi'j, swap_apply_right] },
  { rw swap_apply_of_ne_of_ne i'.succ_ne_zero (mt (λ h, fin.succ_injective _ h) hi'j) },
end

lemma cons_succ_above_eq_self_iff {n : ℕ} {i j : fin (n + 1)} :
  @fin.cons _ (λ _, fin (n + 1)) i i.succ_above j = i ↔ j = 0 :=
begin
  refine fin.cons _ (λ j, _) j,
  { simp },
  { simp [fin.succ_above_ne, fin.succ_ne_zero] }
end

lemma le_cast_succ_pred {n : ℕ} {i j : fin (n + 1)} :
  Π (h : j ≠ 0), i ≤ (j.pred h).cast_succ ↔ i < j :=
begin
  refine fin.cons _ (λ j, _) j,
  { contradiction },
  intro h,
  rw [fin.le_iff_coe_le_coe, fin.coe_cast_succ, fin.lt_iff_coe_lt_coe, fin.coe_succ, fin.pred_succ],
  exact nat.lt_succ_iff.symm
end

lemma fin.succ_above_pred_above {n : ℕ} {i j : fin (n + 1)} (h : j ≠ i) :
  i.succ_above (i.pred_above j h) = j :=
begin
  unfold fin.pred_above,
  split_ifs with hji,
  { rw i.succ_above_below; rwa fin.cast_succ_cast_lt },
  have := lt_of_le_of_ne (le_of_not_gt hji) h.symm,
  rw [i.succ_above_above, fin.succ_pred],
  rwa le_cast_succ_pred
end

/-- The permutation on `fin n` given by the cycle `(0 1 2 ... i-1)`.

If `n = 0` or `i ≤ 1`, this is the identity permutation.
-/
def cycle_range : Π {n : ℕ} (i : fin n), equiv.perm (fin n)
| 0 := λ _, 1
| (nat.succ n) := fin.cons 1 (λ i,
{ to_fun := λ j, if h : j = i.cast_succ then 0 else (fin.pred_above i.cast_succ j h).succ,
  inv_fun := λ j, @fin.cons _ (λ _, fin (n + 1)) i.cast_succ (fin.succ_above i.cast_succ) j,
  left_inv := λ j, begin
    dsimp only, split_ifs with h,
    { rw [h, dif_pos rfl, fin.cons_zero] },
    { rw [dif_neg h, fin.cons_succ, fin.succ_above_pred_above] }
  end,
  right_inv := λ j, begin
    simp only, split_ifs with h,
    { exact (cons_succ_above_eq_self_iff.mp h).symm },
    revert h,
    refine fin.cons _ (λ j, _) j,
    { simp },
    { intro h, simp [fin.cons_succ] }
  end })

lemma cycle_range_apply {n : ℕ} (i j : fin (n + 1)) :
  cycle_range i j = @fin.cons n (λ _, fin (n + 1))
    j
    (λ i, if h : j = i.cast_succ then 0 else (fin.pred_above i.cast_succ j h).succ)
    i :=
begin
  refine @fin.cons _ _ _ (λ i, _) i,
  { simp only [cycle_range, fin.cons_zero, equiv.perm.one_apply] },
  { simp only [cycle_range, fin.cons_succ, coe_fn_mk] },
end

@[simp] lemma cycle_range_zero_left {n : ℕ} : cycle_range (0 : fin (n + 1)) = 1 :=
by { ext1 j, rw [cycle_range_apply, fin.cons_zero, equiv.perm.one_apply] }

lemma cycle_range_succ_left {n : ℕ} (i : fin n) (j : fin (n + 1)) :
  cycle_range i.succ j = if h : j = i.cast_succ then 0 else (fin.pred_above i.cast_succ j h).succ :=
by simp only [cycle_range_apply, fin.cons_succ]

@[simp] lemma pred_above_zero {n : ℕ} (i : fin (n + 1)) (h : i ≠ 0) :
  fin.pred_above 0 i h = i.pred h :=
rfl

lemma fin.zero_lt_succ {n : ℕ} (i : fin n) : 0 < i.succ :=
by { rw [fin.lt_iff_coe_lt_coe, fin.coe_zero, fin.coe_succ], exact nat.zero_lt_succ _ }

@[simp] lemma pred_above_succ_zero {n : ℕ} (i : fin (n + 1)) (h : 0 ≠ i.succ) :
  fin.pred_above i.succ 0 h = 0 :=
dif_pos (fin.zero_lt_succ _)

@[simp] lemma cast_lt_zero {n k : ℕ} (h : 0 < k.succ) : fin.cast_lt (0 : fin n.succ) h = 0 :=
rfl

@[simp] lemma cycle_range_succ_zero {n : ℕ} {i : fin n} : cycle_range i.succ.succ 0 = 1 :=
begin
  rw [← fin.succ_zero_eq_one, cycle_range_succ_left],
  split_ifs with h; rw [← fin.cast_succ_zero, fin.cast_succ_inj] at h,
  { have := i.succ_ne_zero.symm,
    contradiction },
  rw [fin.pred_above, dif_pos, cast_lt_zero],
  exact fin.zero_lt_succ i
end

@[simp] lemma cycle_range_succ_self {n : ℕ} {i : fin n} : cycle_range i.succ i.cast_succ = 0 :=
by rw [cycle_range_succ_left, dif_pos rfl]

lemma fin.lt_succ_iff {n : ℕ} {i : fin (n + 1)} {j : fin n} : i < j.succ ↔ i ≤ j.cast_succ :=
by rw [fin.lt_iff_coe_lt_coe, fin.coe_succ, fin.le_iff_coe_le_coe, fin.coe_cast_succ, nat.lt_succ_iff]

lemma fin.succ_le_iff {n : ℕ} {i : fin n} {j : fin (n + 1)} : i.succ ≤ j ↔ i.cast_succ < j :=
by rw [fin.le_iff_coe_le_coe, fin.coe_succ, fin.lt_iff_coe_lt_coe, fin.coe_cast_succ, nat.succ_le_iff]

@[simp] lemma cycle_range_succ_succ_above {n : ℕ} {i j : fin n} (h : j ≠ i) :
  cycle_range (fin.succ i) ((fin.succ i).succ_above j) = j.succ :=
begin
  rw fin.succ_above,
  split_ifs with hsucc; rw cycle_range_succ_left; rw fin.lt_succ_iff at hsucc,
  { have : j.cast_succ ≠ i.cast_succ := mt fin.cast_succ_inj.mp h,
    rw [dif_neg this, fin.pred_above, dif_pos (lt_of_le_of_ne hsucc this), fin.cast_lt_cast_succ] },
  have hsucc := lt_of_not_ge hsucc,
  have : i.cast_succ < j.succ := fin.lt_succ_iff.mpr (le_of_lt hsucc),
  rw [dif_neg (ne_of_gt this), fin.pred_above, dif_neg (not_lt_of_gt this), fin.pred_succ],
end

lemma cycle_range_succ_above {n : ℕ} (i : fin (n + 1)) (j : fin n) :
  cycle_range i (i.succ_above j) = swap 0 i j.succ :=
begin
  refine @fin.cons _ (λ i, (cycle_range i) (i.succ_above j) = (swap 0 i) j.succ) _ (λ i, _) i,
  { simp [swap_self] },
  by_cases hji : j = i,
  { rw [hji, swap_apply_right, fin.succ_above_below, cycle_range_succ_self],
    exact fin.lt_succ },
  have := mt (λ h, fin.succ_injective _ h) hji,
  rw [swap_apply_of_ne_of_ne j.succ_ne_zero this, cycle_range_succ_succ_above hji]
end

/-- The permutation on `fin n` given by the cycle `(0 1 2 ... i)`.

If `n = 0` or `i = 0`, this is the identity permutation.
-/
def cycle_range' : Π {n : ℕ} (i : fin n), equiv.perm (fin n)
| 0 i := 1
| (nat.succ n) i :=
{ to_fun := λ j, if h : j = i then 0 else (fin.pred_above i j h).succ,
  inv_fun := λ j, @fin.cons _ (λ _, fin (n + 1)) i (fin.succ_above i) j,
  left_inv := λ j, begin
    dsimp only, split_ifs with h,
    { rw [h, dif_pos rfl, fin.cons_zero] },
    { rw [dif_neg h, fin.cons_succ, fin.succ_above_pred_above] }
  end,
  right_inv := λ j, begin
    simp only, split_ifs with h,
    { exact (cons_succ_above_eq_self_iff.mp h).symm },
    revert h,
    refine fin.cons _ (λ j, _) j,
    { simp },
    { intro h, simp [fin.cons_succ] }
  end }

lemma cycle_range'_apply {n : ℕ} (i j : fin (n + 1)) :
  cycle_range' i j = if h : j = i then 0 else (fin.pred_above i j h).succ :=
rfl

lemma cycle_range'_eq_iff {n : ℕ} (i j k : fin (n + 1)) :
  cycle_range' i j = k ↔ (k = 0 ∧ j = i) ∨ (k.cast_succ = j.succ ∧ j < i) ∨ (k = j ∧ i < j) :=
begin
  rw [cycle_range'_apply],
  split_ifs with heq,
  { simp [heq, lt_irrefl, eq_comm] },
  simp only [heq, and_false, false_or, fin.pred_above],
  split_ifs with hlt,
  { simp only [hlt, lt_asymm hlt, and_true, and_false, or_false],
    split; intro h; ext; simpa [eq_comm] using congr_arg (coe : _ → ℕ) h },
  { simp only [hlt, lt_of_le_of_ne (le_of_not_gt hlt) (ne.symm heq), and_false, false_or, and_true,
               fin.succ_pred, eq_comm], }
end

@[simp] lemma cycle_range'_zero {n : ℕ} : cycle_range' (0 : fin (n + 1)) = 1 :=
begin
  ext j,
  rw [cycle_range'_apply],
  split_ifs with h,
  { simp [h] },
  { simp }
end

@[simp] lemma cycle_range'_succ_zero {n : ℕ} (j : fin n) : cycle_range' j.succ 0 = 1 :=
begin
  cases n,
  { exact fin_zero_elim j },
  rw [cycle_range'_apply, dif_neg j.succ_ne_zero.symm, pred_above_succ_zero, fin.succ_zero_eq_one]
end

lemma cycle_range'_succ_zero_ne_zero {n : ℕ} (j : fin n) : cycle_range' j.succ 0 ≠ 0 :=
begin
  cases n,
  { exact fin_zero_elim j },
  rw [cycle_range'_apply, dif_neg j.succ_ne_zero.symm, pred_above_succ_zero],
  apply fin.succ_ne_zero
end

lemma fin.succ_cast_succ {n : ℕ} (j : fin n) : j.cast_succ.succ = j.succ.cast_succ :=
by { ext, simp }

lemma fin.succ_succ_above {n : ℕ} (i : fin (n + 1)) (j : fin n) :
  (i.succ_above j).succ = i.succ.succ_above j.succ :=
begin
  by_cases h : j.cast_succ < i,
  { have : j.succ.cast_succ < i.succ,
    { rwa [← fin.succ_cast_succ, fin.succ_lt_succ_iff] },
    rw [fin.succ_above_below _ _ h, fin.succ_above_below _ _ this, fin.succ_cast_succ] },
  { rw not_lt at h,
    have : i.succ ≤ j.succ.cast_succ,
    { rwa [← fin.succ_cast_succ, fin.succ_le_succ_iff] },
    rw [fin.succ_above_above _ _ h, fin.succ_above_above _ _ this] }
end

@[simp] lemma fin.cast_succ_lt_cast_succ {n : ℕ} {i j : fin n} :
  i.cast_succ < j.cast_succ ↔ i < j := iff.rfl

lemma succ_above_cycle_range' {n : ℕ} (i j : fin n) :
  i.succ.succ_above (cycle_range' i j) = swap 0 i.succ j.succ :=
begin
  cases n, { simp },
  rw [cycle_range', coe_fn_mk],
  split_ifs with heq,
  { rw [heq, swap_apply_right, fin.succ_above_below, fin.cast_succ_zero], exact fin.zero_lt_succ i },
  have : j.succ ≠ i.succ := mt (λ h, fin.succ_injective _ h) heq,
  rw [swap_apply_of_ne_of_ne (j.succ_ne_zero) this, fin.pred_above],
  split_ifs with hlt,
  { rw [← fin.succ_succ_above, fin.succ_above_below]; rwa fin.cast_succ_cast_lt },
  { rw [fin.succ_pred, fin.succ_above_above],
    rw [fin.succ_le_iff, fin.cast_succ_lt_cast_succ],
    exact lt_of_le_of_ne (le_of_not_gt hlt) (ne.symm heq) },
end

lemma cycle_range'_ne {n : ℕ} {i j : fin (n + 1)} :
  cycle_range' i j ≠ j ↔ i ≠ 0 ∧ j ≤ i :=
begin
rw [ne.def, cycle_range'_eq_iff],
  have : j.cast_succ ≠ j.succ := ne_of_lt (fin.cast_succ_lt_succ j),
  simp only [this, false_and, false_or, eq_self_iff_true, true_and],
  by_cases hi : i = 0,
  { simpa [hi, eq_comm] using eq_or_lt_of_le (fin.zero_le j) },
  push_neg,
  simp only [ne.def, hi, not_false_iff, true_and, and_iff_right_iff_imp],
  intros _ hj,
  exact mt (λ h, trans h.symm hj) hi
end

/-- `finset.fin_range' (i : fin n)` is the finset `{0, ..., i-1}` as a `finset (fin n)` -/
def finset.fin_range' {n : ℕ} (i : fin n) : finset (fin n) :=
(finset.range i).attach_fin (λ j hj, lt_trans (mem_range.mp hj) i.2)

@[simp] lemma finset.mem_fin_range' {n : ℕ} {i j : fin n} :
  i ∈ finset.fin_range' j ↔ i < j :=
by rw [finset.fin_range', mem_attach_fin, mem_range, fin.coe_fin_lt]

/-- `finset.fin_range_inclusive (i : fin n)` is the finset `{0, ..., i}` as a `finset (fin n)` -/
def finset.fin_range_inclusive {n : ℕ} (i : fin n) : finset (fin n) :=
(finset.range (i + 1)).attach_fin
  (λ j hj, lt_of_le_of_lt (nat.lt_succ_iff.mp (mem_range.mp hj)) i.2)

@[simp] lemma finset.mem_fin_range_inclusive {n : ℕ} {i j : fin n} :
i ∈ finset.fin_range_inclusive j ↔ i ≤ j :=
by rw [finset.fin_range_inclusive, mem_attach_fin, mem_range, nat.lt_succ_iff, fin.coe_fin_le]

@[simp] lemma finset.card_fin_range_inclusive {n : ℕ} (i : fin n) :
  (finset.fin_range_inclusive i).card = i + 1 :=
by rw [finset.fin_range_inclusive, card_attach_fin, card_range]

@[simp] lemma support_cycle_range'_succ {n : ℕ} (i : fin n) :
  (cycle_range' i.succ).support = finset.fin_range_inclusive i.succ :=
by { ext j, simp_rw [mem_support, finset.mem_fin_range_inclusive, cycle_range'_ne,
                     ne.def, i.succ_ne_zero, not_false_iff, true_and] }

lemma cycle_range'_pow_apply_zero {n : ℕ} (i j : fin (n + 1)) :
  j ≤ i → (cycle_range' i ^ (j : ℕ)) 0 = j :=
begin
  cases j with j hj, cases i with i hi,
  simp only [subtype.mk_le_mk, fin.coe_mk],
  induction j with j ih,
  { simp },
  intro h,
  ext,
  have j_lt_i : j < i := nat.succ_le_iff.mp h,
  rw [fin.coe_mk, nat.succ_eq_add_one, pow_succ, equiv.perm.mul_apply,
      ih (trans j.lt_succ_self hj) (trans j.le_succ h), cycle_range'_apply,
      dif_neg (mt subtype.mk_eq_mk.mp (ne_of_lt j_lt_i)), fin.coe_succ, fin.pred_above,
      dif_pos (subtype.mk_lt_mk.mpr j_lt_i), fin.coe_cast_lt, fin.coe_mk]
end

lemma is_cycle_cycle_range' {n : ℕ} (i : fin n) : is_cycle (cycle_range' i.succ) :=
⟨0, cycle_range'_succ_zero_ne_zero i,
 λ j hj, ⟨j, cycle_range'_pow_apply_zero i.succ j (cycle_range'_ne.mp hj).2⟩⟩

@[simp] lemma sign_cycle_range' {n : ℕ} (i : fin n) :
  sign (cycle_range' i) = (-1) ^ (i : ℕ) :=
begin
  cases n, { exact fin_zero_elim i },
  refine @fin.cons _ (λ i, sign (cycle_range' i) = (-1) ^ (i : ℕ)) _ (λ i, _) i,
  { simp },
  rw [sign_cycle (is_cycle_cycle_range' i), support_cycle_range'_succ,
      finset.card_fin_range_inclusive, pow_succ, units.neg_mul, one_mul, units.neg_neg],
end

/-- Expand a `n+1` by `n+1` matrix along row 0.

This version of `det_succ` gives a minor matrix with one column deleted.
For similar lemmas with one column swapped, see `det_succ_eq_sum_swap` and `det_succ_eq_sum_ite`.
-/
lemma det_succ_row {n : ℕ} (M : matrix (fin n.succ) (fin n.succ) R) :
  det M =
    ∑ (j : fin n.succ), (-1) ^ (j : ℕ) * M j 0 * det (λ (i' j' : fin n), M (j.succ_above i') j'.succ) :=
begin
  convert det_succ_eq_sum_swap M,
  ext j,
  refine fin.cons _ (λ j, _) j,
  { simp [swap_self] },
  rw [if_neg j.succ_ne_zero],
  simp_rw ← succ_above_cycle_range',
  rw [det_permute (cycle_range' j) (λ i' j', M ((fin.succ j).succ_above i') j'.succ),
      fin.coe_succ, pow_succ],
  simp, ring
end

/-- Expand a `n+1` by `n+1` matrix along column 0. -/
lemma det_succ_column {n : ℕ} (M : matrix (fin n.succ) (fin n.succ) R) :
  det M =
    ∑ (i : fin n.succ), (-1) ^ (i : ℕ) * M 0 i * det (λ (i' j' : fin n), M i'.succ (i.succ_above j')) :=
begin
  rw [← det_transpose, det_succ_row, finset.sum_congr rfl],
  intros i _,
  rw [transpose_apply, ← det_transpose],
  refl
end

end matrix
