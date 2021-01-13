import analysis.normed_space.inner_product

noncomputable theory

open_locale big_operators classical
open submodule finite_dimensional

variables (𝕜 : Type*) {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
variables {ι : Type*}

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y -- here work over 𝕜

/-- Induced inner product on a submodule. -/
instance submodule_inner_product_space {W : submodule 𝕜 E} : inner_product_space 𝕜 W :=
{ inner             := λ x y, ⟪(x:E), ↑y⟫,
  conj_sym          := λ _ _, inner_conj_sym _ _ ,
  nonneg_im         := λ _, inner_self_nonneg_im,
  norm_sq_eq_inner  := λ _, norm_sq_eq_inner _,
  add_left          := λ _ _ _ , inner_add_left,
  smul_left         := λ _ _ _, inner_smul_left,
  ..submodule.normed_space W }

/-- The inner product on submodules is the same as on the ambient space. -/
@[simp] lemma coe_inner (W : submodule 𝕜 E) (x y: W) : ⟪x, y⟫ = ⟪(x:E), ↑y⟫ := rfl

/-- An orthonormal set of vectors in an `inner_product_space` -/
def orthonormal [decidable_eq ι] (v : ι → E) : Prop :=
∀ i j, ⟪v i, v j⟫ = if i = j then (1:𝕜) else (0:𝕜)

/-- An orthonormal set is linearly independent. -/
lemma linear_independent_of_orthonormal (v : ι → E) (he : orthonormal 𝕜 v) :
  linear_independent 𝕜 v :=
begin
  rw linear_independent_iff,
  intros l hl,
  ext i,
  have h_fun : (λ j a, a * ⟪v i, v j⟫) = λ j a, a * (if i = j then (1:𝕜) else (0:𝕜)),
  { ext j,
    simp [he i j] },
  have key : ⟪v i, finsupp.total ι E 𝕜 v l⟫ = ⟪v i, 0⟫ := by rw hl,
  simpa [finsupp.total_apply, finsupp.inner_sum, h_fun] using key
end

lemma is_basis_of_orthonormal_of_card_eq_findim [fintype ι] [nonempty ι]
  [finite_dimensional 𝕜 E]
  (v : ι → E) (he : orthonormal 𝕜 v) (card_eq : fintype.card ι = findim 𝕜 E) :
  is_basis 𝕜 v :=
is_basis_of_linear_independent_of_card_eq_findim
(linear_independent_of_orthonormal 𝕜 v he) card_eq

/-- A basis on `ι` for a finite-dimensional inner product space induces a continuous linear
equivalence with `euclidean_space 𝕜 ι`.  If the basis is orthonormal, this continuous linear
equivalence is an isometry, but we don't prove that here. -/
def is_basis.equiv_fun_euclidean [fintype ι] [finite_dimensional 𝕜 E]
  {v : ι → E} (h : is_basis 𝕜 v) :
  E ≃L[𝕜] (euclidean_space 𝕜 ι) :=
h.equiv_fun.to_continuous_linear_equiv

/-- Finite dimensional `inner_product_space`s have nonzero orthonormal sets of maximal size. -/
theorem exists_max_orthonormal [finite_dimensional 𝕜 E] :
  ∃ (v : fin (findim 𝕜 E) → E), orthonormal 𝕜 v :=
begin
  tactic.unfreeze_local_instances,
  induction hk : findim 𝕜 E with k IH generalizing E,
  { use λ i, 0,
    have h₀ : fin 0 → fin 0 → false := fin.elim0,
    simpa [orthonormal] using h₀ },
  have hE : 0 < findim 𝕜 E,
  { rw hk,
    exact k.succ_pos },
  obtain ⟨x, hx⟩ := findim_pos_iff_exists_ne_zero.mp hE,
  let e := (∥x∥⁻¹ : 𝕜) • x,
  have he : ∥e∥ = 1,
  { simp [e],
    have : ∥(∥x∥ : 𝕜)∥ = ∥x∥,
    { rw is_R_or_C.norm_eq_abs,
      exact is_R_or_C.abs_of_nonneg (norm_nonneg _) },
    simp [norm_smul, this],
    rw inv_mul_cancel,
    simp [hx] },
  have he' : ⟪e, e⟫ = 1,
  { rw ← inner_self_re_to_K,
    rw ← norm_sq_eq_inner,
    rw he,
    simp },
  have he'' : e ≠ 0,
  { rw [← norm_pos_iff, he],
    norm_num },
  have dim_perp_to_line : findim 𝕜 (𝕜 ∙ e)ᗮ = k,
  { simp [findim_orthogonal_span_singleton he'', hk] },
  -- apply our inductive hyp to `(𝕜 ∙ e)ᗮ`
  obtain ⟨w, hw⟩ := IH dim_perp_to_line,
  let v : fin (k + 1) → E := λ i, if h : i ≠ 0 then coe (w (i.pred h)) else e,
  -- refine ⟨v, _⟩,
  have h_end : ∀ (j : fin (k.succ)), 0 ≠ j → ⟪v 0, v j⟫ = 0,
  { intros j hj,
    suffices : ⟪e, w (j.pred hj.symm)⟫ = 0,
    { simpa [v, hj.symm] using this },
    apply inner_right_of_mem_orthogonal_singleton,
    exact (w (j.pred hj.symm)).2 },
  use v,
  intros i,
  by_cases h : i = 0,
  { rw h,
    intros j,
    by_cases h' : j = 0,
    { simp [v, h', he'] },
    { convert h_end _ (ne.symm h'),
      simp [ne.symm h'], } },
  { intros j,
    by_cases h' : j = 0,
    { rw h',
      rw ← inner_conj_sym,
      rw h_end i (ne.symm h),
      simp [h] },
    { convert hw (i.pred h) (j.pred h') using 1,
      { simp [v, h, h'] },
      { refine if_congr _ rfl rfl,
        simp } } }
end

variables (E)

def max_orthonormal [finite_dimensional 𝕜 E] : fin (findim 𝕜 E) → E :=
classical.some (exists_max_orthonormal 𝕜)


lemma max_orthonormal_spec [finite_dimensional 𝕜 E] : orthonormal 𝕜 (max_orthonormal 𝕜 E) :=
classical.some_spec (exists_max_orthonormal 𝕜)

instance has_one_findim [nontrivial E] [finite_dimensional 𝕜 E] : has_one (fin (findim 𝕜 E)) :=
begin
  have h : findim 𝕜 E ≠ 0 := ne_of_gt findim_pos,
  rw classical.some_spec (nat.exists_eq_succ_of_ne_zero h),
  exact fin.has_one
end

variables (E)

lemma is_basis_max_orthonormal [nontrivial E] [finite_dimensional 𝕜 E] :
  is_basis 𝕜 (max_orthonormal 𝕜 E) :=
is_basis_of_orthonormal_of_card_eq_findim 𝕜
  (max_orthonormal 𝕜 E)
  (max_orthonormal_spec 𝕜 E)
  (by simp)
