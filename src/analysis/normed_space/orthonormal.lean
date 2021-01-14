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
def orthonormal (v : ι → E) : Prop :=
(∀ i, ∥v i∥ = 1) ∧ (∀ {i j}, i ≠ j → ⟪v i, v j⟫ = 0)

lemma inner_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (∥x∥ ^ 2 : 𝕜) :=
begin
  suffices : (is_R_or_C.re ⟪x, x⟫ : 𝕜) = ∥x∥ ^ 2,
  { simpa [inner_self_re_to_K] using this },
  exact_mod_cast (norm_sq_eq_inner x).symm
end

/-- Lemma to normalize a vector to unit length. -/
@[simp] lemma norm_smul_inv_norm {x : E} (hx : x ≠ 0) : ∥(∥x∥⁻¹ : 𝕜) • x∥ = 1 :=
begin
  have h : ∥(∥x∥ : 𝕜)∥ = ∥x∥,
  { rw is_R_or_C.norm_eq_abs,
    exact is_R_or_C.abs_of_nonneg (norm_nonneg _) },
  have : ∥x∥ ≠ 0 := by simp [hx],
  field_simp [norm_smul, h]
end

variables {𝕜}

@[simp] lemma eq_of_pow_two_eq_pow_two {R : Type*} [linear_ordered_field R] {a b : R}
  (ha : 0 ≤ a) (hb : 0 ≤ b) :
  a ^ 2 = b ^ 2 ↔ a = b :=
sorry

/-- `if ... then ... else` characterization of a set of vectors being orthonormal.  (Inner product
equals Kronecker delta.) -/
lemma orthonormal_iff_ite {v : ι → E} :
  orthonormal 𝕜 v ↔ ∀ i j, ⟪v i, v j⟫ = if i = j then (1:𝕜) else (0:𝕜) :=
begin
  split,
  { intros hv i j,
    split_ifs,
    { simp [h, inner_eq_norm_sq_to_K, hv.1] },
    { exact hv.2 h } },
  { intros h,
    split,
    { intros i,
      have h' : ∥v i∥ ^ 2 = 1 ^ 2,
      { simp [norm_sq_eq_inner, h i i] },
      have h₁ : 0 ≤ ∥v i∥ := norm_nonneg _,
      have h₂ : (0:ℝ) ≤ 1 := by norm_num,
      rwa eq_of_pow_two_eq_pow_two h₁ h₂ at h' },
    { intros i j hij,
      simpa [hij] using h i j } }
end

lemma mysum {v : ι → E} (he : orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
  ⟪v i, finsupp.total ι E 𝕜 v l⟫ = l i :=
by simp [finsupp.total_apply, finsupp.inner_sum, orthonormal_iff_ite.mp he]

/-- An orthonormal set is linearly independent. -/
lemma linear_independent_of_orthonormal {v : ι → E} (he : orthonormal 𝕜 v) :
  linear_independent 𝕜 v :=
begin
  rw linear_independent_iff,
  intros l hl,
  ext i,
  have key : ⟪v i, finsupp.total ι E 𝕜 v l⟫ = ⟪v i, 0⟫ := by rw hl,
  simpa [mysum he] using key
end

lemma is_basis_of_orthonormal_of_card_eq_findim [fintype ι] [nonempty ι] [finite_dimensional 𝕜 E]
  {v : ι → E} (he : orthonormal 𝕜 v) (card_eq : fintype.card ι = findim 𝕜 E) :
  is_basis 𝕜 v :=
is_basis_of_linear_independent_of_card_eq_findim
(linear_independent_of_orthonormal he) card_eq

/-- A basis on `ι` for a finite-dimensional inner product space induces a continuous linear
equivalence with `euclidean_space 𝕜 ι`.  If the basis is orthonormal, this continuous linear
equivalence is an isometry, but we don't prove that here. -/
def is_basis.equiv_fun_euclidean [fintype ι] [finite_dimensional 𝕜 E]
  {v : ι → E} (h : is_basis 𝕜 v) :
  E ≃L[𝕜] (euclidean_space 𝕜 ι) :=
h.equiv_fun.to_continuous_linear_equiv

variables (𝕜)

/-- Finite dimensional `inner_product_space`s have nonzero orthonormal sets of maximal size. -/
theorem exists_max_orthonormal [finite_dimensional 𝕜 E] :
  ∃ (v : fin (findim 𝕜 E) → E), orthonormal 𝕜 v :=
begin
  tactic.unfreeze_local_instances,
  -- prove this by induction on the dimension
  induction hk : findim 𝕜 E with k IH generalizing E,
  { -- base case trivial
    use λ i, 0,
    have h₀ : fin 0 → fin 0 → false := fin.elim0,
    simpa [orthonormal_iff_ite] using h₀ },
  -- in the inductive step, the `inner_product_space` must contain a nonzero vector
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0,
  { rw [← @findim_pos_iff_exists_ne_zero 𝕜, hk],
    exact k.succ_pos },
  -- normalize it
  let e := (∥x∥⁻¹ : 𝕜) • x,
  have he : ∥e∥ = 1 := by simp [e, norm_smul_inv_norm 𝕜 hx],
  -- by the inductive hypothesis, find an orthonormal basis for its orthogonal complement
  obtain ⟨w, hw₁, hw₂⟩ : ∃ w : fin k → (𝕜 ∙ e)ᗮ, orthonormal 𝕜 w,
  { have he' : e ≠ 0,
    { rw [← norm_pos_iff, he],
      norm_num },
    apply IH,
    simp [findim_orthogonal_span_singleton he', hk],
    apply_instance },
  -- put these together to provide a candidate orthonormal basis `v` for the whole space
  let v : fin (k + 1) → E := λ i, if h : i ≠ 0 then coe (w (i.pred h)) else e,
  refine ⟨v, _, _⟩,
  { -- show that the elements of `v` have unit length
    intro i,
    by_cases h : i = 0,
    { simp [v, h, he] },
    { simpa [v, h] using hw₁ (i.pred h) } },
  { -- show that the elements of `v` are orthogonal
    have h_end : ∀ (j : fin k.succ), 0 ≠ j → ⟪v 0, v j⟫ = 0,
    { intros j hj,
      suffices : ⟪e, w (j.pred hj.symm)⟫ = 0,
      { simpa [v, hj.symm] using this },
      apply inner_right_of_mem_orthogonal_singleton,
      exact (w (j.pred hj.symm)).2 },
    intro i,
    by_cases hi : i = 0,
    { rw hi,
      exact h_end },
    intros j inej,
    by_cases hj : j = 0,
    { rw [hj, inner_eq_zero_sym],
      apply h_end _ (ne.symm hi) },
    have : ⟪w (i.pred hi), w (j.pred hj)⟫ = 0 := by simp [inej, hw₂],
    simpa [v, hi, hj] using this }
end


variables (E)

def maximal_orthonormal [finite_dimensional 𝕜 E] : fin (findim 𝕜 E) → E :=
classical.some (exists_max_orthonormal 𝕜)


lemma maximal_orthonormal_spec [finite_dimensional 𝕜 E] :
  orthonormal 𝕜 (maximal_orthonormal 𝕜 E) :=
classical.some_spec (exists_max_orthonormal 𝕜)

instance has_one_findim [nontrivial E] [finite_dimensional 𝕜 E] : has_one (fin (findim 𝕜 E)) :=
begin
  have h : findim 𝕜 E ≠ 0 := ne_of_gt findim_pos,
  rw classical.some_spec (nat.exists_eq_succ_of_ne_zero h),
  apply_instance
end

variables (E)

lemma is_basis_max_orthonormal [nontrivial E] [finite_dimensional 𝕜 E] :
  is_basis 𝕜 (maximal_orthonormal 𝕜 E) :=
is_basis_of_orthonormal_of_card_eq_findim
  (maximal_orthonormal_spec 𝕜 E)
  (by simp)
