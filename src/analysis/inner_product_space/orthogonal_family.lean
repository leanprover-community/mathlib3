/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import analysis.inner_product_space.basic
import analysis.normed_space.bounded_linear_maps

/-!
# Families of mutually-orthogonal subspaces of an inner product space

## Tags

inner product space, Hilbert space, norm, orthogonal subspaces

-/

noncomputable theory

variables {𝕜 : Type*} {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
open real
open_locale big_operators

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

section orthogonal_family

variables {ι : Type*} [dec_ι : decidable_eq ι] (𝕜)
open_locale direct_sum

/-- An indexed family of mutually-orthogonal subspaces of an inner product space `E`.

The simple way to express this concept would be as a condition on `V : ι → submodule 𝕜 E`.  We
We instead implement it as a condition on a family of inner product spaces each equipped with an
isometric embedding into `E`, thus making it a property of morphisms rather than subobjects.

This definition is less lightweight, but allows for better definitional properties when the inner
product space structure on each of the submodules is important -- for example, when considering
their Hilbert sum (`pi_lp V 2`).  For example, given an orthonormal set of vectors `v : ι → E`,
we have an associated orthogonal family of one-dimensional subspaces of `E`, which it is convenient
to be able to discuss using `ι → 𝕜` rather than `Π i : ι, span 𝕜 (v i)`. -/
def orthogonal_family {G : ι → Type*} [Π i, inner_product_space 𝕜 (G i)] (V : Π i, G i →ₗᵢ[𝕜] E) :
  Prop :=
∀ ⦃i j⦄, i ≠ j → ∀ v : G i, ∀ w : G j, ⟪V i v, V j w⟫ = 0

variables {𝕜} {G : ι → Type*} [Π i, inner_product_space 𝕜 (G i)] {V : Π i, G i →ₗᵢ[𝕜] E}
  (hV : orthogonal_family 𝕜 V) [dec_V : Π i (x : G i), decidable (x ≠ 0)]

lemma orthonormal.orthogonal_family {v : ι → E} (hv : orthonormal 𝕜 v) :
  @orthogonal_family 𝕜 _ _ _ _ (λ i : ι, 𝕜) _
    (λ i, linear_isometry.to_span_singleton 𝕜 E (hv.1 i)) :=
λ i j hij a b, by simp [inner_smul_left, inner_smul_right, hv.2 hij]

include hV dec_ι
lemma orthogonal_family.eq_ite {i j : ι} (v : G i) (w : G j) :
  ⟪V i v, V j w⟫ = ite (i = j) ⟪V i v, V j w⟫ 0 :=
begin
  split_ifs,
  { refl },
  { exact hV h v w }
end

include dec_V
lemma orthogonal_family.inner_right_dfinsupp (l : ⨁ i, G i) (i : ι) (v : G i) :
  ⟪V i v, l.sum (λ j, V j)⟫ = ⟪v, l i⟫ :=
calc ⟪V i v, l.sum (λ j, V j)⟫
    = l.sum (λ j, λ w, ⟪V i v, V j w⟫) : dfinsupp.inner_sum (λ j, V j) l (V i v)
... = l.sum (λ j, λ w, ite (i=j) ⟪V i v, V j w⟫ 0) :
  congr_arg l.sum $ funext $ λ j, funext $ hV.eq_ite v
... = ⟪v, l i⟫ :
begin
  simp only [dfinsupp.sum, submodule.coe_inner, finset.sum_ite_eq, ite_eq_left_iff,
    dfinsupp.mem_support_to_fun],
  split_ifs with h h,
  { simp only [linear_isometry.inner_map_map] },
  { simp only [of_not_not h, inner_zero_right] },
end
omit dec_ι dec_V

lemma orthogonal_family.inner_right_fintype [fintype ι] (l : Π i, G i) (i : ι) (v : G i) :
  ⟪V i v, ∑ j : ι, V j (l j)⟫ = ⟪v, l i⟫ :=
by classical;
calc ⟪V i v, ∑ j : ι, V j (l j)⟫
    = ∑ j : ι, ⟪V i v, V j (l j)⟫: by rw inner_sum
... = ∑ j, ite (i = j) ⟪V i v, V j (l j)⟫ 0 :
  congr_arg (finset.sum finset.univ) $ funext $ λ j, (hV.eq_ite v (l j))
... = ⟪v, l i⟫ : by simp only [finset.sum_ite_eq, finset.mem_univ, (V i).inner_map_map, if_true]

lemma orthogonal_family.inner_sum (l₁ l₂ : Π i, G i) (s : finset ι) :
  ⟪∑ i in s, V i (l₁ i), ∑ j in s, V j (l₂ j)⟫ = ∑ i in s, ⟪l₁ i, l₂ i⟫ :=
by classical;
calc ⟪∑ i in s, V i (l₁ i), ∑ j in s, V j (l₂ j)⟫
    = ∑ j in s, ∑ i in s, ⟪V i (l₁ i), V j (l₂ j)⟫ : by simp only [sum_inner, inner_sum]
... = ∑ j in s, ∑ i in s, ite (i = j) ⟪V i (l₁ i), V j (l₂ j)⟫ 0 :
begin
  congr' with i,
  congr' with j,
  apply hV.eq_ite,
end
... = ∑ i in s, ⟪l₁ i, l₂ i⟫ : by simp only [finset.sum_ite_of_true,
  finset.sum_ite_eq', linear_isometry.inner_map_map, imp_self, implies_true_iff]

lemma orthogonal_family.norm_sum (l : Π i, G i) (s : finset ι) :
  ‖∑ i in s, V i (l i)‖ ^ 2 = ∑ i in s, ‖l i‖ ^ 2 :=
begin
  have : (‖∑ i in s, V i (l i)‖ ^ 2 : 𝕜) = ∑ i in s, ‖l i‖ ^ 2,
  { simp only [← inner_self_eq_norm_sq_to_K, hV.inner_sum] },
  exact_mod_cast this,
end

/-- The composition of an orthogonal family of subspaces with an injective function is also an
orthogonal family. -/
lemma orthogonal_family.comp {γ : Type*} {f : γ → ι} (hf : function.injective f) :
  orthogonal_family 𝕜 (λ g : γ, (V (f g) : G (f g) →ₗᵢ[𝕜] E)) :=
λ i j hij v w, hV (hf.ne hij) v w

lemma orthogonal_family.orthonormal_sigma_orthonormal {α : ι → Type*} {v_family : Π i, (α i) → G i}
  (hv_family : ∀ i, orthonormal 𝕜 (v_family i)) :
  orthonormal 𝕜 (λ a : Σ i, α i, V a.1 (v_family a.1 a.2)) :=
begin
  split,
  { rintros ⟨i, v⟩,
    simpa only [linear_isometry.norm_map] using (hv_family i).left v },
  rintros ⟨i, v⟩ ⟨j, w⟩ hvw,
  by_cases hij : i = j,
  { subst hij,
    have : v ≠ w := λ h, by { subst h, exact hvw rfl },
    simpa only [linear_isometry.inner_map_map] using (hv_family i).2 this },
  { exact hV hij (v_family i v) (v_family j w) }
end

include dec_ι
lemma orthogonal_family.norm_sq_diff_sum (f : Π i, G i) (s₁ s₂ : finset ι) :
  ‖∑ i in s₁, V i (f i) - ∑ i in s₂, V i (f i)‖ ^ 2
  = ∑ i in s₁ \ s₂, ‖f i‖ ^ 2 + ∑ i in s₂ \ s₁, ‖f i‖ ^ 2 :=
begin
  rw [← finset.sum_sdiff_sub_sum_sdiff, sub_eq_add_neg, ← finset.sum_neg_distrib],
  let F : Π i, G i := λ i, if i ∈ s₁ then f i else - (f i),
  have hF₁ : ∀ i ∈ s₁ \ s₂, F i = f i := λ i hi, if_pos (finset.sdiff_subset _ _ hi),
  have hF₂ : ∀ i ∈ s₂ \ s₁, F i = - f i := λ i hi, if_neg (finset.mem_sdiff.mp hi).2,
  have hF : ∀ i, ‖F i‖ = ‖f i‖,
  { intros i,
    dsimp only [F],
    split_ifs;
    simp only [eq_self_iff_true, norm_neg], },
  have : ‖∑ i in s₁ \ s₂, V i (F i) + ∑ i in s₂ \ s₁, V i (F i)‖ ^ 2 =
    ∑ i in s₁ \ s₂, ‖F i‖ ^ 2 + ∑ i in s₂ \ s₁, ‖F i‖ ^ 2,
  { have hs : disjoint (s₁ \ s₂) (s₂ \ s₁) := disjoint_sdiff_sdiff,
    simpa only [finset.sum_union hs] using hV.norm_sum F (s₁ \ s₂ ∪ s₂ \ s₁) },
  convert this using 4,
  { refine finset.sum_congr rfl (λ i hi, _),
    simp only [hF₁ i hi] },
  { refine finset.sum_congr rfl (λ i hi, _),
    simp only [hF₂ i hi, linear_isometry.map_neg] },
  { simp only [hF] },
  { simp only [hF] },
end

omit dec_ι

/-- A family `f` of mutually-orthogonal elements of `E` is summable, if and only if
`(λ i, ‖f i‖ ^ 2)` is summable. -/
lemma orthogonal_family.summable_iff_norm_sq_summable [complete_space E] (f : Π i, G i) :
  summable (λ i, V i (f i)) ↔ summable (λ i, ‖f i‖ ^ 2) :=
begin
  classical,
  simp only [summable_iff_cauchy_seq_finset, normed_add_comm_group.cauchy_seq_iff,
    real.norm_eq_abs],
  split,
  { intros hf ε hε,
    obtain ⟨a, H⟩ := hf _ (sqrt_pos.mpr hε),
    use a,
    intros s₁ hs₁ s₂ hs₂,
    rw ← finset.sum_sdiff_sub_sum_sdiff,
    refine (_root_.abs_sub _ _).trans_lt _,
    have : ∀ i, 0 ≤ ‖f i‖ ^ 2 := λ i : ι, sq_nonneg _,
    simp only [finset.abs_sum_of_nonneg' this],
    have : ∑ i in s₁ \ s₂, ‖f i‖ ^ 2 + ∑ i in s₂ \ s₁, ‖f i‖ ^ 2 < (sqrt ε) ^ 2,
    { rw [← hV.norm_sq_diff_sum, sq_lt_sq,
        _root_.abs_of_nonneg (sqrt_nonneg _), _root_.abs_of_nonneg (norm_nonneg _)],
      exact H s₁ hs₁ s₂ hs₂ },
    have hη := sq_sqrt (le_of_lt hε),
    linarith },
  { intros hf ε hε,
    have hε' : 0 < ε ^ 2 / 2 := half_pos (sq_pos_of_pos hε),
    obtain ⟨a, H⟩ := hf _ hε',
    use a,
    intros s₁ hs₁ s₂ hs₂,
    refine (abs_lt_of_sq_lt_sq' _ (le_of_lt hε)).2,
    have has : a ≤ s₁ ⊓ s₂ := le_inf hs₁ hs₂,
    rw hV.norm_sq_diff_sum,
    have Hs₁ : ∑ (x : ι) in s₁ \ s₂, ‖f x‖ ^ 2 < ε ^ 2 / 2,
    { convert H _ hs₁ _ has,
      have : s₁ ⊓ s₂ ⊆ s₁ := finset.inter_subset_left _ _,
      rw [← finset.sum_sdiff this, add_tsub_cancel_right, finset.abs_sum_of_nonneg'],
      { simp },
      { exact λ i, sq_nonneg _ } },
    have Hs₂ : ∑ (x : ι) in s₂ \ s₁, ‖f x‖ ^ 2 < ε ^ 2 /2,
    { convert H _ hs₂ _ has,
      have : s₁ ⊓ s₂ ⊆ s₂ := finset.inter_subset_right _ _,
      rw [← finset.sum_sdiff this, add_tsub_cancel_right, finset.abs_sum_of_nonneg'],
      { simp },
      { exact λ i, sq_nonneg _ } },
    linarith },
end

omit hV

/-- An orthogonal family forms an independent family of subspaces; that is, any collection of
elements each from a different subspace in the family is linearly independent. In particular, the
pairwise intersections of elements of the family are 0. -/
lemma orthogonal_family.independent {V : ι → submodule 𝕜 E}
  (hV : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) :
  complete_lattice.independent V :=
begin
  classical,
  apply complete_lattice.independent_of_dfinsupp_lsum_injective,
  rw [← @linear_map.ker_eq_bot _ _ _ _ _ _ (direct_sum.add_comm_group (λ i, V i)),
    submodule.eq_bot_iff],
  intros v hv,
  rw linear_map.mem_ker at hv,
  ext i,
  suffices : ⟪(v i : E), v i⟫ = 0,
  { simpa only [inner_self_eq_zero] using this },
  calc ⟪(v i : E), v i⟫ = ⟪(v i : E), dfinsupp.lsum ℕ (λ i, (V i).subtype) v⟫ :
    by simpa only [dfinsupp.sum_add_hom_apply, dfinsupp.lsum_apply_apply]
      using (hV.inner_right_dfinsupp v i (v i)).symm
  ... = 0 : by simp only [hv, inner_zero_right],
end

include dec_ι
lemma direct_sum.is_internal.collected_basis_orthonormal {V : ι → submodule 𝕜 E}
  (hV : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ))
  (hV_sum : direct_sum.is_internal (λ i, V i))
  {α : ι → Type*}
  {v_family : Π i, basis (α i) 𝕜 (V i)} (hv_family : ∀ i, orthonormal 𝕜 (v_family i)) :
  orthonormal 𝕜 (hV_sum.collected_basis v_family) :=
by simpa only [hV_sum.collected_basis_coe] using hV.orthonormal_sigma_orthonormal hv_family

end orthogonal_family

lemma submodule.orthogonal_family_self (K : submodule 𝕜 E) :
  @orthogonal_family 𝕜 E _ _ _ (λ b, ((cond b K Kᗮ : submodule 𝕜 E) : Type*)) _
  (λ b, (cond b K Kᗮ).subtypeₗᵢ)
| tt tt := absurd rfl
| tt ff := λ _ x y, submodule.inner_right_of_mem_orthogonal x.prop y.prop
| ff tt := λ _ x y, submodule.inner_left_of_mem_orthogonal y.prop x.prop
| ff ff := absurd rfl
