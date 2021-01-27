/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.analytic.composition

/-!

# Inverse of analytic functions

We construct the left and right inverse of a formal multilinear series with invertible linear term,
and we prove that they coincide.

## Main statements

* `p.left_inv i`: the formal left inverse of the formal multilinear series `p`,
  for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.right_inv i`: the formal right inverse of the formal multilinear series `p`,
  for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.left_inv_comp` says that `p.left_inv i` is indeed a left inverse to `p` when `p₁ = i`.
* `p.right_inv_comp` says that `p.right_inv i` is indeed a right inverse to `p` when `p₁ = i`.
* `p.left_inv_eq_right_inv`: the two inverses coincide.

-/

open_locale big_operators classical topological_space
open finset filter

namespace formal_multilinear_series

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]

/-! ### The left inverse of a formal multilinear series -/

/-- The left inverse of a formal multilinear series, where the `n`-th term is defined inductively
in terms of the previous ones to make sure that `(left_inv p i) ∘ p = id`. For this, the linear term
`p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should
coincide with `p₁`, so that one can use its inverse in the construction. The definition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `q ∘ p` is `∑ qₖ (p_{j₁}, ..., p_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `qₙ (p₁, ..., p₁)`. We adjust the definition so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.

These formulas only make sense when the constant term `p₀` vanishes. The definition we give is
general, but it ignores the value of `p₀`.
-/
noncomputable def left_inv (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  formal_multilinear_series 𝕜 F E
| 0     := 0
| 1     := (continuous_multilinear_curry_fin1 𝕜 F E).symm i.symm
| (n+2) := - ∑ c : {c : composition (n+2) // c.length < n + 2},
      have (c : composition (n+2)).length < n+2 := c.2,
      (left_inv (c : composition (n+2)).length).comp_along_composition
        (p.comp_continuous_linear_map i.symm) c

@[simp] lemma left_inv_coeff_zero (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.left_inv i 0 = 0 := rfl

@[simp] lemma left_inv_coeff_one (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.left_inv i 1 = (continuous_multilinear_curry_fin1 𝕜 F E).symm i.symm := rfl

/-- The left inverse does not depend on the zeroth coefficient of a formal multilinear
series. -/
lemma left_inv_remove_zero (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.remove_zero.left_inv i = p.left_inv i :=
begin
  ext1 n,
  induction n using nat.strong_rec' with n IH,
  cases n, { simp }, -- if one replaces `simp` with `refl`, the proof times out in the kernel.
  cases n, { simp }, -- TODO: why?
  simp only [left_inv, neg_inj],
  refine finset.sum_congr rfl (λ c cuniv, _),
  rcases c with ⟨c, hc⟩,
  ext v,
  dsimp,
  simp [IH _ hc],
end

/-- The left inverse to a formal multilinear series is indeed a left inverse, provided its linear
term is invertible. -/
lemma left_inv_comp (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  (h : p 1 = (continuous_multilinear_curry_fin1 𝕜 E F).symm i) :
  (left_inv p i).comp p = id 𝕜 E :=
begin
  ext n v,
  cases n,
  { simp only [left_inv, continuous_multilinear_map.zero_apply, id_apply_ne_one, ne.def,
      not_false_iff, zero_ne_one, comp_coeff_zero']},
  cases n,
  { simp only [left_inv, comp_coeff_one, h, id_apply_one, continuous_linear_equiv.coe_apply,
      continuous_linear_equiv.symm_apply_apply, continuous_multilinear_curry_fin1_symm_apply] },
  have A : (finset.univ : finset (composition (n+2)))
    = {c | composition.length c < n + 2}.to_finset ∪ {composition.ones (n+2)},
  { refine subset.antisymm (λ c hc, _) (subset_univ _),
    by_cases h : c.length < n + 2,
    { simp [h] },
    { simp [composition.eq_ones_iff_le_length.2 (not_lt.1 h)] } },
  have B : disjoint ({c | composition.length c < n + 2} : set (composition (n + 2))).to_finset
    {composition.ones (n+2)}, by simp,
  have C : (p.left_inv i (composition.ones (n + 2)).length)
    (λ (j : fin (composition.ones n.succ.succ).length), p 1 (λ k,
      v ((fin.cast_le (composition.length_le _)) j)))
    = p.left_inv i (n+2) (λ (j : fin (n+2)), p 1 (λ k, v j)),
  { apply formal_multilinear_series.congr _ (composition.ones_length _) (λ j hj1 hj2, _),
    exact formal_multilinear_series.congr _ rfl (λ k hk1 hk2, by congr) },
  have D : p.left_inv i (n+2) (λ (j : fin (n+2)), p 1 (λ k, v j)) =
    - ∑ (c : composition (n + 2)) in {c : composition (n + 2) | c.length < n + 2}.to_finset,
        (p.left_inv i c.length) (p.apply_composition c v),
  { simp only [left_inv, continuous_multilinear_map.neg_apply, neg_inj,
      continuous_multilinear_map.sum_apply],
    convert (sum_to_finset_eq_subtype (λ (c : composition (n+2)), c.length < n+2)
      (λ (c : composition (n+2)), (continuous_multilinear_map.comp_along_composition
        (p.comp_continuous_linear_map ↑(i.symm)) c (p.left_inv i c.length))
          (λ (j : fin (n + 2)), p 1 (λ (k : fin 1), v j)))).symm.trans _,
    simp only [comp_continuous_linear_map_apply_composition,
      continuous_multilinear_map.comp_along_composition_apply],
    congr,
    ext c,
    congr,
    ext k,
    simp [h] },
  simp [formal_multilinear_series.comp, show n + 2 ≠ 1, by dec_trivial, A, finset.sum_union B,
    apply_composition_ones, C, D],
end

/-! ### The right inverse of a formal multilinear series -/

/-- The right inverse of a formal multilinear series, where the `n`-th term is defined inductively
in terms of the previous ones to make sure that `p ∘ (right_inv p i) = id`. For this, the linear
term `p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should
coincide with `p₁`, so that one can use its inverse in the construction. The definition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `p ∘ q` is `∑ pₖ (q_{j₁}, ..., q_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `p₁ (qₙ)`. We adjust the definition of `qₙ` so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.

These formulas only make sense when the constant term `p₀` vanishes. The definition we give is
general, but it ignores the value of `p₀`.
-/
noncomputable def right_inv (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  formal_multilinear_series 𝕜 F E
| 0     := 0
| 1     := (continuous_multilinear_curry_fin1 𝕜 F E).symm i.symm
| (n+2) :=
    let q : formal_multilinear_series 𝕜 F E := λ k, if h : k < n + 2 then right_inv k else 0 in
    - (i.symm : F →L[𝕜] E).comp_continuous_multilinear_map ((p.comp q) (n+2))

@[simp] lemma right_inv_coeff_zero (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.right_inv i 0 = 0 := rfl

@[simp] lemma right_inv_coeff_one (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.right_inv i 1 = (continuous_multilinear_curry_fin1 𝕜 F E).symm i.symm := rfl

/-- The right inverse does not depend on the zeroth coefficient of a formal multilinear
series. -/
lemma right_inv_remove_zero (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.remove_zero.right_inv i = p.right_inv i :=
begin
  ext1 n,
  induction n using nat.strong_rec' with n IH,
  cases n, { simp },
  cases n, { simp },
  simp only [right_inv, neg_inj],
  unfold_coes,
  congr' 1,
  rw remove_zero_comp_of_pos _ _ (show 0 < n+2, by dec_trivial),
  congr' 1,
  ext k,
  by_cases hk : k < n+2; simp [hk, IH]
end

lemma comp_right_inv_aux1 {n : ℕ} (hn : 0 < n)
  (p : formal_multilinear_series 𝕜 E F) (q : formal_multilinear_series 𝕜 F E) (v : fin n → F) :
  p.comp q n v =
    (∑ (c : composition n) in {c : composition n | 1 < c.length}.to_finset,
      p c.length (q.apply_composition c v)) + p 1 (λ i, q n v) :=
begin
  have A : (finset.univ : finset (composition n))
    = {c | 1 < composition.length c}.to_finset ∪ {composition.single n hn},
  { refine subset.antisymm (λ c hc, _) (subset_univ _),
    by_cases h : 1 < c.length,
    { simp [h] },
    { have : c.length = 1,
        by { refine (eq_iff_le_not_lt.2 ⟨ _, h⟩).symm, exact c.length_pos_of_pos hn },
      rw ← composition.eq_single_iff_length hn at this,
      simp [this] } },
  have B : disjoint ({c | 1 < composition.length c} : set (composition n)).to_finset
    {composition.single n hn}, by simp,
  have C : p (composition.single n hn).length
              (q.apply_composition (composition.single n hn) v)
            = p 1 (λ (i : fin 1), q n v),
  { apply p.congr (composition.single_length hn) (λ j hj1 hj2, _),
    simp [apply_composition_single] },
  simp [formal_multilinear_series.comp, A, finset.sum_union B, C],
end

lemma comp_right_inv_aux2
  (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) (n : ℕ) (v : fin (n + 2) → F) :
  ∑ (c : composition (n + 2)) in {c : composition (n + 2) | 1 < c.length}.to_finset,
    p c.length (apply_composition (λ (k : ℕ), ite (k < n + 2) (p.right_inv i k) 0) c v) =
  ∑ (c : composition (n + 2)) in {c : composition (n + 2) | 1 < c.length}.to_finset,
    p c.length ((p.right_inv i).apply_composition c v) :=
begin
  have N : 0 < n + 2, by dec_trivial,
  refine sum_congr rfl (λ c hc, p.congr rfl (λ j hj1 hj2, _)),
  have : ∀ k, c.blocks_fun k < n + 2,
  { simp only [set.mem_to_finset, set.mem_set_of_eq] at hc,
    simp [← composition.ne_single_iff N, composition.eq_single_iff_length, ne_of_gt hc] },
  simp [apply_composition, this],
end

/-- The right inverse to a formal multilinear series is indeed a right inverse, provided its linear
term is invertible and its constant term vanishes. -/
lemma comp_right_inv (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  (h : p 1 = (continuous_multilinear_curry_fin1 𝕜 E F).symm i) (h0 : p 0 = 0) :
  p.comp (right_inv p i) = id 𝕜 F :=
begin
  ext n v,
  cases n,
  { simp only [h0, continuous_multilinear_map.zero_apply, id_apply_ne_one, ne.def, not_false_iff,
      zero_ne_one, comp_coeff_zero']},
  cases n,
  { simp only [comp_coeff_one, h, right_inv, continuous_linear_equiv.apply_symm_apply, id_apply_one,
      continuous_linear_equiv.coe_apply, continuous_multilinear_curry_fin1_symm_apply] },
  have N : 0 < n+2, by dec_trivial,
  simp [comp_right_inv_aux1 N, h, right_inv, lt_irrefl n, show n + 2 ≠ 1, by dec_trivial,
        ← sub_eq_add_neg, sub_eq_zero, comp_right_inv_aux2],
end

lemma right_inv_coeff (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) (n : ℕ) (hn : 2 ≤ n) :
  p.right_inv i n = - (i.symm : F →L[𝕜] E).comp_continuous_multilinear_map
    (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition n)),
      p.comp_along_composition (p.right_inv i) c) :=
begin
  cases n, { exact false.elim (zero_lt_two.not_le hn) },
  cases n, { exact false.elim (one_lt_two.not_le hn) },
  simp only [right_inv, neg_inj],
  congr' 1,
  ext v,
  have N : 0 < n + 2, by dec_trivial,
  have : (p 1) (λ (i : fin 1), 0) = 0 := continuous_multilinear_map.map_zero _,
  simp [comp_right_inv_aux1 N, lt_irrefl n, this, comp_right_inv_aux2]
end

/-! ### Coincidence of the left and the right inverse -/

private lemma left_inv_eq_right_inv_aux (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  (h : p 1 = (continuous_multilinear_curry_fin1 𝕜 E F).symm i) (h0 : p 0 = 0) :
  left_inv p i = right_inv p i := calc
left_inv p i = (left_inv p i).comp (id 𝕜 F) : by simp
... = (left_inv p i).comp (p.comp (right_inv p i)) : by rw comp_right_inv p i h h0
... = ((left_inv p i).comp p).comp (right_inv p i) : by rw comp_assoc
... = (id 𝕜 E).comp (right_inv p i) : by rw left_inv_comp p i h
... = right_inv p i : by simp

/-- The left inverse and the right inverse of a formal multilinear series coincide. This is not at
all obvious from their definition, but it follows from uniqueness of inverses (which comes from the
fact that composition is associative on formal multilinear series). -/
theorem left_inv_eq_right_inv (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  (h : p 1 = (continuous_multilinear_curry_fin1 𝕜 E F).symm i) :
  left_inv p i = right_inv p i := calc
left_inv p i = left_inv p.remove_zero i : by rw left_inv_remove_zero
... = right_inv p.remove_zero i : by { apply left_inv_eq_right_inv_aux; simp [h] }
... = right_inv p i : by rw right_inv_remove_zero

end formal_multilinear_series
