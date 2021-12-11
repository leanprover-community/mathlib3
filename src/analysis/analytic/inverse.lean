/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.analytic.composition

/-!

# Inverse of analytic functions

We construct the left and right inverse of a formal multilinear series with invertible linear term,
we prove that they coincide and study their properties (notably convergence).

## Main statements

* `p.left_inv i`: the formal left inverse of the formal multilinear series `p`,
  for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.right_inv i`: the formal right inverse of the formal multilinear series `p`,
  for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.left_inv_comp` says that `p.left_inv i` is indeed a left inverse to `p` when `p₁ = i`.
* `p.right_inv_comp` says that `p.right_inv i` is indeed a right inverse to `p` when `p₁ = i`.
* `p.left_inv_eq_right_inv`: the two inverses coincide.
* `p.radius_right_inv_pos_of_radius_pos`: if a power series has a positive radius of convergence,
  then so does its inverse.

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
  p.left_inv i 0 = 0 := by rw left_inv

@[simp] lemma left_inv_coeff_one (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.left_inv i 1 = (continuous_multilinear_curry_fin1 𝕜 F E).symm i.symm := by rw left_inv

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
  p.right_inv i 0 = 0 := by rw right_inv

@[simp] lemma right_inv_coeff_one (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.right_inv i 1 = (continuous_multilinear_curry_fin1 𝕜 F E).symm i.symm := by rw right_inv

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

/-!
### Convergence of the inverse of a power series

Assume that `p` is a convergent multilinear series, and let `q` be its (left or right) inverse.
Using the left-inverse formula gives
$$
q_n = - (p_1)^{-n} \sum_{k=0}^{n-1} \sum_{i_1 + \dotsc + i_k = n} q_k (p_{i_1}, \dotsc, p_{i_k}).
$$
Assume for simplicity that we are in dimension `1` and `p₁ = 1`. In the formula for `qₙ`, the term
`q_{n-1}` appears with a multiplicity of `n-1` (choosing the index `i_j` for which `i_j = 2` while
all the other indices are equal to `1`), which indicates that `qₙ` might grow like `n!`. This is
bad for summability properties.

It turns out that the right-inverse formula is better behaved, and should instead be used for this
kind of estimate. It reads
$$
q_n = - (p_1)^{-1} \sum_{k=2}^n \sum_{i_1 + \dotsc + i_k = n} p_k (q_{i_1}, \dotsc, q_{i_k}).
$$
Here, `q_{n-1}` can only appear in the term with `k = 2`, and it only appears twice, so there is
hope this formula can lead to an at most geometric behavior.

Let `Qₙ = ∥qₙ∥`. Bounding `∥pₖ∥` with `C r^k` gives an inequality
$$
Q_n ≤ C' \sum_{k=2}^n r^k \sum_{i_1 + \dotsc + i_k = n} Q_{i_1} \dotsm Q_{i_k}.
$$

This formula is not enough to prove by naive induction on `n` a bound of the form `Qₙ ≤ D R^n`.
However, assuming that the inequality above were an equality, one could get a formula for the
generating series of the `Qₙ`:

$$
\begin{align}
Q(z) & := \sum Q_n z^n = Q_1 z + C' \sum_{2 \leq k \leq n} \sum_{i_1 + \dotsc + i_k = n}
  (r z^{i_1} Q_{i_1}) \dotsm (r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (\sum_{i_1 \geq 1} r z^{i_1} Q_{i_1})
  \dotsm (\sum_{i_k \geq 1} r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (r Q(z))^k
= Q_1 z + C' (r Q(z))^2 / (1 - r Q(z)).
\end{align}
$$

One can solve this formula explicitly. The solution is analytic in a neighborhood of `0` in `ℂ`,
hence its coefficients grow at most geometrically (by a contour integral argument), and therefore
the original `Qₙ`, which are bounded by these ones, are also at most geometric.

This classical argument is not really satisfactory, as it requires an a priori bound on a complex
analytic function. Another option would be to compute explicitly its terms (with binomial
coefficients) to obtain an explicit geometric bound, but this would be very painful.

Instead, we will use the above intuition, but in a slightly different form, with finite sums and an
induction. I learnt this trick in [pöschel2017siegelsternberg]. Let
$S_n = \sum_{k=1}^n Q_k a^k$ (where `a` is a positive real parameter to be chosen suitably small).
The above computation but with finite sums shows that

$$
S_n \leq Q_1 a + C' \sum_{k=2}^n (r S_{n-1})^k.
$$

In particular, $S_n \leq Q_1 a + C' (r S_{n-1})^2 / (1- r S_{n-1})$.
Assume that $S_{n-1} \leq K a$, where `K > Q₁` is fixed and `a` is small enough so that
`r K a ≤ 1/2` (to control the denominator). Then this equation gives a bound
$S_n \leq Q_1 a + 2 C' r^2 K^2 a^2$.
If `a` is small enough, this is bounded by `K a` as the second term is quadratic in `a`, and
therefore negligible.

By induction, we deduce `Sₙ ≤ K a` for all `n`, which gives in particular the fact that `aⁿ Qₙ`
remains bounded.
-/

/-- First technical lemma to control the growth of coefficients of the inverse. Bound the explicit
expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,
in a general abstract setup. -/
lemma radius_right_inv_pos_of_radius_pos_aux1
  (n : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) :
  ∑ k in Ico 2 (n + 1), a ^ k *
      (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition k)),
          r ^ c.length * ∏ j, p (c.blocks_fun j))
  ≤ ∑ j in Ico 2 (n + 1), r ^ j * (∑ k in Ico 1 n, a ^ k * p k) ^ j :=
calc
∑ k in Ico 2 (n + 1), a ^ k *
  (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition k)),
      r ^ c.length * ∏ j, p (c.blocks_fun j))
= ∑ k in Ico 2 (n + 1),
  (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition k)),
      ∏ j, r * (a ^ (c.blocks_fun j) * p (c.blocks_fun j))) :
begin
  simp_rw [mul_sum],
  apply sum_congr rfl (λ k hk, _),
  apply sum_congr rfl (λ c hc, _),
  rw [prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, composition.sum_blocks_fun,
      prod_const, card_fin],
  ring,
end
... ≤ ∑ d in comp_partial_sum_target 2 (n + 1) n,
        ∏ (j : fin d.2.length), r * (a ^ d.2.blocks_fun j * p (d.2.blocks_fun j)) :
begin
  rw sum_sigma',
  refine sum_le_sum_of_subset_of_nonneg _ (λ x hx1 hx2,
    prod_nonneg (λ j hj, mul_nonneg hr (mul_nonneg (pow_nonneg ha _) (hp _)))),
  rintros ⟨k, c⟩ hd,
  simp only [set.mem_to_finset, mem_Ico, mem_sigma, set.mem_set_of_eq] at hd,
  simp only [mem_comp_partial_sum_target_iff],
  refine ⟨hd.2, c.length_le.trans_lt hd.1.2, λ j, _⟩,
  have : c ≠ composition.single k (zero_lt_two.trans_le hd.1.1),
    by simp [composition.eq_single_iff_length, ne_of_gt hd.2],
  rw composition.ne_single_iff at this,
  exact (this j).trans_le (nat.lt_succ_iff.mp hd.1.2)
end
... = ∑ e in comp_partial_sum_source 2 (n+1) n, ∏ (j : fin e.1), r * (a ^ e.2 j * p (e.2 j)) :
begin
  symmetry,
  apply comp_change_of_variables_sum,
  rintros ⟨k, blocks_fun⟩ H,
  have K : (comp_change_of_variables 2 (n + 1) n ⟨k, blocks_fun⟩ H).snd.length = k, by simp,
  congr' 2; try { rw K },
  rw fin.heq_fun_iff K.symm,
  assume j,
  rw comp_change_of_variables_blocks_fun,
end
... = ∑ j in Ico 2 (n+1), r ^ j * (∑ k in Ico 1 n, a ^ k * p k) ^ j :
begin
  rw [comp_partial_sum_source, ← sum_sigma' (Ico 2 (n + 1))
    (λ (k : ℕ), (fintype.pi_finset (λ (i : fin k), Ico 1 n) : finset (fin k → ℕ)))
    (λ n e, ∏ (j : fin n), r * (a ^ e j * p (e j)))],
  apply sum_congr rfl (λ j hj, _),
  simp only [← @multilinear_map.mk_pi_algebra_apply ℝ (fin j) _ _ ℝ],
  simp only [← multilinear_map.map_sum_finset (multilinear_map.mk_pi_algebra ℝ (fin j) ℝ)
    (λ k (m : ℕ), r * (a ^ m * p m))],
  simp only [multilinear_map.mk_pi_algebra_apply],
  dsimp,
  simp [prod_const, ← mul_sum, mul_pow],
end

/-- Second technical lemma to control the growth of coefficients of the inverse. Bound the explicit
expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,
in the specific setup we are interesting in, by reducing to the general bound in
`radius_right_inv_pos_of_radius_pos_aux1`. -/
lemma radius_right_inv_pos_of_radius_pos_aux2
  {n : ℕ} (hn : 2 ≤ n + 1) (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  {r a C : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (hC : 0 ≤ C) (hp : ∀ n, ∥p n∥ ≤ C * r ^ n) :
   (∑ k in Ico 1 (n + 1), a ^ k * ∥p.right_inv i k∥) ≤
     ∥(i.symm : F →L[𝕜] E)∥ * a + ∥(i.symm : F →L[𝕜] E)∥ * C * ∑ k in Ico 2 (n + 1),
      (r * ((∑ j in Ico 1 n, a ^ j * ∥p.right_inv i j∥))) ^ k :=
let I := ∥(i.symm : F →L[𝕜] E)∥ in calc
∑ k in Ico 1 (n + 1), a ^ k * ∥p.right_inv i k∥
    = a * I + ∑ k in Ico 2 (n + 1), a ^ k * ∥p.right_inv i k∥ :
by simp only [linear_isometry_equiv.norm_map, pow_one, right_inv_coeff_one,
              nat.Ico_succ_singleton, sum_singleton, ← sum_Ico_consecutive _ one_le_two hn]
... = a * I + ∑ k in Ico 2 (n + 1), a ^ k *
        ∥(i.symm : F →L[𝕜] E).comp_continuous_multilinear_map
          (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition k)),
            p.comp_along_composition (p.right_inv i) c)∥ :
begin
  congr' 1,
  apply sum_congr rfl (λ j hj, _),
  rw [right_inv_coeff _ _ _ (mem_Ico.1 hj).1, norm_neg],
end
... ≤ a * ∥(i.symm : F →L[𝕜] E)∥ + ∑ k in Ico 2 (n + 1), a ^ k * (I *
      (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition k)),
        C * r ^ c.length * ∏ j, ∥p.right_inv i (c.blocks_fun j)∥)) :
begin
  apply_rules [add_le_add, le_refl, sum_le_sum (λ j hj, _), mul_le_mul_of_nonneg_left,
    pow_nonneg, ha],
  apply (continuous_linear_map.norm_comp_continuous_multilinear_map_le _ _).trans,
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
  apply (norm_sum_le _ _).trans,
  apply sum_le_sum (λ c hc, _),
  apply (comp_along_composition_norm _ _ _).trans,
  apply mul_le_mul_of_nonneg_right (hp _),
  exact prod_nonneg (λ j hj, norm_nonneg _),
end
... = I * a + I * C * ∑ k in Ico 2 (n + 1), a ^ k *
  (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition k)),
      r ^ c.length * ∏ j, ∥p.right_inv i (c.blocks_fun j)∥) :
begin
  simp_rw [mul_assoc C, ← mul_sum, ← mul_assoc, mul_comm _ (∥↑i.symm∥), mul_assoc, ← mul_sum,
    ← mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum],
  ring,
end
... ≤ I * a + I * C * ∑ k in Ico 2 (n+1), (r * ((∑ j in Ico 1 n, a ^ j * ∥p.right_inv i j∥))) ^ k :
begin
  apply_rules [add_le_add, le_refl, mul_le_mul_of_nonneg_left, norm_nonneg, hC, mul_nonneg],
  simp_rw [mul_pow],
  apply radius_right_inv_pos_of_radius_pos_aux1 n (λ k, ∥p.right_inv i k∥)
    (λ k, norm_nonneg _) hr ha,
end

/-- If a a formal multilinear series has a positive radius of convergence, then its right inverse
also has a positive radius of convergence. -/
theorem radius_right_inv_pos_of_radius_pos (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  (hp : 0 < p.radius) : 0 < (p.right_inv i).radius :=
begin
  obtain ⟨C, r, Cpos, rpos, ple⟩ : ∃ C r (hC : 0 < C) (hr : 0 < r), ∀ (n : ℕ), ∥p n∥ ≤ C * r ^ n :=
    le_mul_pow_of_radius_pos p hp,
  let I := ∥(i.symm : F →L[𝕜] E)∥,
  -- choose `a` small enough to make sure that `∑_{k ≤ n} aᵏ Qₖ` will be controllable by
  -- induction
  obtain ⟨a, apos, ha1, ha2⟩ : ∃ a (apos : 0 < a),
    (2 * I * C * r^2 * (I + 1) ^ 2 * a ≤ 1) ∧ (r * (I + 1) * a ≤ 1/2),
  { have : tendsto (λ a, 2 * I * C * r^2 * (I + 1) ^ 2 * a) (𝓝 0)
      (𝓝 (2 * I * C * r^2 * (I + 1) ^ 2 * 0)) := tendsto_const_nhds.mul tendsto_id,
    have A : ∀ᶠ a in 𝓝 0, 2 * I * C * r^2 * (I + 1) ^ 2 * a < 1,
      by { apply (tendsto_order.1 this).2, simp [zero_lt_one] },
    have : tendsto (λ a, r * (I + 1) * a) (𝓝 0)
      (𝓝 (r * (I + 1) * 0)) := tendsto_const_nhds.mul tendsto_id,
    have B : ∀ᶠ a in 𝓝 0, r * (I + 1) * a < 1/2,
      by { apply (tendsto_order.1 this).2, simp [zero_lt_one] },
    have C : ∀ᶠ a in 𝓝[set.Ioi (0 : ℝ)] (0 : ℝ), (0 : ℝ) < a,
      by { filter_upwards [self_mem_nhds_within], exact λ a ha, ha },
    rcases (C.and ((A.and B).filter_mono inf_le_left)).exists with ⟨a, ha⟩,
    exact ⟨a, ha.1, ha.2.1.le, ha.2.2.le⟩ },
  -- check by induction that the partial sums are suitably bounded, using the choice of `a` and the
  -- inductive control from Lemma `radius_right_inv_pos_of_radius_pos_aux2`.
  let S := λ n, ∑ k in Ico 1 n, a ^ k * ∥p.right_inv i k∥,
  have IRec : ∀ n, 1 ≤ n → S n ≤ (I + 1) * a,
  { apply nat.le_induction,
    { simp only [S],
      rw [Ico_eq_empty_of_le (le_refl 1), sum_empty],
      exact mul_nonneg (add_nonneg (norm_nonneg _) zero_le_one) apos.le },
    { assume n one_le_n hn,
      have In : 2 ≤ n + 1, by linarith,
      have Snonneg : 0 ≤ S n :=
        sum_nonneg (λ x hx, mul_nonneg (pow_nonneg apos.le _) (norm_nonneg _)),
      have rSn : r * S n ≤ 1/2 := calc
        r * S n ≤ r * ((I+1) * a) : mul_le_mul_of_nonneg_left hn rpos.le
        ... ≤ 1/2 : by rwa [← mul_assoc],
      calc S (n + 1) ≤ I * a + I * C * ∑ k in Ico 2 (n + 1), (r * S n)^k :
         radius_right_inv_pos_of_radius_pos_aux2 In p i rpos.le apos.le Cpos.le ple
      ... = I * a + I * C * (((r * S n) ^ 2 - (r * S n) ^ (n + 1)) / (1 - r * S n)) :
        by { rw geom_sum_Ico' _ In, exact ne_of_lt (rSn.trans_lt (by norm_num)) }
      ... ≤ I * a + I * C * ((r * S n) ^ 2 / (1/2)) :
        begin
          apply_rules [add_le_add, le_refl, mul_le_mul_of_nonneg_left, mul_nonneg, norm_nonneg,
            Cpos.le],
          refine div_le_div (sq_nonneg _) _ (by norm_num) (by linarith),
          simp only [sub_le_self_iff],
          apply pow_nonneg (mul_nonneg rpos.le Snonneg),
        end
      ... = I * a + 2 * I * C * (r * S n) ^ 2 : by ring
      ... ≤ I * a + 2 * I * C * (r * ((I + 1) * a)) ^ 2 :
        by apply_rules [add_le_add, le_refl, mul_le_mul_of_nonneg_left, mul_nonneg, norm_nonneg,
            Cpos.le, zero_le_two, pow_le_pow_of_le_left, rpos.le]
      ... = (I + 2 * I * C * r^2 * (I + 1) ^ 2 * a) * a : by ring
      ... ≤ (I + 1) * a :
        by apply_rules [mul_le_mul_of_nonneg_right, apos.le, add_le_add, le_refl] } },
  -- conclude that all coefficients satisfy `aⁿ Qₙ ≤ (I + 1) a`.
  let a' : nnreal := ⟨a, apos.le⟩,
  suffices H : (a' : ennreal) ≤ (p.right_inv i).radius,
    by { apply lt_of_lt_of_le _ H, exact_mod_cast apos },
  apply le_radius_of_bound _ ((I + 1) * a) (λ n, _),
  by_cases hn : n = 0,
  { have : ∥p.right_inv i n∥ = ∥p.right_inv i 0∥, by congr; try { rw hn },
    simp only [this, norm_zero, zero_mul, right_inv_coeff_zero],
    apply_rules [mul_nonneg, add_nonneg, norm_nonneg, zero_le_one, apos.le] },
  { have one_le_n : 1 ≤ n := bot_lt_iff_ne_bot.2 hn,
    calc ∥p.right_inv i n∥ * ↑a' ^ n = a ^ n * ∥p.right_inv i n∥ : mul_comm _ _
    ... ≤ ∑ k in Ico 1 (n + 1), a ^ k * ∥p.right_inv i k∥ :
      begin
        have : ∀ k ∈ Ico 1 (n + 1), 0 ≤ a ^ k * ∥p.right_inv i k∥ :=
          λ k hk, mul_nonneg (pow_nonneg apos.le _) (norm_nonneg _),
        exact single_le_sum this (by simp [one_le_n]),
      end
    ... ≤ (I + 1) * a : IRec (n + 1) (by dec_trivial) }
end

end formal_multilinear_series
