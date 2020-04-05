
/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.analytic.basic combinatorics.ordered_partition

/-!
# Composition of analytic functions

in this file we prove that the composition of analytic functions is analytic.

The argument is the following. Assume `g z = ∑ qₙ (z, ..., z)` and `f y = ∑ pₖ (y, ..., y)`. Then

`g (f y) = ∑ qₙ (∑ pₖ (y, ..., y), ..., ∑ pₖ (y, ..., y))
= ∑ qₙ (p_{i₁} (y, ..., y), ..., p_{iₙ} (y, ..., y))`.

For each `n` and `i₁, ..., iₙ`, define a `i₁ + ... + iₙ` multilinear function mapping
`(y₀, ..., y_{i₁ + ... + iₙ - 1})` to
`qₙ (p_{i₁} (y₀, ..., y_{i₁-1}), p_{i₂} (y_{i₁}, ..., y_{i₁ + i₂ - 1}, ..., p_{iₙ} (....)))`.
Then `g ∘ f` is obtained by summing all these multilinear functions.

To formalize this, we use ordered partitions of an integer `N`, as all its decompositions into
a sum `i₁ + ... + iₙ` of positive integers. Given such an ordered partition `op` and two formal
multilinear series `q` and `p`, let `q.comp_along_ordered_partition p op` be the above multilinear
function. Then the `N`-th coefficient in the power series expansion of `g ∘ f` is the sum of these
terms over all `op : ordered_partition N`.

To complete the proof, we need to show that this power series has a positive radius of convergence.
This follows from the fact that `ordered_partition N` has cardinality `2^(N-1)` and estimates on
the norm of `qₙ` and `pₖ`, which give summability. We also need to show that it indeed converges to
`g ∘ f`. For this, we note that the composition of partial sums converges to `g ∘ f`, and that it
corresponds to a part of the whole sum, on a subset that increases to the whole space. By
summability of the norms, this implies the overall convergence.

## Main results

* `q.comp p` is the formal composition of the formal multilinear series `q` and `p`.
* `has_fpower_series_at.comp` states that if two functions `g` and `f` admit power series expansions
  `q` and `p`, then `g ∘ f` admits a power series expansion given by `q.comp p`.
* `analytic_at.comp` states that the composition of analytic functions is analytic.

## Implementation details

The main technical difficulty is to write down things. In particular, we need to define precisely
`q.comp_along_ordered_partition p op` and to show that it is indeed a continuous multilinear
function. This requires a whole interface built on the class `ordered_partition`. Once this is set,
the main difficulty is to reorder the sums, writing the composition of the partial sums as a sum
over some subset of `Σ n, ordered_partition n`. We need to check that the reordering is a bijection,
running over difficulties due to the dependent nature of the types under consideration, that are
controlled thanks to the interface for `ordered_partition`.
-/

noncomputable theory

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]

open filter
open_locale topological_space classical

/-! ### Composing formal multilinear series -/

namespace formal_multilinear_series

/-- Given a formal multilinear series `p`, an ordered partition `op` of `n` and the index `i` of a
block of `op`, we may define a function on `fin n → E` by picking the variables in the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. This function is
called `p.apply_ordered_partition op v i` for `v : fin n → E` and `i : fin op.max_index`. -/
def apply_ordered_partition
  (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (op : ordered_partition n) :
  (fin n → E) → (fin (op.max_index) → F) :=
λ v i, p (op.size i) (v ∘ (op.embedding i))

/-- Technical lemma stating how `p.apply_ordered_partition` commutes with updating variables. This
will be the key point to show that functions constructed from `apply_ordered_partition` retain
multilinearity. -/
lemma apply_ordered_partition_update
  (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (op : ordered_partition n)
  (j : fin n) (v : fin n → E) (z : E) :
  p.apply_ordered_partition op (function.update v j z)
  = function.update (p.apply_ordered_partition op v) (op.index j)
    (p (op.size (op.index j))
  (function.update (v ∘ (op.embedding (op.index j))) (op.inv_embedding j) z)) :=
begin
  ext k,
  by_cases h : k = op.index j,
  { rw h,
    let r : fin (op.size (op.index j)) → fin n := op.embedding (op.index j),
    simp only [function.update_same],
    change p (op.size (op.index j)) ((function.update v j z) ∘ r) = _,
    let j' := op.inv_embedding j,
    suffices B : (function.update v j z) ∘ r = function.update (v ∘ r) j' z,
      by rw B,
    suffices C : (function.update v (r j') z) ∘ r = function.update (v ∘ r) j' z,
      by { convert C, exact op.embedding_comp_inv j },
    exact function.update_comp_eq_of_injective _ (op.embedding_inj _) _ _ },
  { simp only [h, function.update_eq_self, function.update_noteq, ne.def, not_false_iff],
    let r : fin (op.size k) → fin n := op.embedding k,
    change p (op.size k) ((function.update v j z) ∘ r) = p (op.size k) (v ∘ r),
    suffices B : (function.update v j z) ∘ r = v ∘ r, by rw B,
    apply function.update_comp_eq_of_not_mem_range,
    rwa op.mem_range_embedding_iff' }
end

/-- Given two formal multilinear series `q` and `p` and an ordered partition `op` of `n`, one may
form a multilinear map in `n` variables by applying the right coefficient of `p` to each block of
the ordered partition, and then applying `q op.max_index` to the resulting vector. It is called
`q.comp_along_ordered_partition_multilinear p op`. This function admits a version as a continuous
multilinear map, called `q.comp_along_ordered_partition p op` below. -/
def comp_along_ordered_partition_multilinear {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (op : ordered_partition n) : multilinear_map 𝕜 (λ i : fin n, E) G :=
{ to_fun := λ v, q op.max_index (p.apply_ordered_partition op v),
  add    := λ v i x y, by simp [apply_ordered_partition_update],
  smul   := λ v i c x, by simp [apply_ordered_partition_update] }

/-- The norm of `q.comp_along_ordered_partition_multilinear p op` is controlled by the product of
the norms of the relevant bits of `q` and `p`. -/
lemma comp_along_ordered_partition_multilinear_bound {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (op : ordered_partition n) (v : fin n → E) :
  ∥q.comp_along_ordered_partition_multilinear p op v∥
  ≤ ∥q op.max_index∥ * finset.univ.prod (λ i, ∥p (op.size i)∥)
    * (finset.univ : finset (fin n)).prod (λ i, ∥v i∥) :=
begin
  -- main point: taking the product of the `∥v i∥` along each block, and then along all the blocks,
  -- gives the product of all the `∥v i∥`, as the blocks form a partition of the indices.
  have A : finset.univ.prod (λ (i : fin op.max_index),
    finset.univ.prod (λ (j : fin (op.size i)), ∥(v ∘ op.embedding i) j∥)) =
    finset.prod finset.univ (λ (i : fin n), ∥v i∥),
  { -- The fact that a product over a partition gives the whole product is `finset.prod_bind`.
    -- We just need to check its disjointness and totality assumptions.
    have : (∀ (i : fin op.max_index), i ∈ finset.univ → ∀ (j : fin op.max_index), j ∈ finset.univ →
       i ≠ j → disjoint (finset.univ.image (op.embedding i)) (finset.univ.image (op.embedding j))),
    { assume i hi j hj i_ne_j,
      rw finset.disjoint_iff_disjoint_coe,
      convert op.disjoint_range i_ne_j;
      apply fintype.coe_image_univ },
    have Z := @finset.prod_bind _ _ _ (λ j, ∥v j∥) _ _ finset.univ
      (λ (i : fin op.max_index), finset.univ.image (op.embedding i)) this,
    have : (finset.bind finset.univ (λ (i : fin op.max_index), finset.univ.image (op.embedding i)))
      = finset.univ,
    { ext j,
      simp only [finset.mem_univ, finset.mem_bind, iff_true, exists_prop_of_true, finset.mem_image],
      refine ⟨op.index j, by simpa using op.mem_range_embedding j⟩ },
    rw this at Z,
    rw Z,
    congr,
    ext i,
    rw finset.prod_image,
    assume a ha b hb hab,
    exact op.embedding_inj i hab },
  -- Now that the main point is proved, write down the estimates using the definition of the norm
  -- of a multilinear map
  calc ∥q.comp_along_ordered_partition_multilinear p op v∥
  = ∥q op.max_index (p.apply_ordered_partition op v)∥ : rfl
  ... ≤ ∥q op.max_index∥ * finset.univ.prod (λ i, ∥p.apply_ordered_partition op v i∥) :
    continuous_multilinear_map.le_op_norm _ _
  ... ≤ ∥q op.max_index∥ * finset.univ.prod (λ i, ∥p (op.size i)∥ *
     (finset.univ : finset (fin (op.size i))).prod (λ j, ∥(v ∘ (op.embedding i)) j∥)) :
    begin
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
      refine finset.prod_le_prod (λ i hi, norm_nonneg _) (λ i hi, _),
      apply continuous_multilinear_map.le_op_norm,
    end
  ... = ∥q op.max_index∥ * finset.univ.prod (λ i, ∥p (op.size i)∥) * finset.univ.prod (λ i,
     (finset.univ : finset (fin (op.size i))).prod (λ j, ∥(v ∘ (op.embedding i)) j∥)) :
    by rw [finset.prod_mul_distrib, mul_assoc]
  ... = ∥q op.max_index∥ * finset.univ.prod (λ i, ∥p (op.size i)∥)
    * (finset.univ : finset (fin n)).prod (λ i, ∥v i∥) : by rw A
end

/-- Given two formal multilinear series `q` and `p` and an ordered partition `op` of `n`, one may
form a continuous multilinear map in `n` variables by applying the right coefficient of `p` to each
block of the ordered partition, and then applying `q op.max_index` to the resulting vector. It is
called `q.comp_along_ordered_partition p op`. It is constructed from the analogous multilinear
function `q.comp_along_ordered_partition_multilinear p op`, together with a norm control to get
the continuity. -/
def comp_along_ordered_partition {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (op : ordered_partition n) : continuous_multilinear_map 𝕜 (λ i : fin n, E) G :=
(q.comp_along_ordered_partition_multilinear p op).mk_continuous _
  (q.comp_along_ordered_partition_multilinear_bound p op)

/-- The norm of `q.comp_along_ordered_partition p op` is controlled by the product of
the norms of the relevant bits of `q` and `p`. -/
lemma comp_along_ordered_partition_norm {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (op : ordered_partition n) :
  ∥q.comp_along_ordered_partition p op∥ ≤
  ∥q op.max_index∥ * finset.univ.prod (λ i, ∥p (op.size i)∥) :=
multilinear_map.mk_continuous_norm_le _
  (mul_nonneg (norm_nonneg _) (finset.prod_nonneg (λ i hi, norm_nonneg _))) _

lemma comp_along_ordered_partition_nnnorm {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (op : ordered_partition n) :
  nnnorm (q.comp_along_ordered_partition p op) ≤
  nnnorm (q op.max_index) * finset.univ.prod (λ i, nnnorm (p (op.size i))) :=
begin
  simp only [← nnreal.coe_le_coe, coe_nnnorm, nnreal.coe_mul, coe_nnnorm, nnreal.coe_prod, coe_nnnorm],
  exact q.comp_along_ordered_partition_norm p op
end

/-- Formal composition of two formal multilinear series. The `n`-th coefficient in the composition
is defined to be the sum of `q.comp_along_ordered_partition p op` over all ordered partitions of
`n`. In other words, this term (as a multilinear function applied to `v_0, ..., v_{n-1}`) is
`∑_{k} ∑_{i₁ + ... + iₖ = n} pₖ (q_{i_1} (...), ..., q_{i_k} (...))`, where one puts all variables
`v_0, ..., v_{n-1}` in increasing order in the dots.-/
protected def comp (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F) :
  formal_multilinear_series 𝕜 E G :=
λ n, (finset.univ : finset (ordered_partition n)).sum (λ op, q.comp_along_ordered_partition p op)

/-- If two formal multilinear series have positive radius of convergence, then the terms appearing
in the definition of their composition are also summable (when multiplied by a suitable positive
geometric term). -/
theorem comp_summable_nnreal
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (hq : 0 < q.radius) (hp : 0 < p.radius) :
  ∃ (r : nnreal), 0 < r ∧ summable (λ i, nnnorm (q.comp_along_ordered_partition p i.2) * r ^ i.1 :
    (Σ n, ordered_partition n) → nnreal) :=
begin
  /- This follows from the fact that the growth rate of `∥qₙ∥` and `∥pₙ∥` is at most geometric,
  giving a geometric bound on each `∥q.comp_along_ordered_partition p op∥`, together with the
  fact that there are `2^(n-1)` ordered partitions of `n`, giving at most a geometric loss. -/
  rcases ennreal.lt_iff_exists_nnreal_btwn.1 hq with ⟨rq, rq_pos, hrq⟩,
  rcases ennreal.lt_iff_exists_nnreal_btwn.1 hp with ⟨rp, rp_pos, hrp⟩,
  obtain ⟨Cq, hCq⟩ : ∃ (Cq : nnreal), ∀ n, nnnorm (q n) * rq^n ≤ Cq := q.bound_of_lt_radius hrq,
  obtain ⟨Cp, hCp⟩ : ∃ (Cp : nnreal), ∀ n, nnnorm (p n) * rp^n ≤ Cp := p.bound_of_lt_radius hrp,
  let r0 : nnreal := (4 * max Cp 1)⁻¹,
  set r := min rp 1 * min rq 1 * r0,
  have r_pos : 0 < r,
  { apply mul_pos' (mul_pos' _ _),
    { rw [nnreal.inv_pos],
      apply mul_pos',
      { norm_num },
      { exact lt_of_lt_of_le zero_lt_one (le_max_right _ _) } },
    { rw ennreal.coe_pos at rp_pos, simp [rp_pos, zero_lt_one] },
    { rw ennreal.coe_pos at rq_pos, simp [rq_pos, zero_lt_one] } },
  let a : ennreal := ((4 : nnreal) ⁻¹ : nnreal),
  have two_a : 2 * a < 1,
  { change ((2 : nnreal) : ennreal) * ((4 : nnreal) ⁻¹ : nnreal) < (1 : nnreal),
    rw [← ennreal.coe_mul, ennreal.coe_lt_coe, ← nnreal.coe_lt_coe, nnreal.coe_mul],
    change (2 : ℝ) * (4 : ℝ)⁻¹ < 1,
    norm_num },
  have I : ∀ (i : Σ (n : ℕ), ordered_partition n),
    ↑(nnnorm (q.comp_along_ordered_partition p i.2) * r ^ i.1) ≤ (Cq : ennreal) * a ^ i.1,
  { rintros ⟨n, op⟩,
    rw [← ennreal.coe_pow, ← ennreal.coe_mul, ennreal.coe_le_coe],
    calc nnnorm (q.comp_along_ordered_partition p op) * r ^ n
    ≤ (nnnorm (q op.max_index) *
        (finset.univ : finset (fin (op.max_index))).prod (λ i, nnnorm (p (op.size i)))) * r ^ n :
      mul_le_mul_of_nonneg_right (q.comp_along_ordered_partition_nnnorm p op) (bot_le)
    ... = (nnnorm (q op.max_index) * (min rq 1)^n) *
      ((finset.univ : finset (fin (op.max_index))).prod (λ i, nnnorm (p (op.size i))) * (min rp 1) ^ n)
      * r0 ^ n : by { dsimp [r], ring_exp }
    ... ≤ (nnnorm (q op.max_index) * (min rq 1) ^ op.max_index) *
      ((finset.univ : finset (fin op.max_index)).prod
        (λ i, nnnorm (p (op.size i)) * (min rp 1) ^ (op.size i))) * r0 ^ n :
      begin
        apply_rules [mul_le_mul, bot_le, le_refl, pow_le_pow_of_le_one, min_le_right, op.max_index_le],
        apply le_of_eq,
        rw finset.prod_mul_distrib,
        congr' 1,
        conv_lhs { rw [← op.sum_size, ← finset.prod_pow_eq_pow_sum] },
      end
    ... ≤ Cq * ((finset.univ : finset (fin op.max_index)).prod (λ i, Cp)) * r0 ^ n :
      begin
        apply_rules [mul_le_mul, bot_le, le_trans _ (hCq op.max_index), le_refl, finset.prod_le_prod'],
        { assume i hi,
          refine le_trans (mul_le_mul (le_refl _) _ bot_le bot_le) (hCp (op.size i)),
          exact pow_le_pow_of_le_left bot_le (min_le_left _ _) _ },
        { refine mul_le_mul (le_refl _) _ bot_le bot_le,
          exact pow_le_pow_of_le_left bot_le (min_le_left _ _) _ }
      end
    ... ≤ Cq * (max Cp 1) ^ n * r0 ^ n :
      begin
        apply_rules [mul_le_mul, bot_le, le_refl],
        simp only [finset.card_fin, finset.prod_const],
        refine le_trans (pow_le_pow_of_le_left bot_le (le_max_left Cp 1) op.max_index) _,
        apply pow_le_pow (le_max_right Cp 1) op.max_index_le,
      end
    ... = Cq * 4⁻¹ ^ n :
      begin
        dsimp [r0],
        have A : (4 : nnreal) ≠ 0, by norm_num,
        have B : max Cp 1 ≠ 0 :=
          ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right Cp 1)),
        field_simp [A, B],
        ring_exp
      end },
  refine ⟨r, r_pos, _⟩,
  rw [← ennreal.tsum_coe_ne_top_iff_summable],
  apply ne_of_lt,
  calc (∑ (i : Σ (n : ℕ), ordered_partition n), ↑(nnnorm (q.comp_along_ordered_partition p i.2) * r ^ i.1))
  ≤ (∑ (i : Σ (n : ℕ), ordered_partition n), (Cq : ennreal) * a ^ i.1) : ennreal.tsum_le_tsum I
  ... = (∑ (n : ℕ), (∑ (op : ordered_partition n), (Cq : ennreal) * a ^ n)) : ennreal.tsum_sigma' _
  ... = (∑ (n : ℕ), ↑(fintype.card (ordered_partition n)) * (Cq : ennreal) * a ^ n) :
    begin
      congr' 1,
      ext1 n,
      rw [tsum_fintype, finset.sum_const, add_monoid.smul_eq_mul, finset.card_univ, mul_assoc]
    end
  ... ≤ (∑ (n : ℕ), (2 : ennreal) ^ n * (Cq : ennreal) * a ^ n) :
    begin
      apply ennreal.tsum_le_tsum (λ n, _),
      apply ennreal.mul_le_mul (ennreal.mul_le_mul _ (le_refl _)) (le_refl _),
      rw ordered_partition_card,
      simp only [nat.cast_bit0, nat.cast_one, nat.cast_pow],
      apply ennreal.pow_le_pow _ (nat.sub_le n 1),
      have : (1 : nnreal) ≤ (2 : nnreal), by norm_num,
      rw ← ennreal.coe_le_coe at this,
      exact this
    end
  ... = (∑ (n : ℕ), (Cq : ennreal) * (2 * a) ^ n) : by { congr' 1, ext1 n, rw mul_pow, ring }
  ... = (Cq : ennreal) * (1 - 2 * a) ⁻¹ : by rw [ennreal.tsum_mul_left, ennreal.tsum_geometric]
  ... < ⊤ : by simp [lt_top_iff_ne_top, ennreal.mul_eq_top, two_a]
end

/-- Bounding below the radius of the composition of two formal multilinear series assuming
summability over all ordered partitions. -/
theorem le_comp_radius_of_summable
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F) (r : nnreal)
  (hr : summable (λ i, nnnorm (q.comp_along_ordered_partition p i.2) * r ^ i.1 :
    (Σ n, ordered_partition n) → nnreal)) :
  (r : ennreal) ≤ (q.comp p).radius :=
begin
apply le_radius_of_bound _ (tsum (λ (i : Σ (n : ℕ), ordered_partition n),
    (nnnorm (comp_along_ordered_partition q p i.snd) * r ^ i.fst))),
  assume n,
  calc nnnorm (formal_multilinear_series.comp q p n) * r ^ n ≤
  ∑ (op : ordered_partition n), nnnorm (comp_along_ordered_partition q p op) * r ^ n :
    begin
      rw [tsum_fintype, ← finset.sum_mul],
      exact mul_le_mul_of_nonneg_right (nnnorm_sum_le _ _) bot_le
    end
  ... ≤ ∑ (i : Σ (n : ℕ), ordered_partition n),
          nnnorm (comp_along_ordered_partition q p i.snd) * r ^ i.fst :
    begin
      let f : ordered_partition n → (Σ (n : ℕ), ordered_partition n) := λ op, ⟨n, op⟩,
      have : function.injective f, by tidy,
      convert nnreal.tsum_comp_le_tsum_of_inj hr this
    end
end

/-- Auxiliary set appearing when composing the partial sums of two multilinear series. -/
def comp_partial_sum_set (N : ℕ) : finset (Σ n, ordered_partition n) :=
@set.finite.to_finset (Σ n, ordered_partition n)
  {i | (i.2.max_index < N) ∧ (∀ (j : fin i.2.max_index), i.2.size j < N)}
begin
  let A : (Σ k, fin k → ℕ) → (Σ n, ordered_partition n) := λ i, ⟨_, ordered_partition.of_size i.2⟩,
  have : ({i | (i.2.max_index < N) ∧ (∀ (j : fin i.2.max_index), i.2.size j < N)} :
      set (Σ n, ordered_partition n))
    ⊆ A '' (↑(finset.sigma (finset.range N)
              (λ (n : ℕ), fintype.pi_finset (λ (i : fin n), finset.Ico 1 N) : _))),
  { rintros ⟨n, op⟩ h,
    have : ∀ (a : fin op.max_index), 1 ≤ op.size a := λ a, op.size_pos a,
    exact ⟨⟨_, op.size⟩, by tidy, op.of_size_eq_self.symm⟩ },
  exact set.finite_subset (set.finite_image _ (finset.finite_to_set _)) this
end

@[simp] lemma mem_comp_partial_sum_set_iff {N : ℕ} {a : Σ n, ordered_partition n} :
  a ∈ comp_partial_sum_set N ↔ a.2.max_index < N ∧ (∀ (j : fin a.2.max_index), a.2.size j < N) :=
by simp [comp_partial_sum_set]

/-- The auxiliary set corresponding to the composition of partial sums asymptotically contains
all possible ordered partitions. -/
lemma comp_partial_sum_set_tendsto_at_top :
  tendsto comp_partial_sum_set at_top at_top :=
begin
  apply monotone.tendsto_at_top_finset,
  { assume m n hmn a ha,
    have : ∀ i, i < m → i < n := λ i hi, lt_of_lt_of_le hi hmn,
    tidy },
  { rintros ⟨n, op⟩,
    simp only [mem_comp_partial_sum_set_iff],
    have : bdd_above ↑(finset.univ.image (λ (i : fin op.max_index), op.size i)) :=
      finset.bdd_above _,
    rcases this with ⟨n, hn⟩,
    refine ⟨max n op.max_index + 1, lt_of_le_of_lt (le_max_right n op.max_index) (lt_add_one _),
      λ j, lt_of_le_of_lt (le_trans _ (le_max_left _ _)) (lt_add_one _)⟩,
    apply hn,
    simp only [finset.mem_image_of_mem, finset.mem_coe, finset.mem_univ] }
end

/-- Composing the partial sums of two multilinear series coincides with the sum over all ordered
partitions in `comp_partial_sum_set N`. This is precisely the motivation for the definition of
`comp_partial_sum_set N`. -/
lemma comp_partial_sum
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F) (N : ℕ) (z : E) :
  q.partial_sum N ((finset.Ico 1 N).sum (λ a, p a (λ b, z)))
    = (comp_partial_sum_set N).sum (λ i, q.comp_along_ordered_partition_multilinear p i.2 (λ j, z)) :=
begin
  -- we expand the composition, using the multilinearity of `q` to expand along each coordinate.
  suffices H : (finset.range N).sum
    (λ (n : ℕ), (fintype.pi_finset (λ (i : fin n), finset.Ico 1 N)).sum
          (λ (r : fin n → ℕ), q n (λ (i : fin n), p (r i) (λ (i : fin (r i)), z)))) =
  (comp_partial_sum_set N).sum (λ i, q.comp_along_ordered_partition_multilinear p i.2 (λ j, z)),
    by simpa only [formal_multilinear_series.partial_sum,
                   continuous_multilinear_map.map_sum_finset] using H,
  -- rewrite the first sum as a big sum over a sigma type
  rw ← @finset.sum_sigma _ _ _ _
    (finset.range N) (λ (n : ℕ), (fintype.pi_finset (λ (i : fin n), finset.Ico 1 N)) : _)
    (λ i, q i.1 (λ (j : fin i.1), p (i.2 j) (λ (k : fin (i.2 j)), z))),
  -- show that the two sums correspond to each other by reindexing the variables. This is the
  -- content of `finset.sum_bij`, for which we spell out all parameters of the bijection
  -- explicitly as the setting is complicated.
  apply @finset.sum_bij _ _ _ _
    (finset.sigma (finset.range N) (λ (n : ℕ), fintype.pi_finset (λ (i : fin n), finset.Ico 1 N) : _))
    (comp_partial_sum_set N)
    (λ i, q i.1 (λ (j : fin i.1), p (i.2 j) (λ (k : fin (i.2 j)), z)))
    (λ i, q.comp_along_ordered_partition_multilinear p i.2 (λ j, z))
    (λ i hi, ⟨_, ordered_partition.of_size i.2⟩),
  -- To conclude, we should show that the correspondance we have set up is indeed a bijection
  -- between the index sets of the two sums.
  -- 1 - show that the image belongs to `comp_partial_sum_set N`
  { rintros ⟨k, size⟩ H,
    simp only [finset.Ico.mem, fintype.mem_pi_finset, finset.mem_sigma, finset.mem_range] at H,
    let op := ordered_partition.of_size size,
    have one_le_size : ∀ (i : fin k), 1 ≤ size i := λ i, (H.2 i).1,
    have max_index_eq_k : op.max_index = k :=
      ordered_partition.of_size_max_index one_le_size,
    simp only [comp_partial_sum_set, set.finite.mem_to_finset, set.mem_set_of_eq],
    refine ⟨by convert H.1, _⟩,
    assume a,
    let a' : fin k := ⟨a.val, lt_of_lt_of_le a.2 (le_of_eq max_index_eq_k)⟩,
    have : size a' = ordered_partition.size (ordered_partition.of_size size) a :=
      ordered_partition.of_size_size one_le_size a',
    rw ← this,
    exact (H.2 a').2 },
  -- 2 - show that the composition gives the `comp_along_ordered_partition` application
  { dsimp,
    rintros ⟨k, size⟩ H,
    simp only [finset.Ico.mem, fintype.mem_pi_finset, finset.mem_sigma, finset.mem_range] at H,
    let op := ordered_partition.of_size size,
    have one_le_size : ∀ (i : fin k), 1 ≤ size i := λ i, (H.2 i).1,
    have max_index_eq_k : op.max_index = k :=
      ordered_partition.of_size_max_index one_le_size,
    dsimp [formal_multilinear_series.comp_along_ordered_partition_multilinear,
      formal_multilinear_series.apply_ordered_partition],
    unfold_coes,
    congr' 1; try { rw max_index_eq_k },
    apply fin.heq max_index_eq_k.symm,
    assume i,
    have : size i = op.size ⟨i.val, lt_of_lt_of_le i.2 (le_of_eq max_index_eq_k.symm)⟩ :=
      ordered_partition.of_size_size one_le_size i,
    rw this },
  -- 3 - show that the map is injective
  { rintros ⟨k, size⟩ ⟨k', size'⟩ H H' heq,
    simp at H H',
    exact ordered_partition.of_size_inj (λ i, (H.2 i).1) ((λ i, (H'.2 i).1)) heq },
  -- 4 - show that the map is surjective
  { rintros ⟨n, op⟩ H,
    dsimp [comp_partial_sum_set] at H,
    have : ∀ (a : fin op.max_index), 1 ≤ op.size a := λ a, op.size_pos a,
    exact ⟨⟨_, op.size⟩, by tidy, op.of_size_eq_self⟩ }
end

end formal_multilinear_series

open formal_multilinear_series

/-- If two functions `g` and `f` have power series `q` and `p` respectively at `f x` and `x`, then
`g ∘ f` admits the power series `q.comp p` at `x`. -/
theorem has_fpower_series_at.comp {g : F → G} {f : E → F}
  {q : formal_multilinear_series 𝕜 F G} {p : formal_multilinear_series 𝕜 E F} {x : E}
  (hg : has_fpower_series_at g q (f x)) (hf : has_fpower_series_at f p x) :
  has_fpower_series_at (g ∘ f) (q.comp p) x :=
begin
  /- Consider `rf` and `rg` such that `f` and `g` have power series expansion on the disks
  of radius `rf` and `rg`. -/
  rcases hg with ⟨rg, Hg⟩,
  rcases hf with ⟨rf, Hf⟩,
  /- The terms defining `q.comp p` are geometrically summable in a disk of some radius `r`. -/
  rcases q.comp_summable_nnreal p Hg.radius_pos Hf.radius_pos with ⟨r, r_pos, hr⟩,
  /- We will consider `y` which is smaller than `r` and `rf`, and also small enough that
  `f (x + y)` is close enough to `f x` to be in the disk where `g` is well behaved. Let
  `min (r, rf, δ)` be this new radius.-/
  have : continuous_at f x := Hf.analytic_at.continuous_at,
  obtain ⟨δ, δpos, hδ⟩ : ∃ (δ : ennreal) (H : 0 < δ),
    ∀ {z : E}, z ∈ emetric.ball x δ → f z ∈ emetric.ball (f x) rg,
  { have : emetric.ball (f x) rg ∈ 𝓝 (f x) := emetric.ball_mem_nhds _ Hg.r_pos,
    rcases emetric.mem_nhds_iff.1 (Hf.analytic_at.continuous_at this) with ⟨δ, δpos, Hδ⟩,
    exact ⟨δ, δpos, λ z hz, Hδ hz⟩ },
  let rf' := min rf δ,
  have rf'_pos : 0 < rf', by simp [rf', Hf.r_pos, δpos],
  have min_pos : 0 < min rf' r, by simp [r_pos, rf'_pos],
  /- We will show that `g ∘ f` admits the power series `q.comp p` in the disk of
  radius `min (r, rf', δ)`. -/
  refine ⟨min rf' r, _⟩,
  refine ⟨le_trans (min_le_right rf' r)
    (formal_multilinear_series.le_comp_radius_of_summable q p r hr), min_pos, λ y hy, _⟩,
  /- Let `y` satisfy `∥y∥ < min (r, rf', δ)`. We want to show that `g (f (x + y))` is the sum of
  `q.comp p` applied to `y`. -/
  -- First, check that `y` is small enough so that estimates for `f` and `g` apply.
  have y_mem : y ∈ emetric.ball (0 : E) rf :=
    (emetric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _))) hy,
  have fy_mem : f (x + y) ∈ emetric.ball (f x) rg,
  { apply hδ,
    have : y ∈ emetric.ball (0 : E) δ :=
      (emetric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _))) hy,
    simpa [edist_eq_coe_nnnorm_sub, edist_eq_coe_nnnorm] },
  /- Now starts the proof. To show that the sum of `q.comp p` at `y` is `g (f (x + y))`, we will
  write `q.comp p` applied to `y` as a big sum over all ordered partitions. Since the sum is
  summable, to get its convergence it suffices to get the convergence along some increasing sequence
  of sets. We will use the sequence of sets `comp_partial_sum_set n`, along which the sum is
  exactly the composition of the partial sums of `q` and `p`, by design. To show that it converges
  to `g (f (x + y))`, pointwise convergence would not be enough, but we have uniform convergence
  to save the day. -/
  -- First step: the partial sum of `p` converges to `f (x + y)`.
  have A : tendsto (λ n, (finset.Ico 1 n).sum (λ a, p a (λ b, y))) at_top (𝓝 (f (x + y) - f x)),
  { have L : ∀ᶠ n in at_top, (finset.range n).sum (λ a, p a (λ b, y)) - f x =
     (finset.Ico 1 n).sum (λ a, p a (λ b, y)),
    { rw eventually_at_top,
      refine ⟨1, λ n hn, _⟩,
      symmetry,
      rw [eq_sub_iff_add_eq', finset.range_eq_Ico, ← Hf.coeff_zero (λi, y),
          finset.sum_eq_sum_Ico_succ_bot hn] },
    have : tendsto (λ n, (finset.range n).sum (λ a, p a (λ b, y)) - f x) at_top
          (𝓝 (f (x + y) - f x)) :=
      (Hf.has_sum y_mem).tendsto_sum_nat.sub tendsto_const_nhds,
    exact tendsto.congr' L this },
  -- Second step: the composition of the partial sums of `q` and `p` converges to `g (f (x + y))`.
  have B : tendsto (λ n, q.partial_sum n ((finset.Ico 1 n).sum (λ a, p a (λ b, y))))
    at_top (𝓝 (g (f (x + y)))),
  { -- we use the fact that the partial sums of `q` converge locally uniformly to `g`, and that
    -- composition passes to the limit under locally uniform convergence.
    have B₁ : continuous_at (λ (z : F), g (f x + z)) (f (x + y) - f x),
    { refine continuous_at.comp _ (continuous_const.add continuous_id).continuous_at,
      simp only [add_sub_cancel'_right, id.def],
      exact Hg.continuous_on.continuous_at (mem_nhds_sets (emetric.is_open_ball) fy_mem) },
    have B₂ : f (x + y) - f x ∈ emetric.ball (0 : F) rg,
      by simpa [edist_eq_coe_nnnorm, edist_eq_coe_nnnorm_sub] using fy_mem,
    rw [← nhds_within_eq_of_open B₂ emetric.is_open_ball] at A,
    convert Hg.tendsto_locally_uniformly_on.tendsto_comp B₁.continuous_within_at B₂ A,
    simp only [add_sub_cancel'_right] },
  -- Third step: the sum over all ordered partitions in `comp_partial_sum_set n` converges to
  -- `g (f (x + y))`. As this sum is exactly the composition of the partial sum, this is a direct
  -- consequence of the second step
  have C : tendsto (λ n,
    (comp_partial_sum_set n).sum (λ i, q.comp_along_ordered_partition_multilinear p i.2 (λ j, y)))
    at_top (𝓝 (g (f (x + y)))), by simpa [comp_partial_sum] using B,
  -- Fourth step: the sum over all ordered partitions is `g (f (x + y))`. This follows from the
  -- convergence along a subsequence proved in the third step, and the fact that the sum is Cauchy
  -- thanks to the summability properties.
  have D : has_sum (λ i : (Σ n, ordered_partition n),
    q.comp_along_ordered_partition_multilinear p i.2 (λ j, y)) (g (f (x + y))),
  { have cau : cauchy_seq (λ (s : finset (Σ n, ordered_partition n)),
      s.sum (λ i, q.comp_along_ordered_partition_multilinear p i.2 (λ j, y))),
    { apply cauchy_seq_finset_of_norm_bounded _ (nnreal.summable_coe.2 hr) _,
      simp only [coe_nnnorm, nnreal.coe_mul, nnreal.coe_pow],
      rintros ⟨n, op⟩,
      calc ∥(comp_along_ordered_partition q p op) (λ (j : fin n), y)∥
      ≤ ∥comp_along_ordered_partition q p op∥ * finset.univ.prod (λ (j : fin n), ∥y∥) :
        by apply continuous_multilinear_map.le_op_norm
      ... ≤ ∥comp_along_ordered_partition q p op∥ * (r : ℝ) ^ n :
      begin
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
        simp only [finset.card_fin, finset.prod_const],
        apply pow_le_pow_of_le_left (norm_nonneg _),
        rw [emetric.mem_ball, edist_eq_coe_nnnorm] at hy,
        have := (le_trans (le_of_lt hy) (min_le_right _ _)),
        rwa [ennreal.coe_le_coe, ← nnreal.coe_le_coe, coe_nnnorm] at this
      end },
    exact tendsto_nhds_of_cauchy_seq_of_subseq cau at_top_ne_bot
          comp_partial_sum_set_tendsto_at_top C },
  -- Fifth step: the sum over `n` of `q.comp p n` can be expressed as a particular resummation of
  -- the sum over all ordered partitions, by grouping together the ordered partitions of the same
  -- integer `n`. The convergence of the whole sum therefore implies the converence of the sum
  -- of `q.comp p n`
  have E : has_sum (λ n, (q.comp p) n (λ j, y)) (g (f (x + y))),
  { apply D.sigma,
    assume n,
    dsimp [formal_multilinear_series.comp],
    convert has_sum_fintype _,
    simp only [continuous_multilinear_map.sum_apply],
    refl },
  exact E
end

/-- If two functions `g` and `f` are analytic respectively at `f x` and `x`, then `g ∘ f` is
analytic at `x`. -/
theorem analytic_at.comp {g : F → G} {f : E → F} {x : E}
  (hg : analytic_at 𝕜 g (f x)) (hf : analytic_at 𝕜 f x) : analytic_at 𝕜 (g ∘ f) x :=
let ⟨q, hq⟩ := hg, ⟨p, hp⟩ := hf in (hq.comp hp).analytic_at
