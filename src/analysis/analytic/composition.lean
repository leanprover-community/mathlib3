/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.analytic.basic
import combinatorics.composition

/-!
# Composition of analytic functions

in this file we prove that the composition of analytic functions is analytic.

The argument is the following. Assume `g z = ∑' qₙ (z, ..., z)` and `f y = ∑' pₖ (y, ..., y)`. Then

`g (f y) = ∑' qₙ (∑' pₖ (y, ..., y), ..., ∑' pₖ (y, ..., y))
= ∑' qₙ (p_{i₁} (y, ..., y), ..., p_{iₙ} (y, ..., y))`.

For each `n` and `i₁, ..., iₙ`, define a `i₁ + ... + iₙ` multilinear function mapping
`(y₀, ..., y_{i₁ + ... + iₙ - 1})` to
`qₙ (p_{i₁} (y₀, ..., y_{i₁-1}), p_{i₂} (y_{i₁}, ..., y_{i₁ + i₂ - 1}), ..., p_{iₙ} (....)))`.
Then `g ∘ f` is obtained by summing all these multilinear functions.

To formalize this, we use compositions of an integer `N`, i.e., its decompositions into
a sum `i₁ + ... + iₙ` of positive integers. Given such a composition `c` and two formal
multilinear series `q` and `p`, let `q.comp_along_composition p c` be the above multilinear
function. Then the `N`-th coefficient in the power series expansion of `g ∘ f` is the sum of these
terms over all `c : composition N`.

To complete the proof, we need to show that this power series has a positive radius of convergence.
This follows from the fact that `composition N` has cardinality `2^(N-1)` and estimates on
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
`q.comp_along_composition p c` and to show that it is indeed a continuous multilinear
function. This requires a whole interface built on the class `composition`. Once this is set,
the main difficulty is to reorder the sums, writing the composition of the partial sums as a sum
over some subset of `Σ n, composition n`. We need to check that the reordering is a bijection,
running over difficulties due to the dependent nature of the types under consideration, that are
controlled thanks to the interface for `composition`.
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

/-- Given a formal multilinear series `p`, a composition `c` of `n` and the index `i` of a
block of `c`, we may define a function on `fin n → E` by picking the variables in the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. This function is
called `p.apply_composition c v i` for `v : fin n → E` and `i : fin c.length`. -/
def apply_composition
  (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (c : composition n) :
  (fin n → E) → (fin (c.length) → F) :=
λ v i, p (c.blocks_fun i) (v ∘ (c.embedding i))

/-- Technical lemma stating how `p.apply_composition` commutes with updating variables. This
will be the key point to show that functions constructed from `apply_composition` retain
multilinearity. -/
lemma apply_composition_update
  (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (c : composition n)
  (j : fin n) (v : fin n → E) (z : E) :
  p.apply_composition c (function.update v j z)
  = function.update (p.apply_composition c v) (c.index j)
    (p (c.blocks_fun (c.index j))
  (function.update (v ∘ (c.embedding (c.index j))) (c.inv_embedding j) z)) :=
begin
  ext k,
  by_cases h : k = c.index j,
  { rw h,
    let r : fin (c.blocks_fun (c.index j)) → fin n := c.embedding (c.index j),
    simp only [function.update_same],
    change p (c.blocks_fun (c.index j)) ((function.update v j z) ∘ r) = _,
    let j' := c.inv_embedding j,
    suffices B : (function.update v j z) ∘ r = function.update (v ∘ r) j' z,
      by rw B,
    suffices C : (function.update v (r j') z) ∘ r = function.update (v ∘ r) j' z,
      by { convert C, exact c.embedding_comp_inv j },
    exact function.update_comp_eq_of_injective _ (c.embedding_inj _) _ _ },
  { simp only [h, function.update_eq_self, function.update_noteq, ne.def, not_false_iff],
    let r : fin (c.blocks_fun k) → fin n := c.embedding k,
    change p (c.blocks_fun k) ((function.update v j z) ∘ r) = p (c.blocks_fun k) (v ∘ r),
    suffices B : (function.update v j z) ∘ r = v ∘ r, by rw B,
    apply function.update_comp_eq_of_not_mem_range,
    rwa c.mem_range_embedding_iff' }
end

/-- Given two formal multilinear series `q` and `p` and a composition `c` of `n`, one may
form a multilinear map in `n` variables by applying the right coefficient of `p` to each block of
the composition, and then applying `q c.length` to the resulting vector. It is called
`q.comp_along_composition_multilinear p c`. This function admits a version as a continuous
multilinear map, called `q.comp_along_composition p c` below. -/
def comp_along_composition_multilinear {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (c : composition n) : multilinear_map 𝕜 (λ i : fin n, E) G :=
{ to_fun := λ v, q c.length (p.apply_composition c v),
  add    := λ v i x y, by simp [apply_composition_update],
  smul   := λ v i c x, by simp [apply_composition_update] }

/-- The norm of `q.comp_along_composition_multilinear p c` is controlled by the product of
the norms of the relevant bits of `q` and `p`. -/
lemma comp_along_composition_multilinear_bound {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (c : composition n) (v : fin n → E) :
  ∥q.comp_along_composition_multilinear p c v∥
  ≤ ∥q c.length∥ * finset.univ.prod (λ i, ∥p (c.blocks_fun i)∥)
    * (finset.univ : finset (fin n)).prod (λ i, ∥v i∥) :=
begin
  -- main point: taking the product of the `∥v i∥` along each block, and then along all the blocks,
  -- gives the product of all the `∥v i∥`, as the blocks form a partition of the indices.
  have A : finset.univ.prod (λ (i : fin c.length),
    finset.univ.prod (λ (j : fin (c.blocks_fun i)), ∥(v ∘ c.embedding i) j∥)) =
    finset.prod finset.univ (λ (i : fin n), ∥v i∥),
  { -- The fact that a product over a partition gives the whole product is `finset.prod_bind`.
    -- We just need to check its disjointness and totality assumptions.
    have : (∀ (i : fin c.length), i ∈ finset.univ → ∀ (j : fin c.length), j ∈ finset.univ →
       i ≠ j → disjoint (finset.univ.image (c.embedding i)) (finset.univ.image (c.embedding j))),
    { assume i hi j hj i_ne_j,
      rw finset.disjoint_iff_disjoint_coe,
      convert c.disjoint_range i_ne_j;
      apply fintype.coe_image_univ },
    have Z := @finset.prod_bind _ _ _ (λ j, ∥v j∥) _ _ finset.univ
      (λ (i : fin c.length), finset.univ.image (c.embedding i)) this,
    have : (finset.bind finset.univ (λ (i : fin c.length), finset.univ.image (c.embedding i)))
      = finset.univ,
    { ext j,
      simp only [finset.mem_univ, finset.mem_bind, iff_true, exists_prop_of_true, finset.mem_image],
      refine ⟨c.index j, by simpa using c.mem_range_embedding j⟩ },
    rw this at Z,
    rw Z,
    congr,
    ext i,
    rw finset.prod_image,
    assume a ha b hb hab,
    exact c.embedding_inj i hab },
  -- Now that the main point is proved, write down the estimates using the definition of the norm
  -- of a multilinear map
  calc ∥q.comp_along_composition_multilinear p c v∥
  = ∥q c.length (p.apply_composition c v)∥ : rfl
  ... ≤ ∥q c.length∥ * finset.univ.prod (λ i, ∥p.apply_composition c v i∥) :
    continuous_multilinear_map.le_op_norm _ _
  ... ≤ ∥q c.length∥ * finset.univ.prod (λ i, ∥p (c.blocks_fun i)∥ *
     (finset.univ : finset (fin (c.blocks_fun i))).prod (λ j, ∥(v ∘ (c.embedding i)) j∥)) :
    begin
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
      refine finset.prod_le_prod (λ i hi, norm_nonneg _) (λ i hi, _),
      apply continuous_multilinear_map.le_op_norm,
    end
  ... = ∥q c.length∥ * finset.univ.prod (λ i, ∥p (c.blocks_fun i)∥) * finset.univ.prod (λ i,
     (finset.univ : finset (fin (c.blocks_fun i))).prod (λ j, ∥(v ∘ (c.embedding i)) j∥)) :
    by rw [finset.prod_mul_distrib, mul_assoc]
  ... = ∥q c.length∥ * finset.univ.prod (λ i, ∥p (c.blocks_fun i)∥)
    * (finset.univ : finset (fin n)).prod (λ i, ∥v i∥) : by rw A
end

/-- Given two formal multilinear series `q` and `p` and a composition `c` of `n`, one may
form a continuous multilinear map in `n` variables by applying the right coefficient of `p` to each
block of the composition, and then applying `q c.length` to the resulting vector. It is
called `q.comp_along_composition p c`. It is constructed from the analogous multilinear
function `q.comp_along_composition_multilinear p c`, together with a norm control to get
the continuity. -/
def comp_along_composition {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (c : composition n) : continuous_multilinear_map 𝕜 (λ i : fin n, E) G :=
(q.comp_along_composition_multilinear p c).mk_continuous _
  (q.comp_along_composition_multilinear_bound p c)

/-- The norm of `q.comp_along_composition p c` is controlled by the product of
the norms of the relevant bits of `q` and `p`. -/
lemma comp_along_composition_norm {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (c : composition n) :
  ∥q.comp_along_composition p c∥ ≤
  ∥q c.length∥ * finset.univ.prod (λ i, ∥p (c.blocks_fun i)∥) :=
multilinear_map.mk_continuous_norm_le _
  (mul_nonneg (norm_nonneg _) (finset.prod_nonneg (λ i hi, norm_nonneg _))) _

lemma comp_along_composition_nnnorm {n : ℕ}
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (c : composition n) :
  nnnorm (q.comp_along_composition p c) ≤
  nnnorm (q c.length) * finset.univ.prod (λ i, nnnorm (p (c.blocks_fun i))) :=
begin
  simp only [← nnreal.coe_le_coe, coe_nnnorm, nnreal.coe_mul, coe_nnnorm, nnreal.coe_prod, coe_nnnorm],
  exact q.comp_along_composition_norm p c
end

/-- Formal composition of two formal multilinear series. The `n`-th coefficient in the composition
is defined to be the sum of `q.comp_along_composition p c` over all compositions of
`n`. In other words, this term (as a multilinear function applied to `v_0, ..., v_{n-1}`) is
`∑'_{k} ∑'_{i₁ + ... + iₖ = n} pₖ (q_{i_1} (...), ..., q_{i_k} (...))`, where one puts all variables
`v_0, ..., v_{n-1}` in increasing order in the dots.-/
protected def comp (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F) :
  formal_multilinear_series 𝕜 E G :=
λ n, (finset.univ : finset (composition n)).sum (λ c, q.comp_along_composition p c)

/-- If two formal multilinear series have positive radius of convergence, then the terms appearing
in the definition of their composition are also summable (when multiplied by a suitable positive
geometric term). -/
theorem comp_summable_nnreal
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F)
  (hq : 0 < q.radius) (hp : 0 < p.radius) :
  ∃ (r : nnreal), 0 < r ∧ summable (λ i, nnnorm (q.comp_along_composition p i.2) * r ^ i.1 :
    (Σ n, composition n) → nnreal) :=
begin
  /- This follows from the fact that the growth rate of `∥qₙ∥` and `∥pₙ∥` is at most geometric,
  giving a geometric bound on each `∥q.comp_along_composition p op∥`, together with the
  fact that there are `2^(n-1)` compositions of `n`, giving at most a geometric loss. -/
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
  have I : ∀ (i : Σ (n : ℕ), composition n),
    ↑(nnnorm (q.comp_along_composition p i.2) * r ^ i.1) ≤ (Cq : ennreal) * a ^ i.1,
  { rintros ⟨n, c⟩,
    rw [← ennreal.coe_pow, ← ennreal.coe_mul, ennreal.coe_le_coe],
    calc nnnorm (q.comp_along_composition p c) * r ^ n
    ≤ (nnnorm (q c.length) *
        (finset.univ : finset (fin (c.length))).prod (λ i, nnnorm (p (c.blocks_fun i)))) * r ^ n :
      mul_le_mul_of_nonneg_right (q.comp_along_composition_nnnorm p c) (bot_le)
    ... = (nnnorm (q c.length) * (min rq 1)^n) *
      ((finset.univ : finset (fin (c.length))).prod (λ i, nnnorm (p (c.blocks_fun i))) * (min rp 1) ^ n)
      * r0 ^ n : by { dsimp [r], ring_exp }
    ... ≤ (nnnorm (q c.length) * (min rq 1) ^ c.length) *
      ((finset.univ : finset (fin c.length)).prod
        (λ i, nnnorm (p (c.blocks_fun i)) * (min rp 1) ^ (c.blocks_fun i))) * r0 ^ n :
      begin
        apply_rules [mul_le_mul, bot_le, le_refl, pow_le_pow_of_le_one, min_le_right, c.length_le],
        apply le_of_eq,
        rw finset.prod_mul_distrib,
        congr' 1,
        conv_lhs { rw [← c.sum_blocks_fun, ← finset.prod_pow_eq_pow_sum] },
      end
    ... ≤ Cq * ((finset.univ : finset (fin c.length)).prod (λ i, Cp)) * r0 ^ n :
      begin
        apply_rules [mul_le_mul, bot_le, le_trans _ (hCq c.length), le_refl, finset.prod_le_prod'],
        { assume i hi,
          refine le_trans (mul_le_mul (le_refl _) _ bot_le bot_le) (hCp (c.blocks_fun i)),
          exact pow_le_pow_of_le_left bot_le (min_le_left _ _) _ },
        { refine mul_le_mul (le_refl _) _ bot_le bot_le,
          exact pow_le_pow_of_le_left bot_le (min_le_left _ _) _ }
      end
    ... ≤ Cq * (max Cp 1) ^ n * r0 ^ n :
      begin
        apply_rules [mul_le_mul, bot_le, le_refl],
        simp only [finset.card_fin, finset.prod_const],
        refine le_trans (pow_le_pow_of_le_left bot_le (le_max_left Cp 1) c.length) _,
        apply pow_le_pow (le_max_right Cp 1) c.length_le,
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
  calc (∑' (i : Σ (n : ℕ), composition n), ↑(nnnorm (q.comp_along_composition p i.2) * r ^ i.1))
  ≤ (∑' (i : Σ (n : ℕ), composition n), (Cq : ennreal) * a ^ i.1) : ennreal.tsum_le_tsum I
  ... = (∑' (n : ℕ), (∑' (c : composition n), (Cq : ennreal) * a ^ n)) : ennreal.tsum_sigma' _
  ... = (∑' (n : ℕ), ↑(fintype.card (composition n)) * (Cq : ennreal) * a ^ n) :
    begin
      congr' 1,
      ext1 n,
      rw [tsum_fintype, finset.sum_const, add_monoid.smul_eq_mul, finset.card_univ, mul_assoc]
    end
  ... ≤ (∑' (n : ℕ), (2 : ennreal) ^ n * (Cq : ennreal) * a ^ n) :
    begin
      apply ennreal.tsum_le_tsum (λ n, _),
      apply ennreal.mul_le_mul (ennreal.mul_le_mul _ (le_refl _)) (le_refl _),
      rw composition_card,
      simp only [nat.cast_bit0, nat.cast_one, nat.cast_pow],
      apply ennreal.pow_le_pow _ (nat.sub_le n 1),
      have : (1 : nnreal) ≤ (2 : nnreal), by norm_num,
      rw ← ennreal.coe_le_coe at this,
      exact this
    end
  ... = (∑' (n : ℕ), (Cq : ennreal) * (2 * a) ^ n) : by { congr' 1, ext1 n, rw mul_pow, ring }
  ... = (Cq : ennreal) * (1 - 2 * a) ⁻¹ : by rw [ennreal.tsum_mul_left, ennreal.tsum_geometric]
  ... < ⊤ : by simp [lt_top_iff_ne_top, ennreal.mul_eq_top, two_a]
end

/-- Bounding below the radius of the composition of two formal multilinear series assuming
summability over all compositions. -/
theorem le_comp_radius_of_summable
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F) (r : nnreal)
  (hr : summable (λ i, nnnorm (q.comp_along_composition p i.2) * r ^ i.1 :
    (Σ n, composition n) → nnreal)) :
  (r : ennreal) ≤ (q.comp p).radius :=
begin
apply le_radius_of_bound _ (tsum (λ (i : Σ (n : ℕ), composition n),
    (nnnorm (comp_along_composition q p i.snd) * r ^ i.fst))),
  assume n,
  calc nnnorm (formal_multilinear_series.comp q p n) * r ^ n ≤
  ∑' (c : composition n), nnnorm (comp_along_composition q p c) * r ^ n :
    begin
      rw [tsum_fintype, ← finset.sum_mul],
      exact mul_le_mul_of_nonneg_right (nnnorm_sum_le _ _) bot_le
    end
  ... ≤ ∑' (i : Σ (n : ℕ), composition n),
          nnnorm (comp_along_composition q p i.snd) * r ^ i.fst :
    begin
      let f : composition n → (Σ (n : ℕ), composition n) := λ c, ⟨n, c⟩,
      have : function.injective f, by tidy,
      convert nnreal.tsum_comp_le_tsum_of_inj hr this
    end
end

/-! Now, we will prove that the composition of the partial sums of `q` and `p` up to order `N` is
given by a sum over some large subset of `Σ n, composition n` of `q.comp_along_composition p`, to
deduce that the series for `q.comp p` indeed converges to `g ∘ f` when `q` is a power series for
`g` and `p` is a power series for `f`.

This proof is a big reindexing argument of a sum. Since it is a bit involved, we define first
the source of the change of variables (`comp_partial_source`), its target
(`comp_partial_target`) and the change of variables itself (`comp_change_of_variables`) before
giving the main statement in `comp_partial_sum`. -/

/-- Source set in the change of variables to compute the composition of partial sums of formal
power series -/
def comp_partial_sum_source (N : ℕ) : finset (Σ n, (fin n) → ℕ) :=
finset.sigma (finset.range N) (λ (n : ℕ), fintype.pi_finset (λ (i : fin n), finset.Ico 1 N) : _)

@[simp] lemma mem_comp_partial_sum_source_iff (N : ℕ) (i : Σ n, (fin n) → ℕ) :
  i ∈ comp_partial_sum_source N ↔ i.1 < N ∧ ∀ (a : fin i.1), 1 ≤ i.2 a ∧ i.2 a < N :=
by simp [comp_partial_sum_source]

/-- Change of variables appearing to compute the composition of partial sums of formal
power series -/
def comp_change_of_variables (N : ℕ) (i : Σ n, (fin n) → ℕ) (hi : i ∈ comp_partial_sum_source N) :
  (Σn, composition n) :=
begin
  rcases i with ⟨n, f⟩,
  rw mem_comp_partial_sum_source_iff at hi,
  exact ⟨finset.univ.sum f, list.of_fn (λ a, ⟨f a, (hi.2 a).1⟩), by simp [list.sum_of_fn]⟩
end

@[simp] lemma comp_change_of_variables_length
  (N : ℕ) {i : Σ n, (fin n) → ℕ} (hi : i ∈ comp_partial_sum_source N) :
  composition.length (comp_change_of_variables N i hi).2 = i.1 :=
begin
  rcases i with ⟨k, blocks_fun⟩,
  dsimp [comp_change_of_variables],
  simp only [composition.length, composition.blocks, list.map_of_fn, list.length_of_fn]
end

lemma comp_change_of_variables_blocks_fun
  (N : ℕ) {i : Σ n, (fin n) → ℕ} (hi : i ∈ comp_partial_sum_source N) (j : fin i.1) :
  (comp_change_of_variables N i hi).2.blocks_fun
    ⟨j.val, (comp_change_of_variables_length N hi).symm ▸ j.2⟩ = i.2 j :=
begin
  rcases i with ⟨n, f⟩,
  dsimp [composition.blocks_fun, composition.blocks, comp_change_of_variables],
  simp only [list.map_of_fn, pnat.mk_coe, list.nth_le_of_fn', function.comp_app],
  apply congr_arg,
  rw fin.ext_iff
end

/-- Target set in the change of variables to compute the composition of partial sums of formal
power series, here given a a set. -/
def comp_partial_sum_target_set (N : ℕ) : set (Σ n, composition n) :=
{i | (i.2.length < N) ∧ (∀ (j : fin i.2.length), i.2.blocks_fun j < N)}

lemma comp_partial_sum_target_subset_image_comp_partial_sum_source
  (N : ℕ) (i : Σ n, composition n) (hi : i ∈ comp_partial_sum_target_set N) :
  ∃ j (hj : j ∈ comp_partial_sum_source N), i = comp_change_of_variables N j hj :=
begin
  rcases i with ⟨n, c⟩,
  simp [comp_partial_sum_target_set] at hi,
  refine ⟨⟨c.length, c.blocks_fun⟩, _, _⟩,
  { simp only [mem_comp_partial_sum_source_iff, hi.left, hi.right, true_and, and_true],
    exact λ a, c.one_le_blocks' _ },
  { dsimp [comp_change_of_variables],
    rw composition.sigma_eq_iff_blocks_eq,
    simp only [composition.blocks_fun, composition.blocks, subtype.coe_eta, list.nth_le_map'],
    conv_lhs { rw ← list.of_fn_nth_le c.blocks_pnat },
    congr' 2,
    { exact c.blocks_pnat_length },
    { exact (fin.heq_fun_iff c.blocks_pnat_length).2 (λ i, rfl) } }
end

/-- Target set in the change of variables to compute the composition of partial sums of formal
power series, here given a a finset. -/
def comp_partial_sum_target (N : ℕ) : finset (Σ n, composition n) :=
set.finite.to_finset $ set.finite_dependent_image (finset.finite_to_set _)
  (comp_partial_sum_target_subset_image_comp_partial_sum_source N)

@[simp] lemma mem_comp_partial_sum_target_iff {N : ℕ} {a : Σ n, composition n} :
  a ∈ comp_partial_sum_target N ↔ a.2.length < N ∧ (∀ (j : fin a.2.length), a.2.blocks_fun j < N) :=
by simp [comp_partial_sum_target, comp_partial_sum_target_set]

/-- The auxiliary set corresponding to the composition of partial sums asymptotically contains
all possible compositions. -/
lemma comp_partial_sum_target_tendsto_at_top :
  tendsto comp_partial_sum_target at_top at_top :=
begin
  apply monotone.tendsto_at_top_finset,
  { assume m n hmn a ha,
    have : ∀ i, i < m → i < n := λ i hi, lt_of_lt_of_le hi hmn,
    tidy },
  { rintros ⟨n, c⟩,
    simp only [mem_comp_partial_sum_target_iff],
    have : bdd_above ↑(finset.univ.image (λ (i : fin c.length), c.blocks_fun i)) :=
      finset.bdd_above _,
    rcases this with ⟨n, hn⟩,
    refine ⟨max n c.length + 1, lt_of_le_of_lt (le_max_right n c.length) (lt_add_one _),
      λ j, lt_of_le_of_lt (le_trans _ (le_max_left _ _)) (lt_add_one _)⟩,
    apply hn,
    simp only [finset.mem_image_of_mem, finset.mem_coe, finset.mem_univ] }
end

/-- Composing the partial sums of two multilinear series coincides with the sum over all
compositions in `comp_partial_sum_target N`. This is precisely the motivation for the definition of
`comp_partial_sum_target N`. -/
lemma comp_partial_sum
  (q : formal_multilinear_series 𝕜 F G) (p : formal_multilinear_series 𝕜 E F) (N : ℕ) (z : E) :
  q.partial_sum N ((finset.Ico 1 N).sum (λ a, p a (λ b, z)))
    = (comp_partial_sum_target N).sum (λ i, q.comp_along_composition_multilinear p i.2 (λ j, z)) :=
begin
  -- we expand the composition, using the multilinearity of `q` to expand along each coordinate.
  suffices H : (finset.range N).sum
    (λ (n : ℕ), (fintype.pi_finset (λ (i : fin n), finset.Ico 1 N)).sum
          (λ (r : fin n → ℕ), q n (λ (i : fin n), p (r i) (λ (i : fin (r i)), z)))) =
  (comp_partial_sum_target N).sum (λ i, q.comp_along_composition_multilinear p i.2 (λ j, z)),
    by simpa only [formal_multilinear_series.partial_sum,
                   continuous_multilinear_map.map_sum_finset] using H,
  -- rewrite the first sum as a big sum over a sigma type
  rw ← @finset.sum_sigma _ _ _ _
    (finset.range N) (λ (n : ℕ), (fintype.pi_finset (λ (i : fin n), finset.Ico 1 N)) : _)
    (λ i, q i.1 (λ (j : fin i.1), p (i.2 j) (λ (k : fin (i.2 j)), z))),
  -- show that the two sums correspond to each other by reindexing the variables. This is the
  -- content of `finset.sum_bij`, for which we spell out all parameters of the bijection
  -- explicitly as the setting is complicated.
  apply @finset.sum_bij _ _ _ _ (comp_partial_sum_source N) (comp_partial_sum_target N)
    (λ i, q i.1 (λ (j : fin i.1), p (i.2 j) (λ (k : fin (i.2 j)), z)))
    (λ i, q.comp_along_composition_multilinear p i.2 (λ j, z))
    (comp_change_of_variables N),
  -- To conclude, we should show that the correspondance we have set up is indeed a bijection
  -- between the index sets of the two sums.
  -- 1 - show that the image belongs to `comp_partial_sum_target N`
  { rintros ⟨k, blocks_fun⟩ H,
    rw mem_comp_partial_sum_source_iff at H,
    simp only [mem_comp_partial_sum_target_iff, composition.length, composition.blocks, H.left,
               list.map_of_fn, list.length_of_fn, true_and, comp_change_of_variables],
    assume j,
    simp only [composition.blocks_fun, composition.blocks, (H.right _).right, pnat.mk_coe,
               list.map_of_fn, list.nth_le_of_fn', function.comp_app] },
  -- 2 - show that the composition gives the `comp_along_composition` application
  { rintros ⟨k, blocks_fun⟩ H,
    have L := comp_change_of_variables_length N H,
    have B := comp_change_of_variables_blocks_fun N H,
    rw mem_comp_partial_sum_source_iff at H,
    dsimp [formal_multilinear_series.comp_along_composition_multilinear,
      formal_multilinear_series.apply_composition, comp_change_of_variables] at L B ⊢,
    unfold_coes,
    congr' 1; try { rw L },
    apply (fin.heq_fun_iff L.symm).2 (λ j, _),
    rw ← B },
  -- 3 - show that the map is injective
  { assume i i' H H' heq,
    have B := comp_change_of_variables_blocks_fun N H,
    have B' := comp_change_of_variables_blocks_fun N H',
    have A : i.1 = i'.1,
    { rw [← comp_change_of_variables_length N H, ← comp_change_of_variables_length _ H', heq] },
    rcases i with ⟨k, blocks_fun⟩,
    rcases i' with ⟨k', blocks_fun'⟩,
    dsimp at A B B',
    simp only [A, fin.heq_fun_iff, true_and, eq_self_iff_true],
    assume i,
    rw [← B, ← B'],
    congr' 1; try { rw heq },
    rw fin.heq_ext_iff,
    rw heq },
  -- 4 - show that the map is surjective
  { assume i hi,
    apply comp_partial_sum_target_subset_image_comp_partial_sum_source N i,
    simpa [comp_partial_sum_target] using hi }
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
  write `q.comp p` applied to `y` as a big sum over all compositions. Since the sum is
  summable, to get its convergence it suffices to get the convergence along some increasing sequence
  of sets. We will use the sequence of sets `comp_partial_sum_target n`, along which the sum is
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
  -- Third step: the sum over all compositions in `comp_partial_sum_target n` converges to
  -- `g (f (x + y))`. As this sum is exactly the composition of the partial sum, this is a direct
  -- consequence of the second step
  have C : tendsto (λ n,
    (comp_partial_sum_target n).sum (λ i, q.comp_along_composition_multilinear p i.2 (λ j, y)))
    at_top (𝓝 (g (f (x + y)))), by simpa [comp_partial_sum] using B,
  -- Fourth step: the sum over all compositions is `g (f (x + y))`. This follows from the
  -- convergence along a subsequence proved in the third step, and the fact that the sum is Cauchy
  -- thanks to the summability properties.
  have D : has_sum (λ i : (Σ n, composition n),
    q.comp_along_composition_multilinear p i.2 (λ j, y)) (g (f (x + y))),
  { have cau : cauchy_seq (λ (s : finset (Σ n, composition n)),
      s.sum (λ i, q.comp_along_composition_multilinear p i.2 (λ j, y))),
    { apply cauchy_seq_finset_of_norm_bounded _ (nnreal.summable_coe.2 hr) _,
      simp only [coe_nnnorm, nnreal.coe_mul, nnreal.coe_pow],
      rintros ⟨n, c⟩,
      calc ∥(comp_along_composition q p c) (λ (j : fin n), y)∥
      ≤ ∥comp_along_composition q p c∥ * finset.univ.prod (λ (j : fin n), ∥y∥) :
        by apply continuous_multilinear_map.le_op_norm
      ... ≤ ∥comp_along_composition q p c∥ * (r : ℝ) ^ n :
      begin
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
        simp only [finset.card_fin, finset.prod_const],
        apply pow_le_pow_of_le_left (norm_nonneg _),
        rw [emetric.mem_ball, edist_eq_coe_nnnorm] at hy,
        have := (le_trans (le_of_lt hy) (min_le_right _ _)),
        rwa [ennreal.coe_le_coe, ← nnreal.coe_le_coe, coe_nnnorm] at this
      end },
    exact tendsto_nhds_of_cauchy_seq_of_subseq cau at_top_ne_bot
          comp_partial_sum_target_tendsto_at_top C },
  -- Fifth step: the sum over `n` of `q.comp p n` can be expressed as a particular resummation of
  -- the sum over all compositions, by grouping together the compositions of the same
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
