/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.normed_space.operator_norm
import topology.algebra.multilinear

/-!
# Operator norm on the space of continuous multilinear maps

When `f` is a continuous multilinear map in finitely many variables, we define its norm `∥f∥` as the
smallest number such that `∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥` for all `m`.

We show that it is indeed a norm, and prove its basic properties.

## Main results

Let `f` be a multilinear map in finitely many variables.
* `exists_bound_of_continuous` asserts that, if `f` is continuous, then there exists `C > 0`
  with `∥f m∥ ≤ C * ∏ i, ∥m i∥` for all `m`.
* `continuous_of_bound`, conversely, asserts that this bound implies continuity.
* `mk_continuous` constructs the associated continuous multilinear map.

Let `f` be a continuous multilinear map in finitely many variables.
* `∥f∥` is its norm, i.e., the smallest number such that `∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥` for
  all `m`.
* `le_op_norm f m` asserts the fundamental inequality `∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥`.
* `norm_image_sub_le_of_bound f m₁ m₂` gives a control of the difference `f m₁ - f m₂` in terms of
  `∥f∥` and `∥m₁ - m₂∥`.

We also register isomorphisms corresponding to currying or uncurrying variables, transforming a
continuous multilinear function `f` in `n+1` variables into a continuous linear function taking
values in continuous multilinear functions in `n` variables, and also into a continuous multilinear
function in `n` variables taking values in continuous linear functions. These operations are called
`f.curry_left` and `f.curry_right` respectively (with inverses `f.uncurry_left` and
`f.uncurry_right`). They induce continuous linear equivalences between spaces of
continuous multilinear functions in `n+1` variables and spaces of continuous linear functions into
continuous multilinear functions in `n` variables (resp. continuous multilinear functions in `n`
variables taking values in continuous linear functions), called respectively
`continuous_multilinear_curry_left_equiv` and `continuous_multilinear_curry_right_equiv`.

## Implementation notes

We mostly follow the API (and the proofs) of `operator_norm.lean`, with the additional complexity
that we should deal with multilinear maps in several variables. The currying/uncurrying
constructions are based on those in `multilinear.lean`.

From the mathematical point of view, all the results follow from the results on operator norm in
one variable, by applying them to one variable after the other through currying. However, this
is only well defined when there is an order on the variables (for instance on `fin n`) although
the final result is independent of the order. While everything could be done following this
approach, it turns out that direct proofs are easier and more efficient.
-/

noncomputable theory
open_locale classical big_operators
open finset

local attribute [instance, priority 1001]
add_comm_group.to_add_comm_monoid normed_group.to_add_comm_group normed_space.to_semimodule

universes u v w w₁ w₂ wG
variables {𝕜 : Type u} {ι : Type v} {n : ℕ}
{G : Type wG} {E : fin n.succ → Type w} {E₁ : ι → Type w₁} {E₂ : Type w₂}
[decidable_eq ι] [fintype ι] [nondiscrete_normed_field 𝕜]
[normed_group G] [∀i, normed_group (E i)]  [∀i, normed_group (E₁ i)] [normed_group E₂]
[normed_space 𝕜 G] [∀i, normed_space 𝕜 (E i)] [∀i, normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂]

/-!
### Continuity properties of multilinear maps

We relate continuity of multilinear maps to the inequality `∥f m∥ ≤ C * ∏ i, ∥m i∥`, in
both directions. Along the way, we prove useful bounds on the difference `∥f m₁ - f m₂∥`.
-/
namespace multilinear_map

variable (f : multilinear_map 𝕜 E₁ E₂)

/-- If a multilinear map in finitely many variables on normed spaces is continuous, then it
satisfies the inequality `∥f m∥ ≤ C * ∏ i, ∥m i∥`, for some `C` which can be chosen to be
positive. -/
theorem exists_bound_of_continuous (hf : continuous f) :
  ∃ (C : ℝ), 0 < C ∧ (∀ m, ∥f m∥ ≤ C * ∏ i, ∥m i∥) :=
begin
  /- The proof only uses the continuity at `0`. Then, given a general point `m`, rescale each of
  its coordinates to bring them to a shell of fixed width around `0`, on which one knows that `f` is
  bounded, and then use the multiplicativity of `f` along each coordinate to deduce the desired
  bound.-/
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ∀{m}, dist m 0 < ε → dist (f m) (f 0) < 1 :=
    metric.tendsto_nhds_nhds.1 hf.continuous_at 1 zero_lt_one,
  let δ := ε/2,
  have δ_pos : δ > 0 := half_pos ε_pos,
  /- On points of size at most `δ`, `f` is bounded (by `1 + ∥f 0∥`). -/
  have H : ∀{a}, ∥a∥ ≤ δ → ∥f a∥ ≤ 1 + ∥f 0∥,
  { assume a ha,
    have : dist (f a) (f 0) ≤ 1,
    { apply le_of_lt (hε _),
      rw [dist_eq_norm, sub_zero],
      exact lt_of_le_of_lt ha (half_lt_self ε_pos) },
    calc ∥f a∥ = dist (f a) 0 : (dist_zero_right _).symm
      ... ≤ dist (f a) (f 0) + dist (f 0) 0 : dist_triangle _ _ _
      ... ≤ 1 + ∥f 0∥ : by { rw dist_zero_right, exact add_le_add_right this _ } },
  obtain ⟨c, hc⟩ : ∃c : 𝕜, 1 < ∥c∥ := normed_field.exists_one_lt_norm 𝕜,
  set C := (1 + ∥f 0∥) * ∏ i : ι, (δ⁻¹ * ∥c∥),
  have C_pos : 0 < C :=
    mul_pos (lt_of_lt_of_le zero_lt_one (by simp))
      (prod_pos (λi hi, mul_pos (inv_pos.2 δ_pos) (lt_of_le_of_lt zero_le_one hc))),
  refine ⟨C, C_pos, λm, _⟩,
  /- Given a general point `m`, rescale each coordinate to bring it to `[δ/∥c∥, δ]` by multiplication
  by a power of a scalar `c` with norm `∥c∥ > 1`.-/
  by_cases h : ∃i, m i = 0,
  { rcases h with ⟨i, hi⟩,
    rw [f.map_coord_zero i hi, _root_.norm_zero],
    exact mul_nonneg (le_of_lt C_pos) (prod_nonneg (λi hi, norm_nonneg _)) },
  { push_neg at h,
    have : ∀i, ∃d:𝕜, d ≠ 0 ∧ ∥d • m i∥ ≤ δ ∧ (δ/∥c∥ ≤ ∥d • m i∥) ∧ (∥d∥⁻¹ ≤ δ⁻¹ * ∥c∥ * ∥m i∥) :=
      λi, rescale_to_shell hc δ_pos (h i),
    choose d hd using this,
    have A : 0 ≤ 1 + ∥f 0∥ := add_nonneg zero_le_one (norm_nonneg _),
    have B : ∀ (i : ι), i ∈ univ → 0 ≤ ∥d i∥⁻¹ := λi hi, by simp,
    -- use the bound on `f` on the ball of size `δ` to conclude.
    calc
      ∥f m∥ = ∥f (λi, (d i)⁻¹ • (d i • m i))∥ :
        by { unfold_coes, congr, ext i, rw [← mul_smul, inv_mul_cancel (hd i).1, one_smul] }
      ... = ∥(∏ i, (d i)⁻¹) • f (λi, d i • m i)∥ : by rw f.map_smul_univ
      ... = (∏ i, ∥d i∥⁻¹) * ∥f (λi, d i • m i)∥ :
        by { rw [norm_smul, normed_field.norm_prod], congr, ext i, rw normed_field.norm_inv }
      ... ≤ (∏ i, ∥d i∥⁻¹) * (1 + ∥f 0∥) :
        mul_le_mul_of_nonneg_left (H ((pi_norm_le_iff (le_of_lt δ_pos)).2 (λi, (hd i).2.1)))
          (prod_nonneg B)
      ... ≤ (∏ i, δ⁻¹ * ∥c∥ * ∥m i∥) * (1 + ∥f 0∥) :
        mul_le_mul_of_nonneg_right (prod_le_prod B (λi hi, (hd i).2.2.2)) A
      ... = (∏ i : ι, δ⁻¹ * ∥c∥) * (∏ i, ∥m i∥) * (1 + ∥f 0∥) :
        by rw prod_mul_distrib
      ... = C * (∏ i, ∥m i∥) :
        by rw [mul_comm, ← mul_assoc] }
end

/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a precise but hard to use version. See
`norm_image_sub_le_of_bound` for a less precise but more usable version. The bound reads
`∥f m - f m'∥ ≤ C * ∥m 1 - m' 1∥ * max ∥m 2∥ ∥m' 2∥ * max ∥m 3∥ ∥m' 3∥ * ... * max ∥m n∥ ∥m' n∥ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
lemma norm_image_sub_le_of_bound' {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ m, ∥f m∥ ≤ C * ∏ i, ∥m i∥) (m₁ m₂ : Πi, E₁ i) :
  ∥f m₁ - f m₂∥ ≤
  C * ∑ i, ∏ j, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥ :=
begin
  have A : ∀(s : finset ι), ∥f m₁ - f (s.piecewise m₂ m₁)∥
    ≤ C * ∑ i in s, ∏ j, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥,
  { refine finset.induction (by simp) _,
    assume i s his Hrec,
    have I : ∥f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)∥
      ≤ C * ∏ j, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥,
    { have A : ((insert i s).piecewise m₂ m₁)
            = function.update (s.piecewise m₂ m₁) i (m₂ i) := s.piecewise_insert _ _ _,
      have B : s.piecewise m₂ m₁ = function.update (s.piecewise m₂ m₁) i (m₁ i),
      { ext j,
        by_cases h : j = i,
        { rw h, simp [his] },
        { simp [h] } },
      rw [B, A, ← f.map_sub],
      apply le_trans (H _) (mul_le_mul_of_nonneg_left _ hC),
      refine prod_le_prod (λj hj, norm_nonneg _) (λj hj, _),
      by_cases h : j = i,
      { rw h, simp },
      { by_cases h' : j ∈ s;
        simp [h', h, le_refl] } },
    calc ∥f m₁ - f ((insert i s).piecewise m₂ m₁)∥ ≤
      ∥f m₁ - f (s.piecewise m₂ m₁)∥ + ∥f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)∥ :
        by { rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm], exact dist_triangle _ _ _ }
      ... ≤ (C * ∑ i in s, ∏ j, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥)
            + C * ∏ j, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥ :
        add_le_add Hrec I
      ... = C * ∑ i in insert i s, ∏ j, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥ :
        by simp [his, add_comm, left_distrib] },
  convert A univ,
  simp
end

/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a usable but not very precise version. See
`norm_image_sub_le_of_bound'` for a more precise but less usable version. The bound is
`∥f m - f m'∥ ≤ C * card ι * ∥m - m'∥ * (max ∥m∥ ∥m'∥) ^ (card ι - 1)`. -/
lemma norm_image_sub_le_of_bound {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ m, ∥f m∥ ≤ C * ∏ i, ∥m i∥) (m₁ m₂ : Πi, E₁ i) :
  ∥f m₁ - f m₂∥ ≤ C * (fintype.card ι) * (max ∥m₁∥ ∥m₂∥) ^ (fintype.card ι - 1) * ∥m₁ - m₂∥ :=
begin
  have A : ∀ (i : ι), ∏ j, (if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥)
    ≤ ∥m₁ - m₂∥ * (max ∥m₁∥ ∥m₂∥) ^ (fintype.card ι - 1),
  { assume i,
    calc ∏ j, (if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥)
    ≤ ∏ j : ι, function.update (λ j, max ∥m₁∥ ∥m₂∥) i (∥m₁ - m₂∥) j :
      begin
        apply prod_le_prod,
        { assume j hj, by_cases h : j = i; simp [h, norm_nonneg] },
        { assume j hj,
          by_cases h : j = i,
          { rw h, simp, exact norm_le_pi_norm (m₁ - m₂) i },
          { simp [h, max_le_max, norm_le_pi_norm] } }
      end
    ... = ∥m₁ - m₂∥ * (max ∥m₁∥ ∥m₂∥) ^ (fintype.card ι - 1) :
      by { rw prod_update_of_mem (finset.mem_univ _), simp [card_univ_diff] } },
  calc
  ∥f m₁ - f m₂∥
  ≤ C * ∑ i, ∏ j, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥ :
    f.norm_image_sub_le_of_bound' hC H m₁ m₂
  ... ≤ C * ∑ i, ∥m₁ - m₂∥ * (max ∥m₁∥ ∥m₂∥) ^ (fintype.card ι - 1) :
    mul_le_mul_of_nonneg_left (sum_le_sum (λi hi, A i)) hC
  ... = C * (fintype.card ι) * (max ∥m₁∥ ∥m₂∥) ^ (fintype.card ι - 1) * ∥m₁ - m₂∥ :
    by { rw [sum_const, card_univ, nsmul_eq_mul], ring }
end

/-- If a multilinear map satisfies an inequality `∥f m∥ ≤ C * ∏ i, ∥m i∥`, then it is
continuous. -/
theorem continuous_of_bound (C : ℝ) (H : ∀ m, ∥f m∥ ≤ C * ∏ i, ∥m i∥) :
  continuous f :=
begin
  let D := max C 1,
  have D_pos : 0 ≤ D := le_trans zero_le_one (le_max_right _ _),
  replace H : ∀ m, ∥f m∥ ≤ D * ∏ i, ∥m i∥,
  { assume m,
    apply le_trans (H m) (mul_le_mul_of_nonneg_right (le_max_left _ _) _),
    exact prod_nonneg (λ(i : ι) hi, norm_nonneg (m i)) },
  refine continuous_iff_continuous_at.2 (λm, _),
  refine continuous_at_of_locally_lipschitz zero_lt_one
    (D * (fintype.card ι) * (∥m∥ + 1) ^ (fintype.card ι - 1)) (λm' h', _),
  rw [dist_eq_norm, dist_eq_norm],
  have : 0 ≤ (max ∥m'∥ ∥m∥), by simp,
  have : (max ∥m'∥ ∥m∥) ≤ ∥m∥ + 1,
    by simp [zero_le_one, norm_le_of_mem_closed_ball (le_of_lt h'), -add_comm],
  calc
    ∥f m' - f m∥
    ≤ D * (fintype.card ι) * (max ∥m'∥ ∥m∥) ^ (fintype.card ι - 1) * ∥m' - m∥ :
      f.norm_image_sub_le_of_bound D_pos H m' m
    ... ≤ D * (fintype.card ι) * (∥m∥ + 1) ^ (fintype.card ι - 1) * ∥m' - m∥ :
      by apply_rules [mul_le_mul_of_nonneg_right, mul_le_mul_of_nonneg_left, mul_nonneg,
        norm_nonneg, nat.cast_nonneg, pow_le_pow_of_le_left]
end

/-- Constructing a continuous multilinear map from a multilinear map satisfying a boundedness
condition. -/
def mk_continuous (C : ℝ) (H : ∀ m, ∥f m∥ ≤ C * ∏ i, ∥m i∥) :
  continuous_multilinear_map 𝕜 E₁ E₂ :=
{ cont := f.continuous_of_bound C H, ..f }

/-- Given a multilinear map in `n` variables, if one restricts it to `k` variables putting `z` on
the other coordinates, then the resulting restricted function satisfies an inequality
`∥f.restr v∥ ≤ C * ∥z∥^(n-k) * Π ∥v i∥` if the original function satisfies `∥f v∥ ≤ C * Π ∥v i∥`. -/
lemma restr_norm_le {k n : ℕ} (f : (multilinear_map 𝕜 (λ i : fin n, G) E₂ : _))
  (s : finset (fin n)) (hk : s.card = k) (z : G) {C : ℝ}
  (H : ∀ m, ∥f m∥ ≤ C * ∏ i, ∥m i∥) (v : fin k → G) :
  ∥f.restr s hk z v∥ ≤ C * ∥z∥ ^ (n - k) * ∏ i, ∥v i∥ :=
calc ∥f.restr s hk z v∥
≤ C * ∏ j, ∥(if h : j ∈ s then v ((s.mono_equiv_of_fin hk).symm ⟨j, h⟩) else z)∥ : H _
... = C * ((∏ j in finset.univ \ s,
        ∥(if h : j ∈ s then v ((s.mono_equiv_of_fin hk).symm ⟨j, h⟩) else z)∥)
      * (∏ j in s,
        ∥(if h : j ∈ s then v ((s.mono_equiv_of_fin hk).symm ⟨j, h⟩) else z)∥)) :
  by rw ← finset.prod_sdiff (finset.subset_univ _)
... = C * (∥z∥ ^ (n - k) * ∏ i, ∥v i∥) :
  begin
    congr' 2,
    { have : ∥z∥ ^ (n - k) = ∏ j in finset.univ \ s, ∥z∥,
        by simp [finset.card_sdiff  (finset.subset_univ _), hk],
      rw this,
      exact finset.prod_congr rfl (λ i hi, by rw dif_neg (finset.mem_sdiff.1 hi).2) },
    { apply finset.prod_bij (λ (i : fin n) (hi : i ∈ s), (s.mono_equiv_of_fin hk).symm ⟨i, hi⟩),
      { exact λ _ _, finset.mem_univ _ },
      { exact λ i hi, by simp [hi] },
      { exact λ i j hi hi hij, subtype.mk.inj ((s.mono_equiv_of_fin hk).symm.injective hij) },
      { assume i hi,
        rcases (s.mono_equiv_of_fin hk).symm.surjective i with ⟨j, hj⟩,
        refine ⟨j.1, j.2, _⟩,
        unfold_coes,
        convert hj.symm,
        rw subtype.ext_iff_val } }
  end
... = C * ∥z∥ ^ (n - k) * ∏ i, ∥v i∥ : by rw mul_assoc

end multilinear_map

/-!
### Continuous multilinear maps

We define the norm `∥f∥` of a continuous multilinear map `f` in finitely many variables as the
smallest number such that `∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥` for all `m`. We show that this
defines a normed space structure on `continuous_multilinear_map 𝕜 E₁ E₂`.
-/
namespace continuous_multilinear_map

variables (c : 𝕜) (f g : continuous_multilinear_map 𝕜 E₁ E₂) (m : Πi, E₁ i)

theorem bound : ∃ (C : ℝ), 0 < C ∧ (∀ m, ∥f m∥ ≤ C * ∏ i, ∥m i∥) :=
f.to_multilinear_map.exists_bound_of_continuous f.2

open real

/-- The operator norm of a continuous multilinear map is the inf of all its bounds. -/
def op_norm := Inf {c | 0 ≤ (c : ℝ) ∧ ∀ m, ∥f m∥ ≤ c * ∏ i, ∥m i∥}
instance has_op_norm : has_norm (continuous_multilinear_map 𝕜 E₁ E₂) := ⟨op_norm⟩

lemma norm_def : ∥f∥ = Inf {c | 0 ≤ (c : ℝ) ∧ ∀ m, ∥f m∥ ≤ c * ∏ i, ∥m i∥} := rfl

-- So that invocations of `real.Inf_le` make sense: we show that the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty {f : continuous_multilinear_map 𝕜 E₁ E₂} :
  ∃ c, c ∈ {c | 0 ≤ c ∧ ∀ m, ∥f m∥ ≤ c * ∏ i, ∥m i∥} :=
let ⟨M, hMp, hMb⟩ := f.bound in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below {f : continuous_multilinear_map 𝕜 E₁ E₂} :
  bdd_below {c | 0 ≤ c ∧ ∀ m, ∥f m∥ ≤ c * ∏ i, ∥m i∥} :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma op_norm_nonneg : 0 ≤ ∥f∥ :=
lb_le_Inf _ bounds_nonempty (λ _ ⟨hx, _⟩, hx)

/-- The fundamental property of the operator norm of a continuous multilinear map:
`∥f m∥` is bounded by `∥f∥` times the product of the `∥m i∥`. -/
theorem le_op_norm : ∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥ :=
begin
  have A : 0 ≤ ∏ i, ∥m i∥ := prod_nonneg (λj hj, norm_nonneg _),
  by_cases h : ∏ i, ∥m i∥ = 0,
  { rcases prod_eq_zero_iff.1 h with ⟨i, _, hi⟩,
    rw norm_eq_zero at hi,
    have : f m = 0 := f.map_coord_zero i hi,
    rw [this, norm_zero],
    exact mul_nonneg (op_norm_nonneg f) A },
  { have hlt : 0 < ∏ i, ∥m i∥ := lt_of_le_of_ne A (ne.symm h),
    exact le_mul_of_div_le hlt ((le_Inf _ bounds_nonempty bounds_bdd_below).2
      (λ c ⟨_, hc⟩, div_le_of_le_mul hlt (begin rw mul_comm, apply hc, end))) }
end

lemma ratio_le_op_norm : ∥f m∥ / ∏ i, ∥m i∥ ≤ ∥f∥ :=
begin
  have : 0 ≤ ∏ i, ∥m i∥ := prod_nonneg (λj hj, norm_nonneg _),
  cases eq_or_lt_of_le this with h h,
  { simp [h.symm, op_norm_nonneg f] },
  { rw div_le_iff h,
    exact le_op_norm f m }
end

/-- The image of the unit ball under a continuous multilinear map is bounded. -/
lemma unit_le_op_norm (h : ∥m∥ ≤ 1) : ∥f m∥ ≤ ∥f∥ :=
calc
  ∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥ : f.le_op_norm m
  ... ≤ ∥f∥ * ∏ i : ι, 1 :
    mul_le_mul_of_nonneg_left (prod_le_prod (λi hi, norm_nonneg _) (λi hi, le_trans (norm_le_pi_norm _ _) h))
      (op_norm_nonneg f)
  ... = ∥f∥ : by simp

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
lemma op_norm_le_bound {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ m, ∥f m∥ ≤ M * ∏ i, ∥m i∥) :
  ∥f∥ ≤ M :=
Inf_le _ bounds_bdd_below ⟨hMp, hM⟩

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ∥f + g∥ ≤ ∥f∥ + ∥g∥ :=
Inf_le _ bounds_bdd_below
  ⟨add_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x, by { rw add_mul,
    exact norm_add_le_of_le (le_op_norm _ _) (le_op_norm _ _) }⟩

/-- A continuous linear map is zero iff its norm vanishes. -/
theorem op_norm_zero_iff : ∥f∥ = 0 ↔ f = 0 :=
begin
  split,
  { assume h,
    ext m,
    simpa [h, norm_le_zero_iff.symm] using f.le_op_norm m },
  { assume h,
    apply le_antisymm (op_norm_le_bound f (le_refl _) (λm, _)) (op_norm_nonneg _),
    rw h,
    simp }
end

@[simp] lemma norm_zero : ∥(0 : continuous_multilinear_map 𝕜 E₁ E₂)∥ = 0 :=
by rw op_norm_zero_iff

lemma op_norm_smul_le : ∥c • f∥ ≤ ∥c∥ * ∥f∥ :=
(Inf_le _ bounds_bdd_below
  ⟨mul_nonneg (norm_nonneg _) (op_norm_nonneg _), λ _,
  begin
    erw [norm_smul, mul_assoc],
    exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)
  end⟩)

lemma op_norm_neg : ∥-f∥ = ∥f∥ := by { rw norm_def, apply congr_arg, ext, simp }

/-- Continuous multilinear maps themselves form a normed space with respect to
    the operator norm. -/
instance to_normed_group : normed_group (continuous_multilinear_map 𝕜 E₁ E₂) :=
normed_group.of_core _ ⟨op_norm_zero_iff, op_norm_add_le, op_norm_neg⟩

instance to_normed_space : normed_space 𝕜 (continuous_multilinear_map 𝕜 E₁ E₂) :=
⟨op_norm_smul_le⟩

/-- The difference `f m₁ - f m₂` is controlled in terms of `∥f∥` and `∥m₁ - m₂∥`, precise version.
For a less precise but more usable version, see `norm_image_sub_le_of_bound`. The bound reads
`∥f m - f m'∥ ≤ ∥f∥ * ∥m 1 - m' 1∥ * max ∥m 2∥ ∥m' 2∥ * max ∥m 3∥ ∥m' 3∥ * ... * max ∥m n∥ ∥m' n∥ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`.-/
lemma norm_image_sub_le_of_bound' (m₁ m₂ : Πi, E₁ i) :
  ∥f m₁ - f m₂∥ ≤
  ∥f∥ * ∑ i, ∏ j, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥ :=
f.to_multilinear_map.norm_image_sub_le_of_bound' (norm_nonneg _) f.le_op_norm _ _

/-- The difference `f m₁ - f m₂` is controlled in terms of `∥f∥` and `∥m₁ - m₂∥`, less precise
version. For a more precise but less usable version, see `norm_image_sub_le_of_bound'`.
The bound is `∥f m - f m'∥ ≤ ∥f∥ * card ι * ∥m - m'∥ * (max ∥m∥ ∥m'∥) ^ (card ι - 1)`.-/
lemma norm_image_sub_le_of_bound (m₁ m₂ : Πi, E₁ i) :
  ∥f m₁ - f m₂∥ ≤ ∥f∥ * (fintype.card ι) * (max ∥m₁∥ ∥m₂∥) ^ (fintype.card ι - 1) * ∥m₁ - m₂∥ :=
f.to_multilinear_map.norm_image_sub_le_of_bound (norm_nonneg _) f.le_op_norm _ _

/-- Applying a multilinear map to a vector is continuous in both coordinates. -/
lemma continuous_eval :
  continuous (λ (p : (continuous_multilinear_map 𝕜 E₁ E₂ × (Πi, E₁ i))), p.1 p.2) :=
begin
  apply continuous_iff_continuous_at.2 (λp, _),
  apply continuous_at_of_locally_lipschitz zero_lt_one
    ((∥p∥ + 1) * (fintype.card ι) * (∥p∥ + 1) ^ (fintype.card ι - 1) + ∏ i, ∥p.2 i∥)
    (λq hq, _),
  have : 0 ≤ (max ∥q.2∥ ∥p.2∥), by simp,
  have : 0 ≤ ∥p∥ + 1, by simp [le_trans zero_le_one],
  have A : ∥q∥ ≤ ∥p∥ + 1 := norm_le_of_mem_closed_ball (le_of_lt hq),
  have : (max ∥q.2∥ ∥p.2∥) ≤ ∥p∥ + 1 :=
    le_trans (max_le_max (norm_snd_le q) (norm_snd_le p)) (by simp [A, -add_comm, zero_le_one]),
  have : ∀ (i : ι), i ∈ univ → 0 ≤ ∥p.2 i∥ := λ i hi, norm_nonneg _,
  calc dist (q.1 q.2) (p.1 p.2)
    ≤ dist (q.1 q.2) (q.1 p.2) + dist (q.1 p.2) (p.1 p.2) : dist_triangle _ _ _
    ... = ∥q.1 q.2 - q.1 p.2∥ + ∥q.1 p.2 - p.1 p.2∥ : by rw [dist_eq_norm, dist_eq_norm]
    ... ≤ ∥q.1∥ * (fintype.card ι) * (max ∥q.2∥ ∥p.2∥) ^ (fintype.card ι - 1) * ∥q.2 - p.2∥
          + ∥q.1 - p.1∥ * ∏ i, ∥p.2 i∥ :
      add_le_add (norm_image_sub_le_of_bound _ _ _) ((q.1 - p.1).le_op_norm p.2)
    ... ≤ (∥p∥ + 1) * (fintype.card ι) * (∥p∥ + 1) ^ (fintype.card ι - 1) * ∥q - p∥
          + ∥q - p∥ * ∏ i, ∥p.2 i∥ :
      by apply_rules [add_le_add, mul_le_mul, le_refl, le_trans (norm_fst_le q) A, nat.cast_nonneg,
        mul_nonneg, pow_le_pow_of_le_left, pow_nonneg, norm_snd_le (q - p), norm_nonneg,
        norm_fst_le (q - p), norm_nonneg, prod_nonneg]
    ... = ((∥p∥ + 1) * (fintype.card ι) * (∥p∥ + 1) ^ (fintype.card ι - 1)
              + (∏ i, ∥p.2 i∥)) * dist q p : by { rw dist_eq_norm, ring }
end

lemma continuous_eval_left (m : Π i, E₁ i) :
  continuous (λ (p : (continuous_multilinear_map 𝕜 E₁ E₂)), (p : (Π i, E₁ i) → E₂) m) :=
continuous_eval.comp (continuous.prod_mk continuous_id continuous_const)

lemma has_sum_eval
  {α : Type*} {p : α → continuous_multilinear_map 𝕜 E₁ E₂} {q : continuous_multilinear_map 𝕜 E₁ E₂}
  (h : has_sum p q) (m : Π i, E₁ i) : has_sum (λ a, p a m) (q m) :=
begin
  dsimp [has_sum] at h ⊢,
  convert ((continuous_eval_left m).tendsto _).comp h,
  ext s,
  simp
end

open_locale topological_space
open filter

/-- If the target space is complete, the space of continuous multilinear maps with its norm is also
complete. The proof is essentially the same as for the space of continuous linear maps (modulo the
addition of `finset.prod` where needed. The duplication could be avoided by deducing the linear
case from the multilinear case via a currying isomorphism. However, this would mess up imports,
and it is more satisfactory to have the simplest case as a standalone proof. -/
instance [complete_space E₂] : complete_space (continuous_multilinear_map 𝕜 E₁ E₂) :=
begin
  have nonneg : ∀ (v : Π i, E₁ i), 0 ≤ ∏ i, ∥v i∥ :=
    λ v, finset.prod_nonneg (λ i hi, norm_nonneg _),
  -- We show that every Cauchy sequence converges.
  refine metric.complete_of_cauchy_seq_tendsto (λ f hf, _),
  -- We now expand out the definition of a Cauchy sequence,
  rcases cauchy_seq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩,
  -- and establish that the evaluation at any point `v : Π i, E₁ i` is Cauchy.
  have cau : ∀ v, cauchy_seq (λ n, f n v),
  { assume v,
    apply cauchy_seq_iff_le_tendsto_0.2 ⟨λ n, b n * ∏ i, ∥v i∥, λ n, _, _, _⟩,
    { exact mul_nonneg (b0 n) (nonneg v) },
    { assume n m N hn hm,
      rw dist_eq_norm,
      apply le_trans ((f n - f m).le_op_norm v) _,
      exact mul_le_mul_of_nonneg_right (b_bound n m N hn hm) (nonneg v) },
    { simpa using b_lim.mul tendsto_const_nhds } },
  -- We assemble the limits points of those Cauchy sequences
  -- (which exist as `E₂` is complete)
  -- into a function which we call `F`.
  choose F hF using λv, cauchy_seq_tendsto_of_complete (cau v),
  -- Next, we show that this `F` is multilinear,
  let Fmult : multilinear_map 𝕜 E₁ E₂ :=
  { to_fun := F,
    map_add' := λ v i x y, begin
      have A := hF (function.update v i (x + y)),
      have B := (hF (function.update v i x)).add (hF (function.update v i y)),
      simp at A B,
      exact tendsto_nhds_unique filter.at_top_ne_bot A B
    end,
    map_smul' := λ v i c x, begin
      have A := hF (function.update v i (c • x)),
      have B := filter.tendsto.smul (@tendsto_const_nhds _ ℕ _ c _) (hF (function.update v i x)),
      simp at A B,
      exact tendsto_nhds_unique filter.at_top_ne_bot A B
    end },
  -- and that `F` has norm at most `(b 0 + ∥f 0∥)`.
  have Fnorm : ∀ v, ∥F v∥ ≤ (b 0 + ∥f 0∥) * ∏ i, ∥v i∥,
  { assume v,
    have A : ∀ n, ∥f n v∥ ≤ (b 0 + ∥f 0∥) * ∏ i, ∥v i∥,
    { assume n,
      apply le_trans ((f n).le_op_norm _) _,
      apply mul_le_mul_of_nonneg_right _ (nonneg v),
      calc ∥f n∥ = ∥(f n - f 0) + f 0∥ : by { congr' 1, abel }
      ... ≤ ∥f n - f 0∥ + ∥f 0∥ : norm_add_le _ _
      ... ≤ b 0 + ∥f 0∥ : begin
        apply add_le_add_right,
        simpa [dist_eq_norm] using b_bound n 0 0 (zero_le _) (zero_le _)
      end },
    exact le_of_tendsto at_top_ne_bot (hF v).norm (eventually_of_forall _ A) },
  -- Thus `F` is continuous, and we propose that as the limit point of our original Cauchy sequence.
  let Fcont := Fmult.mk_continuous _ Fnorm,
  use Fcont,
  -- Our last task is to establish convergence to `F` in norm.
  have : ∀ n, ∥f n - Fcont∥ ≤ b n,
  { assume n,
    apply op_norm_le_bound _ (b0 n) (λ v, _),
    have A : ∀ᶠ m in at_top, ∥(f n - f m) v∥ ≤ b n * ∏ i, ∥v i∥,
    { refine eventually_at_top.2 ⟨n, λ m hm, _⟩,
      apply le_trans ((f n - f m).le_op_norm _) _,
      exact mul_le_mul_of_nonneg_right (b_bound n m n (le_refl _) hm) (nonneg v) },
    have B : tendsto (λ m, ∥(f n - f m) v∥) at_top (𝓝 (∥(f n - Fcont) v∥)) :=
      tendsto.norm (tendsto_const_nhds.sub (hF v)),
    exact le_of_tendsto at_top_ne_bot B A },
  erw tendsto_iff_norm_tendsto_zero,
  exact squeeze_zero (λ n, norm_nonneg _) this b_lim,
end

end continuous_multilinear_map

/-- If a continuous multilinear map is constructed from a multilinear map via the constructor
`mk_continuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
lemma multilinear_map.mk_continuous_norm_le (f : multilinear_map 𝕜 E₁ E₂) {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ m, ∥f m∥ ≤ C * ∏ i, ∥m i∥) : ∥f.mk_continuous C H∥ ≤ C :=
continuous_multilinear_map.op_norm_le_bound _ hC (λm, H m)

namespace continuous_multilinear_map

/-- Given a continuous multilinear map `f` on `n` variables (parameterized by `fin n`) and a subset
`s` of `k` of these variables, one gets a new continuous multilinear map on `fin k` by varying
these variables, and fixing the other ones equal to a given value `z`. It is denoted by
`f.restr s hk z`, where `hk` is a proof that the cardinality of `s` is `k`. The implicit
identification between `fin k` and `s` that we use is the canonical (increasing) bijection. -/
def restr {k n : ℕ} (f : (G [×n]→L[𝕜] E₂ : _))
  (s : finset (fin n)) (hk : s.card = k) (z : G) : G [×k]→L[𝕜] E₂ :=
(f.to_multilinear_map.restr s hk z).mk_continuous
(∥f∥ * ∥z∥^(n-k)) $ λ v, multilinear_map.restr_norm_le _ _ _ _ f.le_op_norm _

lemma norm_restr {k n : ℕ} (f : G [×n]→L[𝕜] E₂) (s : finset (fin n)) (hk : s.card = k) (z : G) :
  ∥f.restr s hk z∥ ≤ ∥f∥ * ∥z∥ ^ (n - k) :=
begin
  apply multilinear_map.mk_continuous_norm_le,
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
end

variables (𝕜 ι)

/-- The canonical continuous multilinear map on `𝕜^ι`, associating to `m` the product of all the
`m i` (multiplied by a fixed reference element `z` in the target module) -/
protected def mk_pi_field (z : E₂) : continuous_multilinear_map 𝕜 (λ(i : ι), 𝕜) E₂ :=
@multilinear_map.mk_continuous 𝕜 ι (λ(i : ι), 𝕜) E₂ _ _ _ _ _ _ _
  (multilinear_map.mk_pi_ring 𝕜 ι z) (∥z∥)
  (λ m, by simp only [multilinear_map.mk_pi_ring_apply, norm_smul, normed_field.norm_prod, mul_comm])

variables {𝕜 ι}

@[simp] lemma mk_pi_field_apply (z : E₂) (m : ι → 𝕜) :
  (continuous_multilinear_map.mk_pi_field 𝕜 ι z : (ι → 𝕜) → E₂) m = (∏ i, m i) • z := rfl

lemma mk_pi_ring_apply_one_eq_self (f : continuous_multilinear_map 𝕜 (λ(i : ι), 𝕜) E₂) :
  continuous_multilinear_map.mk_pi_field 𝕜 ι (f (λi, 1)) = f :=
begin
  ext m,
  have : m = (λi, m i • 1), by { ext j, simp },
  conv_rhs { rw [this, f.map_smul_univ] },
  refl
end

variables (𝕜 ι E₂)

/-- Continuous multilinear maps on `𝕜^n` with values in `E₂` are in bijection with `E₂`, as such a
continuous multilinear map is completely determined by its value on the constant vector made of
ones. We register this bijection as a linear equivalence in
`continuous_multilinear_map.pi_field_equiv_aux`. The continuous linear equivalence is
`continuous_multilinear_map.pi_field_equiv`. -/
protected def pi_field_equiv_aux : E₂ ≃ₗ[𝕜] (continuous_multilinear_map 𝕜 (λ(i : ι), 𝕜) E₂) :=
{ to_fun    := λ z, continuous_multilinear_map.mk_pi_field 𝕜 ι z,
  inv_fun   := λ f, f (λi, 1),
  map_add'  := λ z z', by { ext m, simp [smul_add] },
  map_smul' := λ c z, by { ext m, simp [smul_smul, mul_comm] },
  left_inv  := λ z, by simp,
  right_inv := λ f, f.mk_pi_ring_apply_one_eq_self }

/-- Continuous multilinear maps on `𝕜^n` with values in `E₂` are in bijection with `E₂`, as such a
continuous multilinear map is completely determined by its value on the constant vector made of
ones. We register this bijection as a continuous linear equivalence in
`continuous_multilinear_map.pi_field_equiv`. -/
protected def pi_field_equiv : E₂ ≃L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : ι), 𝕜) E₂) :=
{ continuous_to_fun := begin
    refine (continuous_multilinear_map.pi_field_equiv_aux 𝕜 ι E₂).to_linear_map.continuous_of_bound
      (1 : ℝ) (λz, _),
    rw one_mul,
    change ∥continuous_multilinear_map.mk_pi_field 𝕜 ι z∥ ≤ ∥z∥,
    exact multilinear_map.mk_continuous_norm_le _ (norm_nonneg _) _
  end,
  continuous_inv_fun := begin
    refine (continuous_multilinear_map.pi_field_equiv_aux 𝕜 ι E₂).symm.to_linear_map.continuous_of_bound
      (1 : ℝ) (λf, _),
    rw one_mul,
    change ∥f (λi, 1)∥ ≤ ∥f∥,
    apply @continuous_multilinear_map.unit_le_op_norm 𝕜 ι (λ (i : ι), 𝕜) E₂ _ _ _ _ _ _ _ f,
    simp [pi_norm_le_iff zero_le_one, le_refl]
  end,
  .. continuous_multilinear_map.pi_field_equiv_aux 𝕜 ι E₂ }

end continuous_multilinear_map


section currying
/-!
### Currying

We associate to a continuous multilinear map in `n+1` variables (i.e., based on `fin n.succ`) two
curried functions, named `f.curry_left` (which is a continuous linear map on `E 0` taking values
in continuous multilinear maps in `n` variables) and `f.curry_right` (which is a continuous
multilinear map in `n` variables taking values in continuous linear maps on `E (last n)`).
The inverse operations are called `uncurry_left` and `uncurry_right`.

We also register continuous linear equiv versions of these correspondences, in
`continuous_multilinear_curry_left_equiv` and `continuous_multilinear_curry_right_equiv`.
-/
open fin function

lemma continuous_linear_map.norm_map_tail_le
  (f : E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) (m : Πi, E i) :
  ∥f (m 0) (tail m)∥ ≤ ∥f∥ * ∏ i, ∥m i∥ :=
calc
  ∥f (m 0) (tail m)∥ ≤ ∥f (m 0)∥ * ∏ i, ∥(tail m) i∥ : (f (m 0)).le_op_norm _
  ... ≤ (∥f∥ * ∥m 0∥) * ∏ i, ∥(tail m) i∥ :
    mul_le_mul_of_nonneg_right (f.le_op_norm _) (prod_nonneg (λi hi, norm_nonneg _))
  ... = ∥f∥ * (∥m 0∥ * ∏ i, ∥(tail m) i∥) : by ring
  ... = ∥f∥ * ∏ i, ∥m i∥ : by { rw prod_univ_succ, refl }

lemma continuous_multilinear_map.norm_map_init_le
  (f : continuous_multilinear_map 𝕜 (λ(i : fin n), E i.cast_succ) (E (last n) →L[𝕜] E₂)) (m : Πi, E i) :
  ∥f (init m) (m (last n))∥ ≤ ∥f∥ * ∏ i, ∥m i∥ :=
calc
  ∥f (init m) (m (last n))∥ ≤ ∥f (init m)∥ * ∥m (last n)∥ : (f (init m)).le_op_norm _
  ... ≤ (∥f∥ * (∏ i, ∥(init m) i∥)) * ∥m (last n)∥ :
    mul_le_mul_of_nonneg_right (f.le_op_norm _) (norm_nonneg _)
  ... = ∥f∥ * ((∏ i, ∥(init m) i∥) * ∥m (last n)∥) : mul_assoc _ _ _
  ... = ∥f∥ * ∏ i, ∥m i∥ : by { rw prod_univ_cast_succ, refl }

lemma continuous_multilinear_map.norm_map_cons_le
  (f : continuous_multilinear_map 𝕜 E E₂) (x : E 0) (m : Π(i : fin n), E i.succ) :
  ∥f (cons x m)∥ ≤ ∥f∥ * ∥x∥ * ∏ i, ∥m i∥ :=
calc
  ∥f (cons x m)∥ ≤ ∥f∥ * ∏ i, ∥cons x m i∥ : f.le_op_norm _
  ... = (∥f∥ * ∥x∥) * ∏ i, ∥m i∥ : by { rw prod_univ_succ, simp [mul_assoc] }

lemma continuous_multilinear_map.norm_map_snoc_le
  (f : continuous_multilinear_map 𝕜 E E₂) (m : Π(i : fin n), E i.cast_succ) (x : E (last n)) :
  ∥f (snoc m x)∥ ≤ ∥f∥ * (∏ i, ∥m i∥) * ∥x∥ :=
calc
  ∥f (snoc m x)∥ ≤ ∥f∥ * ∏ i, ∥snoc m x i∥ : f.le_op_norm _
  ... = ∥f∥ * (∏ i, ∥m i∥) * ∥x∥ : by { rw prod_univ_cast_succ, simp [mul_assoc] }

/-! #### Left currying -/

/-- Given a continuous linear map `f` from `E 0` to continuous multilinear maps on `n` variables,
construct the corresponding continuous multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (m 0) (tail m)`-/
def continuous_linear_map.uncurry_left
  (f : E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) :
  continuous_multilinear_map 𝕜 E E₂ :=
(@linear_map.uncurry_left 𝕜 n E E₂ _ _ _ _ _
  (continuous_multilinear_map.to_multilinear_map_linear.comp f.to_linear_map)).mk_continuous
    (∥f∥) (λm, continuous_linear_map.norm_map_tail_le f m)

@[simp] lemma continuous_linear_map.uncurry_left_apply
  (f : E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) (m : Πi, E i) :
  f.uncurry_left m = f (m 0) (tail m) := rfl

/-- Given a continuous multilinear map `f` in `n+1` variables, split the first variable to obtain
a continuous linear map into continuous multilinear maps in `n` variables, given by
`x ↦ (m ↦ f (cons x m))`. -/
def continuous_multilinear_map.curry_left
  (f : continuous_multilinear_map 𝕜 E E₂) :
  E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂) :=
linear_map.mk_continuous
{ -- define a linear map into `n` continuous multilinear maps from an `n+1` continuous multilinear
  -- map
  to_fun    := λx, (f.to_multilinear_map.curry_left x).mk_continuous
    (∥f∥ * ∥x∥) (f.norm_map_cons_le x),
  map_add'  := λx y, by { ext m, exact f.cons_add m x y },
  map_smul' := λc x, by { ext m, exact f.cons_smul m c x } }
  -- then register its continuity thanks to its boundedness properties.
(∥f∥) (λx, multilinear_map.mk_continuous_norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _)

@[simp] lemma continuous_multilinear_map.curry_left_apply
  (f : continuous_multilinear_map 𝕜 E E₂) (x : E 0) (m : Π(i : fin n), E i.succ) :
  f.curry_left x m = f (cons x m) := rfl

@[simp] lemma continuous_linear_map.curry_uncurry_left
  (f : E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) :
  f.uncurry_left.curry_left = f :=
begin
  ext m x,
  simp only [tail_cons, continuous_linear_map.uncurry_left_apply,
             continuous_multilinear_map.curry_left_apply],
  rw cons_zero
end

@[simp] lemma continuous_multilinear_map.uncurry_curry_left
  (f : continuous_multilinear_map 𝕜 E E₂) : f.curry_left.uncurry_left = f :=
by { ext m, simp }

@[simp] lemma continuous_multilinear_map.curry_left_norm
  (f : continuous_multilinear_map 𝕜 E E₂) : ∥f.curry_left∥ = ∥f∥ :=
begin
  apply le_antisymm (linear_map.mk_continuous_norm_le _ (norm_nonneg _) _),
  have : ∥f.curry_left.uncurry_left∥ ≤ ∥f.curry_left∥ :=
    multilinear_map.mk_continuous_norm_le _ (norm_nonneg _) _,
  simpa
end

@[simp] lemma continuous_linear_map.uncurry_left_norm
  (f : E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) :
  ∥f.uncurry_left∥ = ∥f∥ :=
begin
  apply le_antisymm (multilinear_map.mk_continuous_norm_le _ (norm_nonneg _) _),
  have : ∥f.uncurry_left.curry_left∥ ≤ ∥f.uncurry_left∥ :=
    linear_map.mk_continuous_norm_le _ (norm_nonneg _) _,
  simpa
end

variables (𝕜 E E₂)

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), E i` is canonically isomorphic to
the space of continuous linear maps from `E 0` to the space of continuous multilinear maps on
`Π(i : fin n), E i.succ `, by separating the first variable. We register this isomorphism as a
linear isomorphism in `continuous_multilinear_curry_left_equiv_aux 𝕜 E E₂`.
The algebraic version (without continuity assumption on the maps) is
`multilinear_curry_left_equiv 𝕜 E E₂`, and the topological isomorphism (registering
additionally that the isomorphism is continuous) is
`continuous_multilinear_curry_left_equiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.uncurry_left` and `f.curry_left`. Use these
unless you need the full framework of linear equivs. -/
def continuous_multilinear_curry_left_equiv_aux :
  (E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) ≃ₗ[𝕜]
  (continuous_multilinear_map 𝕜 E E₂) :=
{ to_fun    := continuous_linear_map.uncurry_left,
  map_add'  := λf₁ f₂, by { ext m, refl },
  map_smul' := λc f, by { ext m, refl },
  inv_fun   := continuous_multilinear_map.curry_left,
  left_inv  := continuous_linear_map.curry_uncurry_left,
  right_inv := continuous_multilinear_map.uncurry_curry_left }

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), E i` is canonically isomorphic to
the space of continuous linear maps from `E 0` to the space of continuous multilinear maps on
`Π(i : fin n), E i.succ `, by separating the first variable. We register this isomorphism in
`continuous_multilinear_curry_left_equiv 𝕜 E E₂`. The algebraic version (without topology) is given
in `multilinear_curry_left_equiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.uncurry_left` and `f.curry_left`. Use these
unless you need the full framework of continuous linear equivs. -/
def continuous_multilinear_curry_left_equiv :
  (E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) ≃L[𝕜]
  (continuous_multilinear_map 𝕜 E E₂) :=
{ continuous_to_fun := begin
    refine (continuous_multilinear_curry_left_equiv_aux 𝕜 E E₂).to_linear_map.continuous_of_bound
      (1 : ℝ) (λf, le_of_eq _),
    rw one_mul,
    exact f.uncurry_left_norm
  end,
  continuous_inv_fun := begin
    refine (continuous_multilinear_curry_left_equiv_aux 𝕜 E E₂).symm.to_linear_map.continuous_of_bound
      (1 : ℝ) (λf, le_of_eq _),
    rw one_mul,
    exact f.curry_left_norm
  end,
  .. continuous_multilinear_curry_left_equiv_aux 𝕜 E E₂ }

variables {𝕜 E E₂}

@[simp] lemma continuous_multilinear_curry_left_equiv_apply
  (f : E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) (v : Π i, E i) :
  continuous_multilinear_curry_left_equiv 𝕜 E E₂ f v = f (v 0) (tail v) := rfl

@[simp] lemma continuous_multilinear_curry_left_equiv_symm_apply
  (f : continuous_multilinear_map 𝕜 E E₂) (x : E 0) (v : Π (i : fin n), E i.succ) :
  (continuous_multilinear_curry_left_equiv 𝕜 E E₂).symm f x v = f (cons x v) := rfl

/-! #### Right currying -/

/-- Given a continuous linear map `f` from continuous multilinear maps on `n` variables to
continuous linear maps on `E 0`, construct the corresponding continuous multilinear map on `n+1`
variables obtained by concatenating the variables, given by `m ↦ f (init m) (m (last n))`. -/
def continuous_multilinear_map.uncurry_right
  (f : continuous_multilinear_map 𝕜 (λ(i : fin n), E i.cast_succ) (E (last n) →L[𝕜] E₂)) :
  continuous_multilinear_map 𝕜 E E₂ :=
let f' : multilinear_map 𝕜 (λ(i : fin n), E i.cast_succ) (E (last n) →ₗ[𝕜] E₂) :=
{ to_fun    := λ m, (f m).to_linear_map,
  map_add'  := λ m i x y, by { simp, refl },
  map_smul' := λ m i c x, by { simp, refl } } in
(@multilinear_map.uncurry_right 𝕜 n E E₂ _ _ _ _ _ f').mk_continuous
  (∥f∥) (λm, f.norm_map_init_le m)

@[simp] lemma continuous_multilinear_map.uncurry_right_apply
  (f : continuous_multilinear_map 𝕜 (λ(i : fin n), E i.cast_succ) (E (last n) →L[𝕜] E₂)) (m : Πi, E i) :
  f.uncurry_right m = f (init m) (m (last n)) := rfl

/-- Given a continuous multilinear map `f` in `n+1` variables, split the last variable to obtain
a continuous multilinear map in `n` variables into continuous linear maps, given by
`m ↦ (x ↦ f (snoc m x))`. -/
def continuous_multilinear_map.curry_right
  (f : continuous_multilinear_map 𝕜 E E₂) :
  continuous_multilinear_map 𝕜 (λ(i : fin n), E i.cast_succ) (E (last n) →L[𝕜] E₂) :=
let f' : multilinear_map 𝕜 (λ(i : fin n), E i.cast_succ) (E (last n) →L[𝕜] E₂) :=
{ to_fun    := λm, (f.to_multilinear_map.curry_right m).mk_continuous
    (∥f∥ * ∏ i, ∥m i∥) $ λx, f.norm_map_snoc_le m x,
  map_add'  := λ m i x y, by { simp, refl },
  map_smul' := λ m i c x, by { simp, refl } } in
f'.mk_continuous (∥f∥) (λm, linear_map.mk_continuous_norm_le _
  (mul_nonneg (norm_nonneg _) (prod_nonneg (λj hj, norm_nonneg _))) _)

@[simp] lemma continuous_multilinear_map.curry_right_apply
  (f : continuous_multilinear_map 𝕜 E E₂) (m : Π(i : fin n), E i.cast_succ) (x : E (last n)) :
  f.curry_right m x = f (snoc m x) := rfl

@[simp] lemma continuous_multilinear_map.curry_uncurry_right
  (f : continuous_multilinear_map 𝕜 (λ(i : fin n), E i.cast_succ) (E (last n) →L[𝕜] E₂)) :
  f.uncurry_right.curry_right = f :=
begin
  ext m x,
  simp only [snoc_last, continuous_multilinear_map.curry_right_apply,
             continuous_multilinear_map.uncurry_right_apply],
  rw init_snoc
end

@[simp] lemma continuous_multilinear_map.uncurry_curry_right
  (f : continuous_multilinear_map 𝕜 E E₂) : f.curry_right.uncurry_right = f :=
by { ext m, simp }

@[simp] lemma continuous_multilinear_map.curry_right_norm
  (f : continuous_multilinear_map 𝕜 E E₂) : ∥f.curry_right∥ = ∥f∥ :=
begin
  refine le_antisymm (multilinear_map.mk_continuous_norm_le _ (norm_nonneg _) _) _,
  have : ∥f.curry_right.uncurry_right∥ ≤ ∥f.curry_right∥ :=
    multilinear_map.mk_continuous_norm_le _ (norm_nonneg _) _,
  simpa
end

@[simp] lemma continuous_multilinear_map.uncurry_right_norm
  (f : continuous_multilinear_map 𝕜 (λ(i : fin n), E i.cast_succ) (E (last n) →L[𝕜] E₂)) :
  ∥f.uncurry_right∥ = ∥f∥ :=
begin
  refine le_antisymm (multilinear_map.mk_continuous_norm_le _ (norm_nonneg _) _) _,
  have : ∥f.uncurry_right.curry_right∥ ≤ ∥f.uncurry_right∥ :=
    multilinear_map.mk_continuous_norm_le _ (norm_nonneg _) _,
  simpa
end

variables (𝕜 E E₂)

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), E i` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : fin n), E i.cast_succ` with values in the space
of continuous linear maps on `E (last n)`, by separating the last variable. We register this
isomorphism as a linear equiv in `continuous_multilinear_curry_right_equiv_aux 𝕜 E E₂`.
The algebraic version (without continuity assumption on the maps) is
`multilinear_curry_right_equiv 𝕜 E E₂`, and the topological isomorphism (registering
additionally that the isomorphism is continuous) is
`continuous_multilinear_curry_right_equiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of linear equivs. -/
def continuous_multilinear_curry_right_equiv_aux :
  (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.cast_succ) (E (last n) →L[𝕜] E₂)) ≃ₗ[𝕜]
  (continuous_multilinear_map 𝕜 E E₂) :=
{ to_fun    := continuous_multilinear_map.uncurry_right,
  map_add'  := λf₁ f₂, by { ext m, refl },
  map_smul' := λc f, by { ext m, refl },
  inv_fun   := continuous_multilinear_map.curry_right,
  left_inv  := continuous_multilinear_map.curry_uncurry_right,
  right_inv := continuous_multilinear_map.uncurry_curry_right }

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), E i` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : fin n), E i.cast_succ` with values in the space
of continuous linear maps on `E (last n)`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuous_multilinear_curry_right_equiv 𝕜 E E₂`.
The algebraic version (without topology) is given in `multilinear_curry_right_equiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of continuous linear equivs. -/
def continuous_multilinear_curry_right_equiv :
  (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.cast_succ) (E (last n) →L[𝕜] E₂)) ≃L[𝕜]
  (continuous_multilinear_map 𝕜 E E₂) :=
{ continuous_to_fun := begin
    refine (continuous_multilinear_curry_right_equiv_aux 𝕜 E E₂).to_linear_map.continuous_of_bound
      (1 : ℝ) (λf, le_of_eq _),
    rw one_mul,
    exact f.uncurry_right_norm
  end,
  continuous_inv_fun := begin
    refine (continuous_multilinear_curry_right_equiv_aux 𝕜 E E₂).symm.to_linear_map.continuous_of_bound
      (1 : ℝ) (λf, le_of_eq _),
    rw one_mul,
    exact f.curry_right_norm
  end,
  .. continuous_multilinear_curry_right_equiv_aux 𝕜 E E₂ }

variables {𝕜 G E E₂}

@[simp] lemma continuous_multilinear_curry_right_equiv_apply
  (f : (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.cast_succ) (E (last n) →L[𝕜] E₂)))
  (v : Π i, E i) :
  (continuous_multilinear_curry_right_equiv 𝕜 E E₂) f v = f (init v) (v (last n)) := rfl

@[simp] lemma continuous_multilinear_curry_right_equiv_symm_apply
  (f : continuous_multilinear_map 𝕜 E E₂)
  (v : Π (i : fin n), E i.cast_succ) (x : E (last n)) :
  (continuous_multilinear_curry_right_equiv 𝕜 E E₂).symm f v x = f (snoc v x) := rfl


/-!
#### Currying with `0` variables

The space of multilinear maps with `0` variables is trivial: such a multilinear map is just an
arbitrary constant (note that multilinear maps in `0` variables need not map `0` to `0`!).
Therefore, the space of continuous multilinear maps on `(fin 0) → G` with values in `E₂` is
isomorphic (and even isometric) to `E₂`. As this is the zeroth step in the construction of iterated
derivatives, we register this isomorphism. -/

variables {𝕜 G E₂}

/-- Associating to a continuous multilinear map in `0` variables the unique value it takes. -/
def continuous_multilinear_map.uncurry0
  (f : continuous_multilinear_map 𝕜 (λ (i : fin 0), G) E₂) : E₂ := f 0

variables (𝕜 G)
/-- Associating to an element `x` of a vector space `E₂` the continuous multilinear map in `0`
variables taking the (unique) value `x` -/
def continuous_multilinear_map.curry0 (x : E₂) :
  continuous_multilinear_map 𝕜 (λ (i : fin 0), G) E₂ :=
{ to_fun    := λm, x,
  map_add'  := λ m i, fin.elim0 i,
  map_smul' := λ m i, fin.elim0 i,
  cont      := continuous_const }

variable {G}
@[simp] lemma continuous_multilinear_map.curry0_apply (x : E₂) (m : (fin 0) → G) :
  (continuous_multilinear_map.curry0 𝕜 G x : ((fin 0) → G) → E₂) m = x := rfl

variable {𝕜}
@[simp] lemma continuous_multilinear_map.uncurry0_apply
  (f : continuous_multilinear_map 𝕜 (λ (i : fin 0), G) E₂) :
  f.uncurry0 = f 0 := rfl

@[simp] lemma continuous_multilinear_map.apply_zero_curry0
  (f : continuous_multilinear_map 𝕜 (λ (i : fin 0), G) E₂) {x : fin 0 → G} :
  continuous_multilinear_map.curry0 𝕜 G (f x) = f :=
by { ext m, simp [(subsingleton.elim _ _ : x = m)] }

lemma continuous_multilinear_map.uncurry0_curry0
  (f : continuous_multilinear_map 𝕜 (λ (i : fin 0), G) E₂) :
  continuous_multilinear_map.curry0 𝕜 G (f.uncurry0) = f :=
by simp

variables (𝕜 G)
@[simp] lemma continuous_multilinear_map.curry0_uncurry0 (x : E₂) :
  (continuous_multilinear_map.curry0 𝕜 G x).uncurry0 = x := rfl

@[simp] lemma continuous_multilinear_map.uncurry0_norm (x : E₂)  :
  ∥continuous_multilinear_map.curry0 𝕜 G x∥ = ∥x∥ :=
begin
  apply le_antisymm,
  { exact continuous_multilinear_map.op_norm_le_bound _ (norm_nonneg _) (λm, by simp) },
  { simpa using (continuous_multilinear_map.curry0 𝕜 G x).le_op_norm 0 }
end

variables {𝕜 G}
@[simp] lemma continuous_multilinear_map.fin0_apply_norm
  (f : continuous_multilinear_map 𝕜 (λ (i : fin 0), G) E₂) {x : fin 0 → G} :
  ∥f x∥ = ∥f∥ :=
begin
  have : x = 0 := subsingleton.elim _ _, subst this,
  refine le_antisymm (by simpa using f.le_op_norm 0) _,
  have : ∥continuous_multilinear_map.curry0 𝕜 G (f.uncurry0)∥ ≤ ∥f.uncurry0∥ :=
    continuous_multilinear_map.op_norm_le_bound _ (norm_nonneg _) (λm,
      by simp [-continuous_multilinear_map.apply_zero_curry0]),
  simpa
end

lemma continuous_multilinear_map.curry0_norm
  (f : continuous_multilinear_map 𝕜 (λ (i : fin 0), G) E₂) : ∥f.uncurry0∥ = ∥f∥ :=
by simp

variables (𝕜 G E₂)
/-- The linear isomorphism between elements of a normed space, and continuous multilinear maps in
`0` variables with values in this normed space. The continuous version is given in
`continuous_multilinear_curry_fin0`.

The direct and inverse maps are `uncurry0` and `curry0`. Use these unless you need the full
framework of linear equivs. -/
def continuous_multilinear_curry_fin0_aux :
  (continuous_multilinear_map 𝕜 (λ (i : fin 0), G) E₂) ≃ₗ[𝕜] E₂ :=
{ to_fun    := λf, continuous_multilinear_map.uncurry0 f,
  inv_fun   := λf, continuous_multilinear_map.curry0 𝕜 G f,
  map_add'  := λf g, rfl,
  map_smul' := λc f, rfl,
  left_inv  := continuous_multilinear_map.uncurry0_curry0,
  right_inv := continuous_multilinear_map.curry0_uncurry0 𝕜 G }

/-- The continuous linear isomorphism between elements of a normed space, and continuous multilinear
maps in `0` variables with values in this normed space.

The direct and inverse maps are `uncurry0` and `curry0`. Use these unless you need the full
framework of continuous linear equivs. -/
def continuous_multilinear_curry_fin0 :
  (continuous_multilinear_map 𝕜 (λ (i : fin 0), G) E₂) ≃L[𝕜] E₂ :=
{ continuous_to_fun := begin
    change continuous (λ (f : continuous_multilinear_map 𝕜 (λ (i : fin 0), G) E₂),
      (f : ((fin 0) → G) → E₂) 0),
    exact continuous_multilinear_map.continuous_eval.comp (continuous_id.prod_mk continuous_const)
  end,
  continuous_inv_fun := begin
    refine (continuous_multilinear_curry_fin0_aux 𝕜 G E₂).symm.to_linear_map.continuous_of_bound
      (1 : ℝ) (λf, le_of_eq _),
    rw one_mul,
    exact continuous_multilinear_map.uncurry0_norm _ _ _
  end,
  .. continuous_multilinear_curry_fin0_aux 𝕜 G E₂ }

variables {𝕜 G E₂}

@[simp] lemma continuous_multilinear_curry_fin0_apply
  (f : (continuous_multilinear_map 𝕜 (λ (i : fin 0), G) E₂)) :
  continuous_multilinear_curry_fin0 𝕜 G E₂ f = f 0 := rfl

@[simp] lemma continuous_multilinear_curry_fin0_symm_apply
  (x : E₂) (v : (fin 0) → G) :
  (continuous_multilinear_curry_fin0 𝕜 G E₂).symm x v = x := rfl

/-! #### With 1 variable -/

variables (𝕜 G E₂)

/-- Continuous multilinear maps from `G^1` to `E₂` are isomorphic with continuous linear maps from
`G` to `E₂`. -/
def continuous_multilinear_curry_fin1 :
  (continuous_multilinear_map 𝕜 (λ (i : fin 1), G) E₂) ≃L[𝕜] (G →L[𝕜] E₂) :=
(continuous_multilinear_curry_right_equiv 𝕜 (λ (i : fin 1), G) E₂).symm.trans
(continuous_multilinear_curry_fin0 𝕜 G (G →L[𝕜] E₂))

variables {𝕜 G E₂}

@[simp] lemma continuous_multilinear_curry_fin1_apply
  (f : (continuous_multilinear_map 𝕜 (λ (i : fin 1), G) E₂)) (x : G) :
  continuous_multilinear_curry_fin1 𝕜 G E₂ f x = f (fin.snoc 0 x) := rfl

@[simp] lemma continuous_multilinear_curry_fin1_symm_apply
  (f : G →L[𝕜] E₂) (v : (fin 1) → G) :
  (continuous_multilinear_curry_fin1 𝕜 G E₂).symm f v = f (v 0) := rfl

end currying
