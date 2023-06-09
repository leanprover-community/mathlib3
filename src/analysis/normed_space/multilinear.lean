/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.normed_space.operator_norm
import topology.algebra.module.multilinear

/-!
# Operator norm on the space of continuous multilinear maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

When `f` is a continuous multilinear map in finitely many variables, we define its norm `‖f‖` as the
smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for all `m`.

We show that it is indeed a norm, and prove its basic properties.

## Main results

Let `f` be a multilinear map in finitely many variables.
* `exists_bound_of_continuous` asserts that, if `f` is continuous, then there exists `C > 0`
  with `‖f m‖ ≤ C * ∏ i, ‖m i‖` for all `m`.
* `continuous_of_bound`, conversely, asserts that this bound implies continuity.
* `mk_continuous` constructs the associated continuous multilinear map.

Let `f` be a continuous multilinear map in finitely many variables.
* `‖f‖` is its norm, i.e., the smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for
  all `m`.
* `le_op_norm f m` asserts the fundamental inequality `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖`.
* `norm_image_sub_le f m₁ m₂` gives a control of the difference `f m₁ - f m₂` in terms of
  `‖f‖` and `‖m₁ - m₂‖`.

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
open_locale big_operators nnreal
open finset metric

local attribute [instance, priority 1001]
add_comm_group.to_add_comm_monoid normed_add_comm_group.to_add_comm_group normed_space.to_module'

/-!
### Type variables

We use the following type variables in this file:

* `𝕜` : a `nontrivially_normed_field`;
* `ι`, `ι'` : finite index types with decidable equality;
* `E`, `E₁` : families of normed vector spaces over `𝕜` indexed by `i : ι`;
* `E'` : a family of normed vector spaces over `𝕜` indexed by `i' : ι'`;
* `Ei` : a family of normed vector spaces over `𝕜` indexed by `i : fin (nat.succ n)`;
* `G`, `G'` : normed vector spaces over `𝕜`.
-/

universes u v v' wE wE₁ wE' wEi wG wG'
variables {𝕜 : Type u} {ι : Type v} {ι' : Type v'} {n : ℕ}
  {E : ι → Type wE} {E₁ : ι → Type wE₁} {E' : ι' → Type wE'} {Ei : fin n.succ → Type wEi}
  {G : Type wG} {G' : Type wG'}
  [fintype ι] [fintype ι'] [nontrivially_normed_field 𝕜]
  [Π i, normed_add_comm_group (E i)] [Π i, normed_space 𝕜 (E i)]
  [Π i, normed_add_comm_group (E₁ i)] [Π i, normed_space 𝕜 (E₁ i)]
  [Π i, normed_add_comm_group (E' i)] [Π i, normed_space 𝕜 (E' i)]
  [Π i, normed_add_comm_group (Ei i)] [Π i, normed_space 𝕜 (Ei i)]
  [normed_add_comm_group G] [normed_space 𝕜 G] [normed_add_comm_group G'] [normed_space 𝕜 G']

/-!
### Continuity properties of multilinear maps

We relate continuity of multilinear maps to the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, in
both directions. Along the way, we prove useful bounds on the difference `‖f m₁ - f m₂‖`.
-/
namespace multilinear_map

variable (f : multilinear_map 𝕜 E G)

/-- If a multilinear map in finitely many variables on normed spaces satisfies the inequality
`‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i` for some positive numbers `ε i`
and elements `c i : 𝕜`, `1 < ‖c i‖`, then it satisfies this inequality for all `m`. -/
lemma bound_of_shell {ε : ι → ℝ} {C : ℝ} (hε : ∀ i, 0 < ε i) {c : ι → 𝕜} (hc : ∀ i, 1 < ‖c i‖)
  (hf : ∀ m : Π i, E i, (∀ i, ε i / ‖c i‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε i) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
  (m : Π i, E i) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
begin
  rcases em (∃ i, m i = 0) with ⟨i, hi⟩|hm; [skip, push_neg at hm],
  { simp [f.map_coord_zero i hi, prod_eq_zero (mem_univ i), hi] },
  choose δ hδ0 hδm_lt hle_δm hδinv using λ i, rescale_to_shell (hc i) (hε i) (hm i),
  have hδ0 : 0 < ∏ i, ‖δ i‖, from prod_pos (λ i _, norm_pos_iff.2 (hδ0 i)),
  simpa [map_smul_univ, norm_smul, prod_mul_distrib, mul_left_comm C, mul_le_mul_left hδ0]
    using hf (λ i, δ i • m i) hle_δm hδm_lt,
end

/-- If a multilinear map in finitely many variables on normed spaces is continuous, then it
satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, for some `C` which can be chosen to be
positive. -/
theorem exists_bound_of_continuous (hf : continuous f) :
  ∃ (C : ℝ), 0 < C ∧ (∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :=
begin
  casesI is_empty_or_nonempty ι,
  { refine ⟨‖f 0‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, λ m, _⟩,
    obtain rfl : m = 0, from funext (is_empty.elim ‹_›),
    simp [univ_eq_empty, zero_le_one] },
  obtain ⟨ε : ℝ, ε0 : 0 < ε, hε : ∀ m : Π i, E i, ‖m - 0‖ < ε → ‖f m - f 0‖ < 1⟩ :=
    normed_add_comm_group.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one,
  simp only [sub_zero, f.map_zero] at hε,
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  have : 0 < (‖c‖ / ε) ^ fintype.card ι, from pow_pos (div_pos (zero_lt_one.trans hc) ε0) _,
  refine ⟨_, this, _⟩,
  refine f.bound_of_shell (λ _, ε0) (λ _, hc) (λ m hcm hm, _),
  refine (hε m ((pi_norm_lt_iff ε0).2 hm)).le.trans _,
  rw [← div_le_iff' this, one_div, ← inv_pow, inv_div, fintype.card, ← prod_const],
  exact prod_le_prod (λ _ _, div_nonneg ε0.le (norm_nonneg _)) (λ i _, hcm i)
end

/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a precise but hard to use version. See
`norm_image_sub_le_of_bound` for a less precise but more usable version. The bound reads
`‖f m - f m'‖ ≤
  C * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
lemma norm_image_sub_le_of_bound' [decidable_eq ι] {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : Πi, E i) :
  ‖f m₁ - f m₂‖ ≤
  C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
begin
  have A : ∀(s : finset ι), ‖f m₁ - f (s.piecewise m₂ m₁)‖
    ≤ C * ∑ i in s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖,
  { refine finset.induction (by simp) _,
    assume i s his Hrec,
    have I : ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖
      ≤ C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖,
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
    calc ‖f m₁ - f ((insert i s).piecewise m₂ m₁)‖ ≤
      ‖f m₁ - f (s.piecewise m₂ m₁)‖ + ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ :
        by { rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm], exact dist_triangle _ _ _ }
      ... ≤ (C * ∑ i in s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖)
            + C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :
        add_le_add Hrec I
      ... = C * ∑ i in insert i s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :
        by simp [his, add_comm, left_distrib] },
  convert A univ,
  simp
end

/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a usable but not very precise version. See
`norm_image_sub_le_of_bound'` for a more precise but less usable version. The bound is
`‖f m - f m'‖ ≤ C * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`. -/
lemma norm_image_sub_le_of_bound {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : Πi, E i) :
  ‖f m₁ - f m₂‖ ≤ C * (fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (fintype.card ι - 1) * ‖m₁ - m₂‖ :=
begin
  letI := classical.dec_eq ι,
  have A : ∀ (i : ι), ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖)
    ≤ ‖m₁ - m₂‖ * (max ‖m₁‖ ‖m₂‖) ^ (fintype.card ι - 1),
  { assume i,
    calc ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖)
    ≤ ∏ j : ι, function.update (λ j, max ‖m₁‖ ‖m₂‖) i (‖m₁ - m₂‖) j :
      begin
        apply prod_le_prod,
        { assume j hj, by_cases h : j = i; simp [h, norm_nonneg] },
        { assume j hj,
          by_cases h : j = i,
          { rw h, simp, exact norm_le_pi_norm (m₁ - m₂) i },
          { simp [h, max_le_max, norm_le_pi_norm (_ : Π i, E i)] } }
      end
    ... = ‖m₁ - m₂‖ * (max ‖m₁‖ ‖m₂‖) ^ (fintype.card ι - 1) :
      by { rw prod_update_of_mem (finset.mem_univ _), simp [card_univ_diff] } },
  calc
  ‖f m₁ - f m₂‖
  ≤ C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :
    f.norm_image_sub_le_of_bound' hC H m₁ m₂
  ... ≤ C * ∑ i, ‖m₁ - m₂‖ * (max ‖m₁‖ ‖m₂‖) ^ (fintype.card ι - 1) :
    mul_le_mul_of_nonneg_left (sum_le_sum (λi hi, A i)) hC
  ... = C * (fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (fintype.card ι - 1) * ‖m₁ - m₂‖ :
    by { rw [sum_const, card_univ, nsmul_eq_mul], ring }
end

/-- If a multilinear map satisfies an inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, then it is
continuous. -/
theorem continuous_of_bound (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
  continuous f :=
begin
  let D := max C 1,
  have D_pos : 0 ≤ D := le_trans zero_le_one (le_max_right _ _),
  replace H : ∀ m, ‖f m‖ ≤ D * ∏ i, ‖m i‖,
  { assume m,
    apply le_trans (H m) (mul_le_mul_of_nonneg_right (le_max_left _ _) _),
    exact prod_nonneg (λ(i : ι) hi, norm_nonneg (m i)) },
  refine continuous_iff_continuous_at.2 (λm, _),
  refine continuous_at_of_locally_lipschitz zero_lt_one
    (D * (fintype.card ι) * (‖m‖ + 1) ^ (fintype.card ι - 1)) (λm' h', _),
  rw [dist_eq_norm, dist_eq_norm],
  have : 0 ≤ (max ‖m'‖ ‖m‖), by simp,
  have : (max ‖m'‖ ‖m‖) ≤ ‖m‖ + 1,
    by simp [zero_le_one, norm_le_of_mem_closed_ball (le_of_lt h'), -add_comm],
  calc
    ‖f m' - f m‖
    ≤ D * (fintype.card ι) * (max ‖m'‖ ‖m‖) ^ (fintype.card ι - 1) * ‖m' - m‖ :
      f.norm_image_sub_le_of_bound D_pos H m' m
    ... ≤ D * (fintype.card ι) * (‖m‖ + 1) ^ (fintype.card ι - 1) * ‖m' - m‖ :
      by apply_rules [mul_le_mul_of_nonneg_right, mul_le_mul_of_nonneg_left, mul_nonneg,
        norm_nonneg, nat.cast_nonneg, pow_le_pow_of_le_left]
end

/-- Constructing a continuous multilinear map from a multilinear map satisfying a boundedness
condition. -/
def mk_continuous (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
  continuous_multilinear_map 𝕜 E G :=
{ cont := f.continuous_of_bound C H, ..f }

@[simp] lemma coe_mk_continuous (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
  ⇑(f.mk_continuous C H) = f :=
rfl

/-- Given a multilinear map in `n` variables, if one restricts it to `k` variables putting `z` on
the other coordinates, then the resulting restricted function satisfies an inequality
`‖f.restr v‖ ≤ C * ‖z‖^(n-k) * Π ‖v i‖` if the original function satisfies `‖f v‖ ≤ C * Π ‖v i‖`. -/
lemma restr_norm_le {k n : ℕ} (f : (multilinear_map 𝕜 (λ i : fin n, G) G' : _))
  (s : finset (fin n)) (hk : s.card = k) (z : G) {C : ℝ}
  (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (v : fin k → G) :
  ‖f.restr s hk z v‖ ≤ C * ‖z‖ ^ (n - k) * ∏ i, ‖v i‖ :=
begin
  rw [mul_right_comm, mul_assoc],
  convert H _ using 2,
  simp only [apply_dite norm, fintype.prod_dite, prod_const (‖z‖), finset.card_univ,
    fintype.card_of_subtype sᶜ (λ x, mem_compl), card_compl, fintype.card_fin, hk, mk_coe,
    ← (s.order_iso_of_fin hk).symm.bijective.prod_comp (λ x, ‖v x‖)],
  refl
end

end multilinear_map

/-!
### Continuous multilinear maps

We define the norm `‖f‖` of a continuous multilinear map `f` in finitely many variables as the
smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for all `m`. We show that this
defines a normed space structure on `continuous_multilinear_map 𝕜 E G`.
-/
namespace continuous_multilinear_map

variables (c : 𝕜) (f g : continuous_multilinear_map 𝕜 E G) (m : Πi, E i)

theorem bound : ∃ (C : ℝ), 0 < C ∧ (∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :=
f.to_multilinear_map.exists_bound_of_continuous f.2

open real

/-- The operator norm of a continuous multilinear map is the inf of all its bounds. -/
def op_norm := Inf {c | 0 ≤ (c : ℝ) ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖}
instance has_op_norm : has_norm (continuous_multilinear_map 𝕜 E G) := ⟨op_norm⟩

/-- An alias of `continuous_multilinear_map.has_op_norm` with non-dependent types to help typeclass
search. -/
instance has_op_norm' : has_norm (continuous_multilinear_map 𝕜 (λ (i : ι), G) G') :=
continuous_multilinear_map.has_op_norm

lemma norm_def : ‖f‖ = Inf {c | 0 ≤ (c : ℝ) ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} := rfl

-- So that invocations of `le_cInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty {f : continuous_multilinear_map 𝕜 E G} :
  ∃ c, c ∈ {c | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} :=
let ⟨M, hMp, hMb⟩ := f.bound in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below {f : continuous_multilinear_map 𝕜 E G} :
  bdd_below {c | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma op_norm_nonneg : 0 ≤ ‖f‖ :=
le_cInf bounds_nonempty (λ _ ⟨hx, _⟩, hx)

/-- The fundamental property of the operator norm of a continuous multilinear map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`. -/
theorem le_op_norm : ‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖ :=
begin
  have A : 0 ≤ ∏ i, ‖m i‖ := prod_nonneg (λj hj, norm_nonneg _),
  cases A.eq_or_lt with h hlt,
  { rcases prod_eq_zero_iff.1 h.symm with ⟨i, _, hi⟩,
    rw norm_eq_zero at hi,
    have : f m = 0 := f.map_coord_zero i hi,
    rw [this, norm_zero],
    exact mul_nonneg (op_norm_nonneg f) A },
  { rw [← div_le_iff hlt],
    apply le_cInf bounds_nonempty,
    rintro c ⟨_, hc⟩, rw [div_le_iff hlt], apply hc }
end

theorem le_of_op_norm_le {C : ℝ} (h : ‖f‖ ≤ C) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
(f.le_op_norm m).trans $ mul_le_mul_of_nonneg_right h (prod_nonneg $ λ i _, norm_nonneg (m i))

lemma ratio_le_op_norm : ‖f m‖ / ∏ i, ‖m i‖ ≤ ‖f‖ :=
div_le_of_nonneg_of_le_mul (prod_nonneg $ λ i _, norm_nonneg _) (op_norm_nonneg _) (f.le_op_norm m)

/-- The image of the unit ball under a continuous multilinear map is bounded. -/
lemma unit_le_op_norm (h : ‖m‖ ≤ 1) : ‖f m‖ ≤ ‖f‖ :=
calc
  ‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖ : f.le_op_norm m
  ... ≤ ‖f‖ * ∏ i : ι, 1 :
    mul_le_mul_of_nonneg_left (prod_le_prod (λi hi, norm_nonneg _)
      (λi hi, le_trans (norm_le_pi_norm (_ : Π i, E i) _) h)) (op_norm_nonneg f)
  ... = ‖f‖ : by simp

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
lemma op_norm_le_bound {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ m, ‖f m‖ ≤ M * ∏ i, ‖m i‖) :
  ‖f‖ ≤ M :=
cInf_le bounds_bdd_below ⟨hMp, hM⟩

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
cInf_le bounds_bdd_below
  ⟨add_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x, by { rw add_mul,
    exact norm_add_le_of_le (le_op_norm _ _) (le_op_norm _ _) }⟩

lemma op_norm_zero : ‖(0 : continuous_multilinear_map 𝕜 E G)‖ = 0 :=
(op_norm_nonneg _).antisymm' $ op_norm_le_bound 0 le_rfl $ λ m, by simp

/-- A continuous linear map is zero iff its norm vanishes. -/
theorem op_norm_zero_iff : ‖f‖ = 0 ↔ f = 0 :=
⟨λ h, by { ext m, simpa [h] using f.le_op_norm m }, by { rintro rfl, exact op_norm_zero }⟩

section
variables {𝕜' : Type*} [normed_field 𝕜'] [normed_space 𝕜' G] [smul_comm_class 𝕜 𝕜' G]

lemma op_norm_smul_le (c : 𝕜') : ‖c • f‖ ≤ ‖c‖ * ‖f‖ :=
(c • f).op_norm_le_bound
  (mul_nonneg (norm_nonneg _) (op_norm_nonneg _))
  begin
    intro m,
    erw [norm_smul, mul_assoc],
    exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)
  end

lemma op_norm_neg : ‖-f‖ = ‖f‖ := by { rw norm_def, apply congr_arg, ext, simp }

/-- Continuous multilinear maps themselves form a normed space with respect to
    the operator norm. -/
instance normed_add_comm_group : normed_add_comm_group (continuous_multilinear_map 𝕜 E G) :=
add_group_norm.to_normed_add_comm_group
{ to_fun := norm,
  map_zero' := op_norm_zero,
  neg' := op_norm_neg,
  add_le' := op_norm_add_le,
  eq_zero_of_map_eq_zero' := λ f, f.op_norm_zero_iff.1 }

/-- An alias of `continuous_multilinear_map.normed_add_comm_group` with non-dependent types to help
typeclass search. -/
instance normed_add_comm_group' :
  normed_add_comm_group (continuous_multilinear_map 𝕜 (λ i : ι, G) G') :=
continuous_multilinear_map.normed_add_comm_group

instance normed_space : normed_space 𝕜' (continuous_multilinear_map 𝕜 E G) :=
⟨λ c f, f.op_norm_smul_le c⟩

/-- An alias of `continuous_multilinear_map.normed_space` with non-dependent types to help typeclass
search. -/
instance normed_space' : normed_space 𝕜' (continuous_multilinear_map 𝕜 (λ i : ι, G') G) :=
continuous_multilinear_map.normed_space

theorem le_op_norm_mul_prod_of_le {b : ι → ℝ} (hm : ∀ i, ‖m i‖ ≤ b i) : ‖f m‖ ≤ ‖f‖ * ∏ i, b i :=
(f.le_op_norm m).trans $ mul_le_mul_of_nonneg_left
  (prod_le_prod (λ _ _, norm_nonneg _) (λ i _, hm i)) (norm_nonneg f)

theorem le_op_norm_mul_pow_card_of_le {b : ℝ} (hm : ∀ i, ‖m i‖ ≤ b) :
  ‖f m‖ ≤ ‖f‖ * b ^ fintype.card ι :=
by simpa only [prod_const] using f.le_op_norm_mul_prod_of_le m hm

theorem le_op_norm_mul_pow_of_le {Ei : fin n → Type*} [Π i, normed_add_comm_group (Ei i)]
  [Π i, normed_space 𝕜 (Ei i)] (f : continuous_multilinear_map 𝕜 Ei G) (m : Π i, Ei i)
  {b : ℝ} (hm : ‖m‖ ≤ b) :
  ‖f m‖ ≤ ‖f‖ * b ^ n :=
by simpa only [fintype.card_fin]
  using f.le_op_norm_mul_pow_card_of_le m (λ i, (norm_le_pi_norm m i).trans hm)

/-- The fundamental property of the operator norm of a continuous multilinear map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`, `nnnorm` version. -/
theorem le_op_nnnorm : ‖f m‖₊ ≤ ‖f‖₊ * ∏ i, ‖m i‖₊ :=
nnreal.coe_le_coe.1 $ by { push_cast, exact f.le_op_norm m }

theorem le_of_op_nnnorm_le {C : ℝ≥0} (h : ‖f‖₊ ≤ C) : ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊ :=
(f.le_op_nnnorm m).trans $ mul_le_mul' h le_rfl

lemma op_norm_prod (f : continuous_multilinear_map 𝕜 E G) (g : continuous_multilinear_map 𝕜 E G') :
  ‖f.prod g‖ = max (‖f‖) (‖g‖) :=
le_antisymm
  (op_norm_le_bound _ (norm_nonneg (f, g)) (λ m,
    have H : 0 ≤ ∏ i, ‖m i‖, from prod_nonneg $ λ _ _,  norm_nonneg _,
    by simpa only [prod_apply, prod.norm_def, max_mul_of_nonneg, H]
      using max_le_max (f.le_op_norm m) (g.le_op_norm m))) $
  max_le
    (f.op_norm_le_bound (norm_nonneg _) $ λ m, (le_max_left _ _).trans ((f.prod g).le_op_norm _))
    (g.op_norm_le_bound (norm_nonneg _) $ λ m, (le_max_right _ _).trans ((f.prod g).le_op_norm _))

lemma norm_pi {ι' : Type v'} [fintype ι'] {E' : ι' → Type wE'} [Π i', normed_add_comm_group (E' i')]
  [Π i', normed_space 𝕜 (E' i')] (f : Π i', continuous_multilinear_map 𝕜 E (E' i')) :
  ‖pi f‖ = ‖f‖ :=
begin
  apply le_antisymm,
  { refine (op_norm_le_bound _ (norm_nonneg f) (λ m, _)),
    dsimp,
    rw pi_norm_le_iff_of_nonneg,
    exacts [λ i, (f i).le_of_op_norm_le m (norm_le_pi_norm f i),
      mul_nonneg (norm_nonneg f) (prod_nonneg $ λ _ _, norm_nonneg _)] },
  { refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (λ i, _),
    refine (op_norm_le_bound _ (norm_nonneg _) (λ m, _)),
    refine le_trans _ ((pi f).le_op_norm m),
    convert norm_le_pi_norm (λ j, f j m) i }
end

section
variables (𝕜 G)

@[simp] lemma norm_of_subsingleton [subsingleton ι] [nontrivial G] (i' : ι) :
  ‖of_subsingleton 𝕜 G i'‖ = 1 :=
begin
  apply le_antisymm,
  { refine op_norm_le_bound _ zero_le_one (λ m, _),
    rw [fintype.prod_subsingleton _ i', one_mul, of_subsingleton_apply] },
  { obtain ⟨g, hg⟩ := exists_ne (0 : G),
    rw ←norm_ne_zero_iff at hg,
    have := (of_subsingleton 𝕜 G i').ratio_le_op_norm (λ _, g),
    rwa [fintype.prod_subsingleton _ i', of_subsingleton_apply, div_self hg] at this },
end

@[simp] lemma nnnorm_of_subsingleton [subsingleton ι] [nontrivial G] (i' : ι) :
  ‖of_subsingleton 𝕜 G i'‖₊ = 1 :=
nnreal.eq $ norm_of_subsingleton _ _ _

variables {G} (E)

@[simp] lemma norm_const_of_is_empty [is_empty ι] (x : G) : ‖const_of_is_empty 𝕜 E x‖ = ‖x‖ :=
begin
  apply le_antisymm,
  { refine op_norm_le_bound _ (norm_nonneg _) (λ x, _),
    rw [fintype.prod_empty, mul_one, const_of_is_empty_apply], },
  { simpa using (const_of_is_empty 𝕜 E x).le_op_norm 0 }
end

@[simp] lemma nnnorm_const_of_is_empty [is_empty ι] (x : G) : ‖const_of_is_empty 𝕜 E x‖₊ = ‖x‖₊ :=
nnreal.eq $ norm_const_of_is_empty _ _ _

end

section

variables (𝕜 E E' G G')

/-- `continuous_multilinear_map.prod` as a `linear_isometry_equiv`. -/
def prodL :
  (continuous_multilinear_map 𝕜 E G) × (continuous_multilinear_map 𝕜 E G') ≃ₗᵢ[𝕜]
    continuous_multilinear_map 𝕜 E (G × G') :=
{ to_fun := λ f, f.1.prod f.2,
  inv_fun := λ f, ((continuous_linear_map.fst 𝕜 G G').comp_continuous_multilinear_map f,
    (continuous_linear_map.snd 𝕜 G G').comp_continuous_multilinear_map f),
  map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl,
  left_inv := λ f, by ext; refl,
  right_inv := λ f, by ext; refl,
  norm_map' := λ f, op_norm_prod f.1 f.2 }

/-- `continuous_multilinear_map.pi` as a `linear_isometry_equiv`. -/
def piₗᵢ {ι' : Type v'} [fintype ι'] {E' : ι' → Type wE'} [Π i', normed_add_comm_group (E' i')]
  [Π i', normed_space 𝕜 (E' i')] :
  @linear_isometry_equiv 𝕜 𝕜 _ _ (ring_hom.id 𝕜) _ _ _
    (Π i', continuous_multilinear_map 𝕜 E (E' i')) (continuous_multilinear_map 𝕜 E (Π i, E' i)) _ _
      (@pi.module ι' _ 𝕜 _ _ (λ i', infer_instance)) _ :=
{ to_linear_equiv :=
  -- note: `pi_linear_equiv` does not unify correctly here, presumably due to issues with dependent
  -- typeclass arguments.
  { map_add' := λ f g, rfl,
    map_smul' := λ c f, rfl,
    .. pi_equiv, },
  norm_map' := norm_pi }

end

end

section restrict_scalars

variables {𝕜' : Type*} [nontrivially_normed_field 𝕜'] [normed_algebra 𝕜' 𝕜]
variables [normed_space 𝕜' G] [is_scalar_tower 𝕜' 𝕜 G]
variables [Π i, normed_space 𝕜' (E i)] [∀ i, is_scalar_tower 𝕜' 𝕜 (E i)]

@[simp] lemma norm_restrict_scalars : ‖f.restrict_scalars 𝕜'‖ = ‖f‖ :=
by simp only [norm_def, coe_restrict_scalars]

variable (𝕜')

/-- `continuous_multilinear_map.restrict_scalars` as a `continuous_multilinear_map`. -/
def restrict_scalars_linear :
  continuous_multilinear_map 𝕜 E G →L[𝕜'] continuous_multilinear_map 𝕜' E G :=
linear_map.mk_continuous
{ to_fun := restrict_scalars 𝕜',
  map_add' := λ m₁ m₂, rfl,
  map_smul' := λ c m, rfl } 1 $ λ f, by simp

variable {𝕜'}

lemma continuous_restrict_scalars :
  continuous (restrict_scalars 𝕜' : continuous_multilinear_map 𝕜 E G →
    continuous_multilinear_map 𝕜' E G) :=
(restrict_scalars_linear 𝕜').continuous

end restrict_scalars

/-- The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, precise version.
For a less precise but more usable version, see `norm_image_sub_le`. The bound reads
`‖f m - f m'‖ ≤
  ‖f‖ * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`.-/
lemma norm_image_sub_le' [decidable_eq ι] (m₁ m₂ : Πi, E i) :
  ‖f m₁ - f m₂‖ ≤
  ‖f‖ * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
f.to_multilinear_map.norm_image_sub_le_of_bound' (norm_nonneg _) f.le_op_norm _ _

/-- The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, less precise
version. For a more precise but less usable version, see `norm_image_sub_le'`.
The bound is `‖f m - f m'‖ ≤ ‖f‖ * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`.-/
lemma norm_image_sub_le (m₁ m₂ : Πi, E i) :
  ‖f m₁ - f m₂‖ ≤ ‖f‖ * (fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (fintype.card ι - 1) * ‖m₁ - m₂‖ :=
f.to_multilinear_map.norm_image_sub_le_of_bound (norm_nonneg _) f.le_op_norm _ _

/-- Applying a multilinear map to a vector is continuous in both coordinates. -/
lemma continuous_eval :
  continuous (λ p : continuous_multilinear_map 𝕜 E G × Π i, E i, p.1 p.2) :=
begin
  apply continuous_iff_continuous_at.2 (λp, _),
  apply continuous_at_of_locally_lipschitz zero_lt_one
    ((‖p‖ + 1) * (fintype.card ι) * (‖p‖ + 1) ^ (fintype.card ι - 1) + ∏ i, ‖p.2 i‖)
    (λq hq, _),
  have : 0 ≤ (max ‖q.2‖ ‖p.2‖), by simp,
  have : 0 ≤ ‖p‖ + 1 := zero_le_one.trans ((le_add_iff_nonneg_left 1).2 $ norm_nonneg p),
  have A : ‖q‖ ≤ ‖p‖ + 1 := norm_le_of_mem_closed_ball hq.le,
  have : (max ‖q.2‖ ‖p.2‖) ≤ ‖p‖ + 1 :=
    (max_le_max (norm_snd_le q) (norm_snd_le p)).trans (by simp [A, -add_comm, zero_le_one]),
  have : ∀ (i : ι), i ∈ univ → 0 ≤ ‖p.2 i‖ := λ i hi, norm_nonneg _,
  calc dist (q.1 q.2) (p.1 p.2)
    ≤ dist (q.1 q.2) (q.1 p.2) + dist (q.1 p.2) (p.1 p.2) : dist_triangle _ _ _
    ... = ‖q.1 q.2 - q.1 p.2‖ + ‖q.1 p.2 - p.1 p.2‖ : by rw [dist_eq_norm, dist_eq_norm]
    ... ≤ ‖q.1‖ * (fintype.card ι) * (max ‖q.2‖ ‖p.2‖) ^ (fintype.card ι - 1) * ‖q.2 - p.2‖
          + ‖q.1 - p.1‖ * ∏ i, ‖p.2 i‖ :
      add_le_add (norm_image_sub_le _ _ _) ((q.1 - p.1).le_op_norm p.2)
    ... ≤ (‖p‖ + 1) * (fintype.card ι) * (‖p‖ + 1) ^ (fintype.card ι - 1) * ‖q - p‖
          + ‖q - p‖ * ∏ i, ‖p.2 i‖ :
      by apply_rules [add_le_add, mul_le_mul, le_refl, le_trans (norm_fst_le q) A, nat.cast_nonneg,
        mul_nonneg, pow_le_pow_of_le_left, pow_nonneg, norm_snd_le (q - p), norm_nonneg,
        norm_fst_le (q - p), prod_nonneg]
    ... = ((‖p‖ + 1) * (fintype.card ι) * (‖p‖ + 1) ^ (fintype.card ι - 1)
              + (∏ i, ‖p.2 i‖)) * dist q p : by { rw dist_eq_norm, ring }
end

lemma continuous_eval_left (m : Π i, E i) :
  continuous (λ p : continuous_multilinear_map 𝕜 E G, p m) :=
continuous_eval.comp (continuous_id.prod_mk continuous_const)

lemma has_sum_eval
  {α : Type*} {p : α → continuous_multilinear_map 𝕜 E G} {q : continuous_multilinear_map 𝕜 E G}
  (h : has_sum p q) (m : Π i, E i) : has_sum (λ a, p a m) (q m) :=
begin
  dsimp [has_sum] at h ⊢,
  convert ((continuous_eval_left m).tendsto _).comp h,
  ext s,
  simp
end

lemma tsum_eval {α : Type*} {p : α → continuous_multilinear_map 𝕜 E G} (hp : summable p)
  (m : Π i, E i) : (∑' a, p a) m = ∑' a, p a m :=
(has_sum_eval hp.has_sum m).tsum_eq.symm

open_locale topology
open filter

/-- If the target space is complete, the space of continuous multilinear maps with its norm is also
complete. The proof is essentially the same as for the space of continuous linear maps (modulo the
addition of `finset.prod` where needed. The duplication could be avoided by deducing the linear
case from the multilinear case via a currying isomorphism. However, this would mess up imports,
and it is more satisfactory to have the simplest case as a standalone proof. -/
instance [complete_space G] : complete_space (continuous_multilinear_map 𝕜 E G) :=
begin
  have nonneg : ∀ (v : Π i, E i), 0 ≤ ∏ i, ‖v i‖ :=
    λ v, finset.prod_nonneg (λ i hi, norm_nonneg _),
  -- We show that every Cauchy sequence converges.
  refine metric.complete_of_cauchy_seq_tendsto (λ f hf, _),
  -- We now expand out the definition of a Cauchy sequence,
  rcases cauchy_seq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩,
  -- and establish that the evaluation at any point `v : Π i, E i` is Cauchy.
  have cau : ∀ v, cauchy_seq (λ n, f n v),
  { assume v,
    apply cauchy_seq_iff_le_tendsto_0.2 ⟨λ n, b n * ∏ i, ‖v i‖, λ n, _, _, _⟩,
    { exact mul_nonneg (b0 n) (nonneg v) },
    { assume n m N hn hm,
      rw dist_eq_norm,
      apply le_trans ((f n - f m).le_op_norm v) _,
      exact mul_le_mul_of_nonneg_right (b_bound n m N hn hm) (nonneg v) },
    { simpa using b_lim.mul tendsto_const_nhds } },
  -- We assemble the limits points of those Cauchy sequences
  -- (which exist as `G` is complete)
  -- into a function which we call `F`.
  choose F hF using λv, cauchy_seq_tendsto_of_complete (cau v),
  -- Next, we show that this `F` is multilinear,
  let Fmult : multilinear_map 𝕜 E G :=
  { to_fun := F,
    map_add' := λ _ v i x y, begin
      resetI,
      have A := hF (function.update v i (x + y)),
      have B := (hF (function.update v i x)).add (hF (function.update v i y)),
      simp at A B,
      exact tendsto_nhds_unique A B
    end,
    map_smul' := λ _ v i c x, begin
      resetI,
      have A := hF (function.update v i (c • x)),
      have B := filter.tendsto.smul (@tendsto_const_nhds _ ℕ _ c _) (hF (function.update v i x)),
      simp at A B,
      exact tendsto_nhds_unique A B
    end },
  -- and that `F` has norm at most `(b 0 + ‖f 0‖)`.
  have Fnorm : ∀ v, ‖F v‖ ≤ (b 0 + ‖f 0‖) * ∏ i, ‖v i‖,
  { assume v,
    have A : ∀ n, ‖f n v‖ ≤ (b 0 + ‖f 0‖) * ∏ i, ‖v i‖,
    { assume n,
      apply le_trans ((f n).le_op_norm _) _,
      apply mul_le_mul_of_nonneg_right _ (nonneg v),
      calc ‖f n‖ = ‖(f n - f 0) + f 0‖ : by { congr' 1, abel }
      ... ≤ ‖f n - f 0‖ + ‖f 0‖ : norm_add_le _ _
      ... ≤ b 0 + ‖f 0‖ : begin
        apply add_le_add_right,
        simpa [dist_eq_norm] using b_bound n 0 0 (zero_le _) (zero_le _)
      end },
    exact le_of_tendsto (hF v).norm (eventually_of_forall A) },
  -- Thus `F` is continuous, and we propose that as the limit point of our original Cauchy sequence.
  let Fcont := Fmult.mk_continuous _ Fnorm,
  use Fcont,
  -- Our last task is to establish convergence to `F` in norm.
  have : ∀ n, ‖f n - Fcont‖ ≤ b n,
  { assume n,
    apply op_norm_le_bound _ (b0 n) (λ v, _),
    have A : ∀ᶠ m in at_top, ‖(f n - f m) v‖ ≤ b n * ∏ i, ‖v i‖,
    { refine eventually_at_top.2 ⟨n, λ m hm, _⟩,
      apply le_trans ((f n - f m).le_op_norm _) _,
      exact mul_le_mul_of_nonneg_right (b_bound n m n le_rfl hm) (nonneg v) },
    have B : tendsto (λ m, ‖(f n - f m) v‖) at_top (𝓝 (‖(f n - Fcont) v‖)) :=
      tendsto.norm (tendsto_const_nhds.sub (hF v)),
    exact le_of_tendsto B A },
  erw tendsto_iff_norm_tendsto_zero,
  exact squeeze_zero (λ n, norm_nonneg _) this b_lim,
end

end continuous_multilinear_map

/-- If a continuous multilinear map is constructed from a multilinear map via the constructor
`mk_continuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
lemma multilinear_map.mk_continuous_norm_le (f : multilinear_map 𝕜 E G) {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mk_continuous C H‖ ≤ C :=
continuous_multilinear_map.op_norm_le_bound _ hC (λm, H m)

/-- If a continuous multilinear map is constructed from a multilinear map via the constructor
`mk_continuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
lemma multilinear_map.mk_continuous_norm_le' (f : multilinear_map 𝕜 E G) {C : ℝ}
  (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mk_continuous C H‖ ≤ max C 0 :=
continuous_multilinear_map.op_norm_le_bound _ (le_max_right _ _) $
  λ m, (H m).trans $ mul_le_mul_of_nonneg_right (le_max_left _ _)
    (prod_nonneg $ λ _ _, norm_nonneg _)

namespace continuous_multilinear_map

/-- Given a continuous multilinear map `f` on `n` variables (parameterized by `fin n`) and a subset
`s` of `k` of these variables, one gets a new continuous multilinear map on `fin k` by varying
these variables, and fixing the other ones equal to a given value `z`. It is denoted by
`f.restr s hk z`, where `hk` is a proof that the cardinality of `s` is `k`. The implicit
identification between `fin k` and `s` that we use is the canonical (increasing) bijection. -/
def restr {k n : ℕ} (f : (G [×n]→L[𝕜] G' : _)) (s : finset (fin n)) (hk : s.card = k) (z : G) :
  G [×k]→L[𝕜] G' :=
(f.to_multilinear_map.restr s hk z).mk_continuous
(‖f‖ * ‖z‖^(n-k)) $ λ v, multilinear_map.restr_norm_le _ _ _ _ f.le_op_norm _

lemma norm_restr {k n : ℕ} (f : G [×n]→L[𝕜] G') (s : finset (fin n)) (hk : s.card = k) (z : G) :
  ‖f.restr s hk z‖ ≤ ‖f‖ * ‖z‖ ^ (n - k) :=
begin
  apply multilinear_map.mk_continuous_norm_le,
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
end

section

variables {𝕜 ι} {A : Type*} [normed_comm_ring A] [normed_algebra 𝕜 A]

@[simp]
lemma norm_mk_pi_algebra_le [nonempty ι] :
  ‖continuous_multilinear_map.mk_pi_algebra 𝕜 ι A‖ ≤ 1 :=
begin
  have := λ f, @op_norm_le_bound 𝕜 ι (λ i, A) A _ _ _ _ _ _ f _ zero_le_one,
  refine this _ _,
  intros m,
  simp only [continuous_multilinear_map.mk_pi_algebra_apply, one_mul],
  exact norm_prod_le' _ univ_nonempty _,
end

lemma norm_mk_pi_algebra_of_empty [is_empty ι] :
  ‖continuous_multilinear_map.mk_pi_algebra 𝕜 ι A‖ = ‖(1 : A)‖ :=
begin
  apply le_antisymm,
  { have := λ f, @op_norm_le_bound 𝕜 ι (λ i, A) A _ _ _ _ _ _ f _ (norm_nonneg (1 : A)),
    refine this _ _,
    simp, },
  { convert ratio_le_op_norm _ (λ _, (1 : A)),
    simp [eq_empty_of_is_empty (univ : finset ι)], },
end

@[simp] lemma norm_mk_pi_algebra [norm_one_class A] :
  ‖continuous_multilinear_map.mk_pi_algebra 𝕜 ι A‖ = 1 :=
begin
  casesI is_empty_or_nonempty ι,
  { simp [norm_mk_pi_algebra_of_empty] },
  { refine le_antisymm norm_mk_pi_algebra_le _,
    convert ratio_le_op_norm _ (λ _, 1); [skip, apply_instance],
    simp },
end

end

section

variables {𝕜 n} {A : Type*} [normed_ring A] [normed_algebra 𝕜 A]

lemma norm_mk_pi_algebra_fin_succ_le :
  ‖continuous_multilinear_map.mk_pi_algebra_fin 𝕜 n.succ A‖ ≤ 1 :=
begin
  have := λ f, @op_norm_le_bound 𝕜 (fin n.succ) (λ i, A) A _ _ _ _ _ _ f _ zero_le_one,
  refine this _ _,
  intros m,
  simp only [continuous_multilinear_map.mk_pi_algebra_fin_apply, one_mul, list.of_fn_eq_map,
    fin.prod_univ_def, multiset.coe_map, multiset.coe_prod],
  refine (list.norm_prod_le' _).trans_eq _,
  { rw [ne.def, list.map_eq_nil, list.fin_range_eq_nil],
    exact nat.succ_ne_zero _, },
  rw list.map_map,
end

lemma norm_mk_pi_algebra_fin_le_of_pos (hn : 0 < n) :
  ‖continuous_multilinear_map.mk_pi_algebra_fin 𝕜 n A‖ ≤ 1 :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_succ_of_ne_zero hn.ne',
  exact norm_mk_pi_algebra_fin_succ_le
end

lemma norm_mk_pi_algebra_fin_zero :
  ‖continuous_multilinear_map.mk_pi_algebra_fin 𝕜 0 A‖ = ‖(1 : A)‖ :=
begin
  refine le_antisymm _ _,
  { have := λ f, @op_norm_le_bound 𝕜 (fin 0) (λ i, A) A _ _ _ _ _ _ f _ (norm_nonneg (1 : A)),
    refine this _ _,
    simp, },
  { convert ratio_le_op_norm _ (λ _, (1 : A)),
    simp }
end

@[simp] lemma norm_mk_pi_algebra_fin [norm_one_class A] :
  ‖continuous_multilinear_map.mk_pi_algebra_fin 𝕜 n A‖ = 1 :=
begin
  cases n,
  { simp [norm_mk_pi_algebra_fin_zero] },
  { refine le_antisymm norm_mk_pi_algebra_fin_succ_le _,
    convert ratio_le_op_norm _ (λ _, 1); [skip, apply_instance],
    simp }
end

end

variables (𝕜 ι)

/-- The canonical continuous multilinear map on `𝕜^ι`, associating to `m` the product of all the
`m i` (multiplied by a fixed reference element `z` in the target module) -/
protected def mk_pi_field (z : G) : continuous_multilinear_map 𝕜 (λ(i : ι), 𝕜) G :=
multilinear_map.mk_continuous
  (multilinear_map.mk_pi_ring 𝕜 ι z) (‖z‖)
  (λ m, by simp only [multilinear_map.mk_pi_ring_apply, norm_smul, norm_prod,
    mul_comm])

variables {𝕜 ι}

@[simp] lemma mk_pi_field_apply (z : G) (m : ι → 𝕜) :
  (continuous_multilinear_map.mk_pi_field 𝕜 ι z : (ι → 𝕜) → G) m = (∏ i, m i) • z := rfl

lemma mk_pi_field_apply_one_eq_self (f : continuous_multilinear_map 𝕜 (λ(i : ι), 𝕜) G) :
  continuous_multilinear_map.mk_pi_field 𝕜 ι (f (λi, 1)) = f :=
to_multilinear_map_injective f.to_multilinear_map.mk_pi_ring_apply_one_eq_self

@[simp] lemma norm_mk_pi_field (z : G) : ‖continuous_multilinear_map.mk_pi_field 𝕜 ι z‖ = ‖z‖ :=
(multilinear_map.mk_continuous_norm_le _ (norm_nonneg z) _).antisymm $
  by simpa using (continuous_multilinear_map.mk_pi_field 𝕜 ι z).le_op_norm (λ _, 1)

lemma mk_pi_field_eq_iff {z₁ z₂ : G} :
  continuous_multilinear_map.mk_pi_field 𝕜 ι z₁ = continuous_multilinear_map.mk_pi_field 𝕜 ι z₂ ↔
  z₁ = z₂ :=
begin
  rw [← to_multilinear_map_injective.eq_iff],
  exact multilinear_map.mk_pi_ring_eq_iff
end

lemma mk_pi_field_zero :
  continuous_multilinear_map.mk_pi_field 𝕜 ι (0 : G) = 0 :=
by ext; rw [mk_pi_field_apply, smul_zero, continuous_multilinear_map.zero_apply]

lemma mk_pi_field_eq_zero_iff (z : G) :
  continuous_multilinear_map.mk_pi_field 𝕜 ι z = 0 ↔ z = 0 :=
by rw [← mk_pi_field_zero, mk_pi_field_eq_iff]

variables (𝕜 ι G)

/-- Continuous multilinear maps on `𝕜^n` with values in `G` are in bijection with `G`, as such a
continuous multilinear map is completely determined by its value on the constant vector made of
ones. We register this bijection as a linear isometry in
`continuous_multilinear_map.pi_field_equiv`. -/
protected def pi_field_equiv : G ≃ₗᵢ[𝕜] (continuous_multilinear_map 𝕜 (λ(i : ι), 𝕜) G) :=
{ to_fun    := λ z, continuous_multilinear_map.mk_pi_field 𝕜 ι z,
  inv_fun   := λ f, f (λi, 1),
  map_add'  := λ z z', by { ext m, simp [smul_add] },
  map_smul' := λ c z, by { ext m, simp [smul_smul, mul_comm] },
  left_inv  := λ z, by simp,
  right_inv := λ f, f.mk_pi_field_apply_one_eq_self,
  norm_map' := norm_mk_pi_field }

end continuous_multilinear_map

namespace continuous_linear_map

lemma norm_comp_continuous_multilinear_map_le (g : G →L[𝕜] G')
  (f : continuous_multilinear_map 𝕜 E G) :
  ‖g.comp_continuous_multilinear_map f‖ ≤ ‖g‖ * ‖f‖ :=
continuous_multilinear_map.op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) $ λ m,
calc ‖g (f m)‖ ≤ ‖g‖ * (‖f‖ * ∏ i, ‖m i‖) : g.le_op_norm_of_le $ f.le_op_norm _
           ... = _                        : (mul_assoc _ _ _).symm

variables (𝕜 E G G')
/-- `continuous_linear_map.comp_continuous_multilinear_map` as a bundled continuous bilinear map. -/
def comp_continuous_multilinear_mapL :
  (G →L[𝕜] G') →L[𝕜] continuous_multilinear_map 𝕜 E G →L[𝕜] continuous_multilinear_map 𝕜 E G' :=
linear_map.mk_continuous₂
  (linear_map.mk₂ 𝕜 comp_continuous_multilinear_map (λ f₁ f₂ g, rfl) (λ c f g, rfl)
    (λ f g₁ g₂, by { ext1, apply f.map_add }) (λ c f g, by { ext1, simp }))
  1 $ λ f g, by { rw one_mul, exact f.norm_comp_continuous_multilinear_map_le g }

variables {𝕜 G G'}

/-- `continuous_linear_map.comp_continuous_multilinear_map` as a bundled
continuous linear equiv. -/
def _root_.continuous_linear_equiv.comp_continuous_multilinear_mapL (g : G ≃L[𝕜] G') :
  continuous_multilinear_map 𝕜 E G ≃L[𝕜] continuous_multilinear_map 𝕜 E G' :=
{ inv_fun := comp_continuous_multilinear_mapL 𝕜 _ _ _ g.symm.to_continuous_linear_map,
  left_inv := begin
    assume f,
    ext1 m,
    simp only [comp_continuous_multilinear_mapL, continuous_linear_equiv.coe_def_rev,
      to_linear_map_eq_coe, linear_map.to_fun_eq_coe, coe_coe, linear_map.mk_continuous₂_apply,
      linear_map.mk₂_apply, comp_continuous_multilinear_map_coe, continuous_linear_equiv.coe_coe,
      function.comp_app, continuous_linear_equiv.symm_apply_apply],
  end,
  right_inv := begin
    assume f,
    ext1 m,
    simp only [comp_continuous_multilinear_mapL, continuous_linear_equiv.coe_def_rev,
      to_linear_map_eq_coe, linear_map.mk_continuous₂_apply, linear_map.mk₂_apply,
      linear_map.to_fun_eq_coe, coe_coe, comp_continuous_multilinear_map_coe,
      continuous_linear_equiv.coe_coe, function.comp_app, continuous_linear_equiv.apply_symm_apply],
  end,
  continuous_to_fun :=
    (comp_continuous_multilinear_mapL 𝕜 _ _ _ g.to_continuous_linear_map).continuous,
  continuous_inv_fun :=
    (comp_continuous_multilinear_mapL 𝕜 _ _ _ g.symm.to_continuous_linear_map).continuous,
  .. comp_continuous_multilinear_mapL 𝕜 _ _ _ g.to_continuous_linear_map }

@[simp] lemma _root_.continuous_linear_equiv.comp_continuous_multilinear_mapL_symm
  (g : G ≃L[𝕜] G') :
  (g.comp_continuous_multilinear_mapL E).symm = g.symm.comp_continuous_multilinear_mapL E := rfl

variables {E}

@[simp] lemma _root_.continuous_linear_equiv.comp_continuous_multilinear_mapL_apply
  (g : G ≃L[𝕜] G') (f : continuous_multilinear_map 𝕜 E G) :
  g.comp_continuous_multilinear_mapL E f = (g : G →L[𝕜] G').comp_continuous_multilinear_map f :=
rfl

/-- Flip arguments in `f : G →L[𝕜] continuous_multilinear_map 𝕜 E G'` to get
`continuous_multilinear_map 𝕜 E (G →L[𝕜] G')` -/
def flip_multilinear (f : G →L[𝕜] continuous_multilinear_map 𝕜 E G') :
  continuous_multilinear_map 𝕜 E (G →L[𝕜] G') :=
multilinear_map.mk_continuous
  { to_fun := λ m, linear_map.mk_continuous
      { to_fun := λ x, f x m,
        map_add' := λ x y, by simp only [map_add, continuous_multilinear_map.add_apply],
        map_smul' := λ c x, by simp only [continuous_multilinear_map.smul_apply, map_smul,
                                          ring_hom.id_apply] }
      (‖f‖ * ∏ i, ‖m i‖) $ λ x,
      by { rw mul_right_comm, exact (f x).le_of_op_norm_le _ (f.le_op_norm x) },
    map_add' := λ _ m i x y,
      by { ext1, simp only [add_apply, continuous_multilinear_map.map_add, linear_map.coe_mk,
                            linear_map.mk_continuous_apply]},
    map_smul' := λ _ m i c x,
      by { ext1, simp only [coe_smul', continuous_multilinear_map.map_smul, linear_map.coe_mk,
                            linear_map.mk_continuous_apply, pi.smul_apply]} }
  ‖f‖ $ λ m,
  linear_map.mk_continuous_norm_le _
    (mul_nonneg (norm_nonneg f) (prod_nonneg $ λ i hi, norm_nonneg (m i))) _

end continuous_linear_map

lemma linear_isometry.norm_comp_continuous_multilinear_map
  (g : G →ₗᵢ[𝕜] G') (f : continuous_multilinear_map 𝕜 E G) :
  ‖g.to_continuous_linear_map.comp_continuous_multilinear_map f‖ = ‖f‖ :=
by simp only [continuous_linear_map.comp_continuous_multilinear_map_coe,
    linear_isometry.coe_to_continuous_linear_map, linear_isometry.norm_map,
    continuous_multilinear_map.norm_def]

open continuous_multilinear_map

namespace multilinear_map

/-- Given a map `f : G →ₗ[𝕜] multilinear_map 𝕜 E G'` and an estimate
`H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖`, construct a continuous linear
map from `G` to `continuous_multilinear_map 𝕜 E G'`.

In order to lift, e.g., a map `f : (multilinear_map 𝕜 E G) →ₗ[𝕜] multilinear_map 𝕜 E' G'`
to a map `(continuous_multilinear_map 𝕜 E G) →L[𝕜] continuous_multilinear_map 𝕜 E' G'`,
one can apply this construction to `f.comp continuous_multilinear_map.to_multilinear_map_linear`
which is a linear map from `continuous_multilinear_map 𝕜 E G` to `multilinear_map 𝕜 E' G'`. -/
def mk_continuous_linear (f : G →ₗ[𝕜] multilinear_map 𝕜 E G') (C : ℝ)
  (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) :
  G →L[𝕜] continuous_multilinear_map 𝕜 E G' :=
linear_map.mk_continuous
  { to_fun := λ x, (f x).mk_continuous (C * ‖x‖) $ H x,
    map_add' := λ x y, by { ext1, simp only [_root_.map_add], refl },
    map_smul' := λ c x, by { ext1, simp only [smul_hom_class.map_smul], refl } }
  (max C 0) $ λ x, ((f x).mk_continuous_norm_le' _).trans_eq $
    by rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

lemma mk_continuous_linear_norm_le' (f : G →ₗ[𝕜] multilinear_map 𝕜 E G') (C : ℝ)
  (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) :
  ‖mk_continuous_linear f C H‖ ≤ max C 0 :=
begin
  dunfold mk_continuous_linear,
  exact linear_map.mk_continuous_norm_le _ (le_max_right _ _) _
end

lemma mk_continuous_linear_norm_le (f : G →ₗ[𝕜] multilinear_map 𝕜 E G') {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) :
  ‖mk_continuous_linear f C H‖ ≤ C :=
(mk_continuous_linear_norm_le' f C H).trans_eq (max_eq_left hC)

/-- Given a map `f : multilinear_map 𝕜 E (multilinear_map 𝕜 E' G)` and an estimate
`H : ∀ m m', ‖f m m'‖ ≤ C * ∏ i, ‖m i‖ * ∏ i, ‖m' i‖`, upgrade all `multilinear_map`s in the type to
`continuous_multilinear_map`s. -/
def mk_continuous_multilinear (f : multilinear_map 𝕜 E (multilinear_map 𝕜 E' G)) (C : ℝ)
  (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ C * (∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
  continuous_multilinear_map 𝕜 E (continuous_multilinear_map 𝕜 E' G) :=
mk_continuous
  { to_fun := λ m, mk_continuous (f m) (C * ∏ i, ‖m i‖) $ H m,
    map_add' := λ _ m i x y, by { ext1, simp },
    map_smul' := λ _ m i c x, by { ext1, simp } }
  (max C 0) $ λ m, ((f m).mk_continuous_norm_le' _).trans_eq $
    by { rw [max_mul_of_nonneg, zero_mul], exact prod_nonneg (λ _ _, norm_nonneg _) }

@[simp] lemma mk_continuous_multilinear_apply (f : multilinear_map 𝕜 E (multilinear_map 𝕜 E' G))
  {C : ℝ} (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ C * (∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) (m : Π i, E i) :
  ⇑(mk_continuous_multilinear f C H m) = f m :=
rfl

lemma mk_continuous_multilinear_norm_le' (f : multilinear_map 𝕜 E (multilinear_map 𝕜 E' G)) (C : ℝ)
  (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ C * (∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
  ‖mk_continuous_multilinear f C H‖ ≤ max C 0 :=
begin
  dunfold mk_continuous_multilinear,
  exact mk_continuous_norm_le _ (le_max_right _ _) _
end

lemma mk_continuous_multilinear_norm_le (f : multilinear_map 𝕜 E (multilinear_map 𝕜 E' G)) {C : ℝ}
  (hC : 0 ≤ C) (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ C * (∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
  ‖mk_continuous_multilinear f C H‖ ≤ C :=
(mk_continuous_multilinear_norm_le' f C H).trans_eq (max_eq_left hC)

end multilinear_map

namespace continuous_multilinear_map

lemma norm_comp_continuous_linear_le (g : continuous_multilinear_map 𝕜 E₁ G)
  (f : Π i, E i →L[𝕜] E₁ i) :
  ‖g.comp_continuous_linear_map f‖ ≤ ‖g‖ * ∏ i, ‖f i‖ :=
op_norm_le_bound _ (mul_nonneg (norm_nonneg _) $ prod_nonneg $ λ i hi, norm_nonneg _) $ λ m,
calc ‖g (λ i, f i (m i))‖ ≤ ‖g‖ * ∏ i, ‖f i (m i)‖ : g.le_op_norm _
... ≤ ‖g‖ * ∏ i, (‖f i‖ * ‖m i‖) :
  mul_le_mul_of_nonneg_left
    (prod_le_prod (λ _ _, norm_nonneg _) (λ i hi, (f i).le_op_norm (m i))) (norm_nonneg g)
... = (‖g‖ * ∏ i, ‖f i‖) * ∏ i, ‖m i‖ : by rw [prod_mul_distrib, mul_assoc]

lemma norm_comp_continuous_linear_isometry_le (g : continuous_multilinear_map 𝕜 E₁ G)
  (f : Π i, E i →ₗᵢ[𝕜] E₁ i) :
  ‖g.comp_continuous_linear_map (λ i, (f i).to_continuous_linear_map)‖ ≤ ‖g‖ :=
begin
  apply op_norm_le_bound _ (norm_nonneg _) (λ m, _),
  apply (g.le_op_norm _).trans _,
  simp only [continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe,
    linear_isometry.coe_to_continuous_linear_map, linear_isometry.norm_map]
end

lemma norm_comp_continuous_linear_isometry_equiv (g : continuous_multilinear_map 𝕜 E₁ G)
  (f : Π i, E i ≃ₗᵢ[𝕜] E₁ i) :
  ‖g.comp_continuous_linear_map (λ i, (f i : E i →L[𝕜] E₁ i))‖ = ‖g‖ :=
begin
  apply le_antisymm (g.norm_comp_continuous_linear_isometry_le (λ i, (f i).to_linear_isometry)),
  have : g = (g.comp_continuous_linear_map (λ i, (f i : E i →L[𝕜] E₁ i)))
    .comp_continuous_linear_map (λ i, ((f i).symm : E₁ i →L[𝕜] E i)),
  { ext1 m,
    simp only [comp_continuous_linear_map_apply, linear_isometry_equiv.coe_coe'',
      linear_isometry_equiv.apply_symm_apply] },
  conv_lhs { rw this },
  apply (g.comp_continuous_linear_map (λ i, (f i : E i →L[𝕜] E₁ i)))
    .norm_comp_continuous_linear_isometry_le (λ i, (f i).symm.to_linear_isometry),
end

/-- `continuous_multilinear_map.comp_continuous_linear_map` as a bundled continuous linear map.
This implementation fixes `f : Π i, E i →L[𝕜] E₁ i`.

TODO: Actually, the map is multilinear in `f` but an attempt to formalize this failed because of
issues with class instances. -/
def comp_continuous_linear_mapL (f : Π i, E i →L[𝕜] E₁ i) :
  continuous_multilinear_map 𝕜 E₁ G →L[𝕜] continuous_multilinear_map 𝕜 E G :=
linear_map.mk_continuous
  { to_fun := λ g, g.comp_continuous_linear_map f,
    map_add' := λ g₁ g₂, rfl,
    map_smul' := λ c g, rfl }
  (∏ i, ‖f i‖) $ λ g, (norm_comp_continuous_linear_le _ _).trans_eq (mul_comm _ _)

@[simp] lemma comp_continuous_linear_mapL_apply
  (g : continuous_multilinear_map 𝕜 E₁ G) (f : Π i, E i →L[𝕜] E₁ i) :
  comp_continuous_linear_mapL f g = g.comp_continuous_linear_map f :=
rfl

lemma norm_comp_continuous_linear_mapL_le (f : Π i, E i →L[𝕜] E₁ i) :
  ‖@comp_continuous_linear_mapL 𝕜 ι E E₁ G _ _ _ _ _ _ _ _ f‖ ≤ (∏ i, ‖f i‖) :=
linear_map.mk_continuous_norm_le _ (prod_nonneg $ λ i _, norm_nonneg _) _

variable (G)

/-- `continuous_multilinear_map.comp_continuous_linear_map` as a bundled continuous linear equiv,
given `f : Π i, E i ≃L[𝕜] E₁ i`. -/
def comp_continuous_linear_map_equivL (f : Π i, E i ≃L[𝕜] E₁ i) :
  continuous_multilinear_map 𝕜 E₁ G ≃L[𝕜] continuous_multilinear_map 𝕜 E G :=
{ inv_fun := comp_continuous_linear_mapL (λ i, ((f i).symm : E₁ i →L[𝕜] E i)),
  continuous_to_fun := (comp_continuous_linear_mapL (λ i, (f i : E i →L[𝕜] E₁ i))).continuous,
  continuous_inv_fun :=
    (comp_continuous_linear_mapL (λ i, ((f i).symm : E₁ i →L[𝕜] E i))).continuous,
  left_inv := begin
    assume g,
    ext1 m,
    simp only [continuous_linear_map.to_linear_map_eq_coe, linear_map.to_fun_eq_coe,
      continuous_linear_map.coe_coe, comp_continuous_linear_mapL_apply,
      comp_continuous_linear_map_apply, continuous_linear_equiv.coe_coe,
      continuous_linear_equiv.apply_symm_apply],
  end,
  right_inv := begin
    assume g,
    ext1 m,
    simp only [continuous_linear_map.to_linear_map_eq_coe, comp_continuous_linear_mapL_apply,
      linear_map.to_fun_eq_coe, continuous_linear_map.coe_coe, comp_continuous_linear_map_apply,
      continuous_linear_equiv.coe_coe, continuous_linear_equiv.symm_apply_apply],
  end,
  .. comp_continuous_linear_mapL (λ i, (f i : E i →L[𝕜] E₁ i)) }

@[simp] lemma comp_continuous_linear_map_equivL_symm (f : Π i, E i ≃L[𝕜] E₁ i) :
  (comp_continuous_linear_map_equivL G f).symm =
    comp_continuous_linear_map_equivL G (λ (i : ι), (f i).symm) :=
rfl

variable {G}

@[simp] lemma comp_continuous_linear_map_equivL_apply
  (g : continuous_multilinear_map 𝕜 E₁ G) (f : Π i, E i ≃L[𝕜] E₁ i) :
  comp_continuous_linear_map_equivL G f g =
    g.comp_continuous_linear_map (λ i, (f i : E i →L[𝕜] E₁ i)) := rfl

end continuous_multilinear_map

section smul

variables {R : Type*} [semiring R] [module R G] [smul_comm_class 𝕜 R G]
  [has_continuous_const_smul R G]

instance : has_continuous_const_smul R (continuous_multilinear_map 𝕜 E G) :=
⟨λ c, (continuous_linear_map.comp_continuous_multilinear_mapL 𝕜 _ G G
  (c • continuous_linear_map.id 𝕜 G)).2⟩

end smul

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
  (f : Ei 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), Ei i.succ) G)) (m : Πi, Ei i) :
  ‖f (m 0) (tail m)‖ ≤ ‖f‖ * ∏ i, ‖m i‖ :=
calc
  ‖f (m 0) (tail m)‖ ≤ ‖f (m 0)‖ * ∏ i, ‖(tail m) i‖ : (f (m 0)).le_op_norm _
  ... ≤ (‖f‖ * ‖m 0‖) * ∏ i, ‖(tail m) i‖ :
    mul_le_mul_of_nonneg_right (f.le_op_norm _) (prod_nonneg (λi hi, norm_nonneg _))
  ... = ‖f‖ * (‖m 0‖ * ∏ i, ‖(tail m) i‖) : by ring
  ... = ‖f‖ * ∏ i, ‖m i‖ : by { rw prod_univ_succ, refl }

lemma continuous_multilinear_map.norm_map_init_le
  (f : continuous_multilinear_map 𝕜 (λ(i : fin n), Ei i.cast_succ) (Ei (last n) →L[𝕜] G))
  (m : Πi, Ei i) :
  ‖f (init m) (m (last n))‖ ≤ ‖f‖ * ∏ i, ‖m i‖ :=
calc
  ‖f (init m) (m (last n))‖ ≤ ‖f (init m)‖ * ‖m (last n)‖ : (f (init m)).le_op_norm _
  ... ≤ (‖f‖ * (∏ i, ‖(init m) i‖)) * ‖m (last n)‖ :
    mul_le_mul_of_nonneg_right (f.le_op_norm _) (norm_nonneg _)
  ... = ‖f‖ * ((∏ i, ‖(init m) i‖) * ‖m (last n)‖) : mul_assoc _ _ _
  ... = ‖f‖ * ∏ i, ‖m i‖ : by { rw prod_univ_cast_succ, refl }

lemma continuous_multilinear_map.norm_map_cons_le
  (f : continuous_multilinear_map 𝕜 Ei G) (x : Ei 0) (m : Π(i : fin n), Ei i.succ) :
  ‖f (cons x m)‖ ≤ ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ :=
calc
  ‖f (cons x m)‖ ≤ ‖f‖ * ∏ i, ‖cons x m i‖ : f.le_op_norm _
  ... = (‖f‖ * ‖x‖) * ∏ i, ‖m i‖ : by { rw prod_univ_succ, simp [mul_assoc] }

lemma continuous_multilinear_map.norm_map_snoc_le
  (f : continuous_multilinear_map 𝕜 Ei G) (m : Π(i : fin n), Ei i.cast_succ) (x : Ei (last n)) :
  ‖f (snoc m x)‖ ≤ ‖f‖ * (∏ i, ‖m i‖) * ‖x‖ :=
calc
  ‖f (snoc m x)‖ ≤ ‖f‖ * ∏ i, ‖snoc m x i‖ : f.le_op_norm _
  ... = ‖f‖ * (∏ i, ‖m i‖) * ‖x‖ : by { rw prod_univ_cast_succ, simp [mul_assoc] }

/-! #### Left currying -/

/-- Given a continuous linear map `f` from `E 0` to continuous multilinear maps on `n` variables,
construct the corresponding continuous multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (m 0) (tail m)`-/
def continuous_linear_map.uncurry_left
  (f : Ei 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), Ei i.succ) G)) :
  continuous_multilinear_map 𝕜 Ei G :=
(@linear_map.uncurry_left 𝕜 n Ei G _ _ _ _ _
  (continuous_multilinear_map.to_multilinear_map_linear.comp f.to_linear_map)).mk_continuous
    (‖f‖) (λm, continuous_linear_map.norm_map_tail_le f m)

@[simp] lemma continuous_linear_map.uncurry_left_apply
  (f : Ei 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), Ei i.succ) G)) (m : Πi, Ei i) :
  f.uncurry_left m = f (m 0) (tail m) := rfl

/-- Given a continuous multilinear map `f` in `n+1` variables, split the first variable to obtain
a continuous linear map into continuous multilinear maps in `n` variables, given by
`x ↦ (m ↦ f (cons x m))`. -/
def continuous_multilinear_map.curry_left
  (f : continuous_multilinear_map 𝕜 Ei G) :
  Ei 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), Ei i.succ) G) :=
linear_map.mk_continuous
{ -- define a linear map into `n` continuous multilinear maps from an `n+1` continuous multilinear
  -- map
  to_fun    := λx, (f.to_multilinear_map.curry_left x).mk_continuous
    (‖f‖ * ‖x‖) (f.norm_map_cons_le x),
  map_add'  := λx y, by { ext m, exact f.cons_add m x y },
  map_smul' := λc x, by { ext m, exact f.cons_smul m c x } }
  -- then register its continuity thanks to its boundedness properties.
(‖f‖) (λx, multilinear_map.mk_continuous_norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _)

@[simp] lemma continuous_multilinear_map.curry_left_apply
  (f : continuous_multilinear_map 𝕜 Ei G) (x : Ei 0) (m : Π(i : fin n), Ei i.succ) :
  f.curry_left x m = f (cons x m) := rfl

@[simp] lemma continuous_linear_map.curry_uncurry_left
  (f : Ei 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), Ei i.succ) G)) :
  f.uncurry_left.curry_left = f :=
begin
  ext m x,
  simp only [tail_cons, continuous_linear_map.uncurry_left_apply,
             continuous_multilinear_map.curry_left_apply],
  rw cons_zero
end

@[simp] lemma continuous_multilinear_map.uncurry_curry_left
  (f : continuous_multilinear_map 𝕜 Ei G) : f.curry_left.uncurry_left = f :=
continuous_multilinear_map.to_multilinear_map_injective $ f.to_multilinear_map.uncurry_curry_left

variables (𝕜 Ei G)

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), E i` is canonically isomorphic to
the space of continuous linear maps from `E 0` to the space of continuous multilinear maps on
`Π(i : fin n), E i.succ `, by separating the first variable. We register this isomorphism in
`continuous_multilinear_curry_left_equiv 𝕜 E E₂`. The algebraic version (without topology) is given
in `multilinear_curry_left_equiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.uncurry_left` and `f.curry_left`. Use these
unless you need the full framework of linear isometric equivs. -/
def continuous_multilinear_curry_left_equiv :
  (Ei 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), Ei i.succ) G)) ≃ₗᵢ[𝕜]
  (continuous_multilinear_map 𝕜 Ei G) :=
linear_isometry_equiv.of_bounds
  { to_fun    := continuous_linear_map.uncurry_left,
    map_add'  := λf₁ f₂, by { ext m, refl },
    map_smul' := λc f, by { ext m, refl },
    inv_fun   := continuous_multilinear_map.curry_left,
    left_inv  := continuous_linear_map.curry_uncurry_left,
    right_inv := continuous_multilinear_map.uncurry_curry_left }
  (λ f, multilinear_map.mk_continuous_norm_le _ (norm_nonneg f) _)
  (λ f, linear_map.mk_continuous_norm_le _ (norm_nonneg f) _)

variables {𝕜 Ei G}

@[simp] lemma continuous_multilinear_curry_left_equiv_apply
  (f : Ei 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ i : fin n, Ei i.succ) G)) (v : Π i, Ei i) :
  continuous_multilinear_curry_left_equiv 𝕜 Ei G f v = f (v 0) (tail v) := rfl

@[simp] lemma continuous_multilinear_curry_left_equiv_symm_apply
  (f : continuous_multilinear_map 𝕜 Ei G) (x : Ei 0) (v : Π i : fin n, Ei i.succ) :
  (continuous_multilinear_curry_left_equiv 𝕜 Ei G).symm f x v = f (cons x v) := rfl

@[simp] lemma continuous_multilinear_map.curry_left_norm
  (f : continuous_multilinear_map 𝕜 Ei G) : ‖f.curry_left‖ = ‖f‖ :=
(continuous_multilinear_curry_left_equiv 𝕜 Ei G).symm.norm_map f

@[simp] lemma continuous_linear_map.uncurry_left_norm
  (f : Ei 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), Ei i.succ) G)) :
  ‖f.uncurry_left‖ = ‖f‖ :=
(continuous_multilinear_curry_left_equiv 𝕜 Ei G).norm_map f

/-! #### Right currying -/

/-- Given a continuous linear map `f` from continuous multilinear maps on `n` variables to
continuous linear maps on `E 0`, construct the corresponding continuous multilinear map on `n+1`
variables obtained by concatenating the variables, given by `m ↦ f (init m) (m (last n))`. -/
def continuous_multilinear_map.uncurry_right
  (f : continuous_multilinear_map 𝕜 (λ i : fin n, Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) :
  continuous_multilinear_map 𝕜 Ei G :=
let f' : multilinear_map 𝕜 (λ(i : fin n), Ei i.cast_succ) (Ei (last n) →ₗ[𝕜] G) :=
{ to_fun    := λ m, (f m).to_linear_map,
  map_add'  := λ _ m i x y, by simp,
  map_smul' := λ _ m i c x, by simp } in
(@multilinear_map.uncurry_right 𝕜 n Ei G _ _ _ _ _ f').mk_continuous
  (‖f‖) (λm, f.norm_map_init_le m)

@[simp] lemma continuous_multilinear_map.uncurry_right_apply
  (f : continuous_multilinear_map 𝕜 (λ(i : fin n), Ei i.cast_succ) (Ei (last n) →L[𝕜] G))
  (m : Πi, Ei i) :
  f.uncurry_right m = f (init m) (m (last n)) := rfl

/-- Given a continuous multilinear map `f` in `n+1` variables, split the last variable to obtain
a continuous multilinear map in `n` variables into continuous linear maps, given by
`m ↦ (x ↦ f (snoc m x))`. -/
def continuous_multilinear_map.curry_right
  (f : continuous_multilinear_map 𝕜 Ei G) :
  continuous_multilinear_map 𝕜 (λ i : fin n, Ei i.cast_succ) (Ei (last n) →L[𝕜] G) :=
let f' : multilinear_map 𝕜 (λ(i : fin n), Ei i.cast_succ) (Ei (last n) →L[𝕜] G) :=
{ to_fun    := λm, (f.to_multilinear_map.curry_right m).mk_continuous
    (‖f‖ * ∏ i, ‖m i‖) $ λx, f.norm_map_snoc_le m x,
  map_add'  := λ _ m i x y, by { simp, refl },
  map_smul' := λ _ m i c x, by { simp, refl } } in
f'.mk_continuous (‖f‖) (λm, linear_map.mk_continuous_norm_le _
  (mul_nonneg (norm_nonneg _) (prod_nonneg (λj hj, norm_nonneg _))) _)

@[simp] lemma continuous_multilinear_map.curry_right_apply
  (f : continuous_multilinear_map 𝕜 Ei G) (m : Π i : fin n, Ei i.cast_succ) (x : Ei (last n)) :
  f.curry_right m x = f (snoc m x) := rfl

@[simp] lemma continuous_multilinear_map.curry_uncurry_right
  (f : continuous_multilinear_map 𝕜 (λ i : fin n, Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) :
  f.uncurry_right.curry_right = f :=
begin
  ext m x,
  simp only [snoc_last, continuous_multilinear_map.curry_right_apply,
             continuous_multilinear_map.uncurry_right_apply],
  rw init_snoc
end

@[simp] lemma continuous_multilinear_map.uncurry_curry_right
  (f : continuous_multilinear_map 𝕜 Ei G) : f.curry_right.uncurry_right = f :=
by { ext m, simp }

variables (𝕜 Ei G)

/--
The space of continuous multilinear maps on `Π(i : fin (n+1)), Ei i` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : fin n), Ei i.cast_succ` with values in the space
of continuous linear maps on `Ei (last n)`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuous_multilinear_curry_right_equiv 𝕜 Ei G`.
The algebraic version (without topology) is given in `multilinear_curry_right_equiv 𝕜 Ei G`.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of linear isometric equivs.
-/
def continuous_multilinear_curry_right_equiv :
  (continuous_multilinear_map 𝕜 (λ(i : fin n), Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) ≃ₗᵢ[𝕜]
  (continuous_multilinear_map 𝕜 Ei G) :=
linear_isometry_equiv.of_bounds
  { to_fun    := continuous_multilinear_map.uncurry_right,
    map_add'  := λf₁ f₂, by { ext m, refl },
    map_smul' := λc f, by { ext m, refl },
    inv_fun   := continuous_multilinear_map.curry_right,
    left_inv  := continuous_multilinear_map.curry_uncurry_right,
    right_inv := continuous_multilinear_map.uncurry_curry_right }
  (λ f, multilinear_map.mk_continuous_norm_le _ (norm_nonneg f) _)
  (λ f, multilinear_map.mk_continuous_norm_le _ (norm_nonneg f) _)

variables (n G')

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), G` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : fin n), G` with values in the space
of continuous linear maps on `G`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuous_multilinear_curry_right_equiv' 𝕜 n G G'`.
For a version allowing dependent types, see `continuous_multilinear_curry_right_equiv`. When there
are no dependent types, use the primed version as it helps Lean a lot for unification.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of linear isometric equivs. -/
def continuous_multilinear_curry_right_equiv' :
  (G [×n]→L[𝕜] (G →L[𝕜] G')) ≃ₗᵢ[𝕜] (G [×n.succ]→L[𝕜] G') :=
continuous_multilinear_curry_right_equiv 𝕜 (λ (i : fin n.succ), G) G'

variables {n 𝕜 G Ei G'}

@[simp] lemma continuous_multilinear_curry_right_equiv_apply
  (f : (continuous_multilinear_map 𝕜 (λ(i : fin n), Ei i.cast_succ) (Ei (last n) →L[𝕜] G)))
  (v : Π i, Ei i) :
  (continuous_multilinear_curry_right_equiv 𝕜 Ei G) f v = f (init v) (v (last n)) := rfl

@[simp] lemma continuous_multilinear_curry_right_equiv_symm_apply
  (f : continuous_multilinear_map 𝕜 Ei G)
  (v : Π (i : fin n), Ei i.cast_succ) (x : Ei (last n)) :
  (continuous_multilinear_curry_right_equiv 𝕜 Ei G).symm f v x = f (snoc v x) := rfl

@[simp] lemma continuous_multilinear_curry_right_equiv_apply'
  (f : G [×n]→L[𝕜] (G →L[𝕜] G')) (v : fin (n + 1) → G) :
  continuous_multilinear_curry_right_equiv' 𝕜 n G G' f v = f (init v) (v (last n)) := rfl

@[simp] lemma continuous_multilinear_curry_right_equiv_symm_apply'
  (f : G [×n.succ]→L[𝕜] G') (v : fin n → G) (x : G) :
  (continuous_multilinear_curry_right_equiv' 𝕜 n G G').symm f v x = f (snoc v x) := rfl

@[simp] lemma continuous_multilinear_map.curry_right_norm
  (f : continuous_multilinear_map 𝕜 Ei G) : ‖f.curry_right‖ = ‖f‖ :=
(continuous_multilinear_curry_right_equiv 𝕜 Ei G).symm.norm_map f

@[simp] lemma continuous_multilinear_map.uncurry_right_norm
  (f : continuous_multilinear_map 𝕜 (λ i : fin n, Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) :
  ‖f.uncurry_right‖ = ‖f‖ :=
(continuous_multilinear_curry_right_equiv 𝕜 Ei G).norm_map f

/-!
#### Currying with `0` variables

The space of multilinear maps with `0` variables is trivial: such a multilinear map is just an
arbitrary constant (note that multilinear maps in `0` variables need not map `0` to `0`!).
Therefore, the space of continuous multilinear maps on `(fin 0) → G` with values in `E₂` is
isomorphic (and even isometric) to `E₂`. As this is the zeroth step in the construction of iterated
derivatives, we register this isomorphism. -/

section

variables {𝕜 G G'}

/-- Associating to a continuous multilinear map in `0` variables the unique value it takes. -/
def continuous_multilinear_map.uncurry0
  (f : continuous_multilinear_map 𝕜 (λ (i : fin 0), G) G') : G' := f 0

variables (𝕜 G)
/-- Associating to an element `x` of a vector space `E₂` the continuous multilinear map in `0`
variables taking the (unique) value `x` -/
def continuous_multilinear_map.curry0 (x : G') : G [×0]→L[𝕜] G' :=
continuous_multilinear_map.const_of_is_empty 𝕜 _ x

variable {G}
@[simp] lemma continuous_multilinear_map.curry0_apply (x : G') (m : (fin 0) → G) :
  continuous_multilinear_map.curry0 𝕜 G x m = x := rfl

variable {𝕜}
@[simp] lemma continuous_multilinear_map.uncurry0_apply (f : G [×0]→L[𝕜] G') :
  f.uncurry0 = f 0 := rfl

@[simp] lemma continuous_multilinear_map.apply_zero_curry0 (f : G [×0]→L[𝕜] G') {x : fin 0 → G} :
  continuous_multilinear_map.curry0 𝕜 G (f x) = f :=
by { ext m, simp [(subsingleton.elim _ _ : x = m)] }

lemma continuous_multilinear_map.uncurry0_curry0 (f : G [×0]→L[𝕜] G') :
  continuous_multilinear_map.curry0 𝕜 G (f.uncurry0) = f :=
by simp

variables (𝕜 G)
@[simp] lemma continuous_multilinear_map.curry0_uncurry0 (x : G') :
  (continuous_multilinear_map.curry0 𝕜 G x).uncurry0 = x := rfl

@[simp] lemma continuous_multilinear_map.curry0_norm (x : G')  :
  ‖continuous_multilinear_map.curry0 𝕜 G x‖ = ‖x‖ :=
norm_const_of_is_empty _ _ _

variables {𝕜 G}
@[simp] lemma continuous_multilinear_map.fin0_apply_norm (f : G [×0]→L[𝕜] G') {x : fin 0 → G} :
  ‖f x‖ = ‖f‖ :=
begin
  obtain rfl : x = 0 := subsingleton.elim _ _,
  refine le_antisymm (by simpa using f.le_op_norm 0) _,
  have : ‖continuous_multilinear_map.curry0 𝕜 G (f.uncurry0)‖ ≤ ‖f.uncurry0‖ :=
    continuous_multilinear_map.op_norm_le_bound _ (norm_nonneg _) (λm,
      by simp [-continuous_multilinear_map.apply_zero_curry0]),
  simpa
end

lemma continuous_multilinear_map.uncurry0_norm (f : G [×0]→L[𝕜] G') : ‖f.uncurry0‖ = ‖f‖ :=
by simp

variables (𝕜 G G')
/-- The continuous linear isomorphism between elements of a normed space, and continuous multilinear
maps in `0` variables with values in this normed space.

The direct and inverse maps are `uncurry0` and `curry0`. Use these unless you need the full
framework of linear isometric equivs. -/
def continuous_multilinear_curry_fin0 : (G [×0]→L[𝕜] G') ≃ₗᵢ[𝕜] G' :=
{ to_fun    := λf, continuous_multilinear_map.uncurry0 f,
  inv_fun   := λf, continuous_multilinear_map.curry0 𝕜 G f,
  map_add'  := λf g, rfl,
  map_smul' := λc f, rfl,
  left_inv  := continuous_multilinear_map.uncurry0_curry0,
  right_inv := continuous_multilinear_map.curry0_uncurry0 𝕜 G,
  norm_map' := continuous_multilinear_map.uncurry0_norm }

variables {𝕜 G G'}

@[simp] lemma continuous_multilinear_curry_fin0_apply (f : G [×0]→L[𝕜] G') :
  continuous_multilinear_curry_fin0 𝕜 G G' f = f 0 := rfl

@[simp] lemma continuous_multilinear_curry_fin0_symm_apply (x : G') (v : (fin 0) → G) :
  (continuous_multilinear_curry_fin0 𝕜 G G').symm x v = x := rfl

end

/-! #### With 1 variable -/

variables (𝕜 G G')

/-- Continuous multilinear maps from `G^1` to `G'` are isomorphic with continuous linear maps from
`G` to `G'`. -/
def continuous_multilinear_curry_fin1 : (G [×1]→L[𝕜] G') ≃ₗᵢ[𝕜] (G →L[𝕜] G') :=
(continuous_multilinear_curry_right_equiv 𝕜 (λ (i : fin 1), G) G').symm.trans
(continuous_multilinear_curry_fin0 𝕜 G (G →L[𝕜] G'))

variables {𝕜 G G'}

@[simp] lemma continuous_multilinear_curry_fin1_apply (f : G [×1]→L[𝕜] G') (x : G) :
  continuous_multilinear_curry_fin1 𝕜 G G' f x = f (fin.snoc 0 x) := rfl

@[simp] lemma continuous_multilinear_curry_fin1_symm_apply
  (f : G →L[𝕜] G') (v : (fin 1) → G) :
  (continuous_multilinear_curry_fin1 𝕜 G G').symm f v = f (v 0) := rfl

namespace continuous_multilinear_map

variables (𝕜 G G')

/-- An equivalence of the index set defines a linear isometric equivalence between the spaces
of multilinear maps. -/
def dom_dom_congr (σ : ι ≃ ι') :
  continuous_multilinear_map 𝕜 (λ _ : ι, G) G' ≃ₗᵢ[𝕜]
    continuous_multilinear_map 𝕜 (λ _ : ι', G) G' :=
linear_isometry_equiv.of_bounds
  { to_fun := λ f, (multilinear_map.dom_dom_congr σ f.to_multilinear_map).mk_continuous ‖f‖ $
      λ m, (f.le_op_norm (λ i, m (σ i))).trans_eq $ by rw [← σ.prod_comp],
    inv_fun := λ f, (multilinear_map.dom_dom_congr σ.symm f.to_multilinear_map).mk_continuous ‖f‖ $
      λ m, (f.le_op_norm (λ i, m (σ.symm i))).trans_eq $ by rw [← σ.symm.prod_comp],
    left_inv := λ f, ext $ λ m, congr_arg f $ by simp only [σ.symm_apply_apply],
    right_inv := λ f, ext $ λ m, congr_arg f $ by simp only [σ.apply_symm_apply],
    map_add' := λ f g, rfl,
    map_smul' := λ c f, rfl }
  (λ f, multilinear_map.mk_continuous_norm_le _ (norm_nonneg f) _)
  (λ f, multilinear_map.mk_continuous_norm_le _ (norm_nonneg f) _)

variables {𝕜 G G'}

section

/-- A continuous multilinear map with variables indexed by `ι ⊕ ι'` defines a continuous multilinear
map with variables indexed by `ι` taking values in the space of continuous multilinear maps with
variables indexed by `ι'`. -/
def curry_sum (f : continuous_multilinear_map 𝕜 (λ x : ι ⊕ ι', G) G') :
  continuous_multilinear_map 𝕜 (λ x : ι, G) (continuous_multilinear_map 𝕜 (λ x : ι', G) G') :=
multilinear_map.mk_continuous_multilinear (multilinear_map.curry_sum f.to_multilinear_map) (‖f‖) $
  λ m m', by simpa [fintype.prod_sum_type, mul_assoc] using f.le_op_norm (sum.elim m m')

@[simp] lemma curry_sum_apply (f : continuous_multilinear_map 𝕜 (λ x : ι ⊕ ι', G) G')
  (m : ι → G) (m' : ι' → G) :
  f.curry_sum m m' = f (sum.elim m m') :=
rfl

/-- A continuous multilinear map with variables indexed by `ι` taking values in the space of
continuous multilinear maps with variables indexed by `ι'` defines a continuous multilinear map with
variables indexed by `ι ⊕ ι'`. -/
def uncurry_sum
  (f : continuous_multilinear_map 𝕜 (λ x : ι, G) (continuous_multilinear_map 𝕜 (λ x : ι', G) G')) :
  continuous_multilinear_map 𝕜 (λ x : ι ⊕ ι', G) G' :=
multilinear_map.mk_continuous
  (to_multilinear_map_linear.comp_multilinear_map f.to_multilinear_map).uncurry_sum (‖f‖) $ λ m,
  by simpa [fintype.prod_sum_type, mul_assoc]
    using (f (m ∘ sum.inl)).le_of_op_norm_le (m ∘ sum.inr) (f.le_op_norm _)

@[simp] lemma uncurry_sum_apply
  (f : continuous_multilinear_map 𝕜 (λ x : ι, G) (continuous_multilinear_map 𝕜 (λ x : ι', G) G'))
  (m : ι ⊕ ι' → G) :
  f.uncurry_sum m = f (m ∘ sum.inl) (m ∘ sum.inr) :=
rfl

variables (𝕜 ι ι' G G')

/-- Linear isometric equivalence between the space of continuous multilinear maps with variables
indexed by `ι ⊕ ι'` and the space of continuous multilinear maps with variables indexed by `ι`
taking values in the space of continuous multilinear maps with variables indexed by `ι'`.

The forward and inverse functions are `continuous_multilinear_map.curry_sum`
and `continuous_multilinear_map.uncurry_sum`. Use this definition only if you need
some properties of `linear_isometry_equiv`. -/
def curry_sum_equiv : continuous_multilinear_map 𝕜 (λ x : ι ⊕ ι', G) G' ≃ₗᵢ[𝕜]
  continuous_multilinear_map 𝕜 (λ x : ι, G) (continuous_multilinear_map 𝕜 (λ x : ι', G) G') :=
linear_isometry_equiv.of_bounds
  { to_fun := curry_sum,
    inv_fun := uncurry_sum,
    map_add' := λ f g, by { ext, refl },
    map_smul' := λ c f, by { ext, refl },
    left_inv := λ f, by { ext m, exact congr_arg f (sum.elim_comp_inl_inr m) },
    right_inv := λ f, by { ext m₁ m₂, change f _ _ = f _ _,
      rw [sum.elim_comp_inl, sum.elim_comp_inr] } }
  (λ f, multilinear_map.mk_continuous_multilinear_norm_le _ (norm_nonneg f) _)
  (λ f, multilinear_map.mk_continuous_norm_le _ (norm_nonneg f) _)

end

section

variables (𝕜 G G') {k l : ℕ} {s : finset (fin n)}

/-- If `s : finset (fin n)` is a finite set of cardinality `k` and its complement has cardinality
`l`, then the space of continuous multilinear maps `G [×n]→L[𝕜] G'` of `n` variables is isomorphic
to the space of continuous multilinear maps `G [×k]→L[𝕜] G [×l]→L[𝕜] G'` of `k` variables taking
values in the space of continuous multilinear maps of `l` variables. -/
def curry_fin_finset {k l n : ℕ} {s : finset (fin n)}
  (hk : s.card = k) (hl : sᶜ.card = l) :
  (G [×n]→L[𝕜] G') ≃ₗᵢ[𝕜] (G [×k]→L[𝕜] G [×l]→L[𝕜] G') :=
(dom_dom_congr 𝕜 G G' (fin_sum_equiv_of_finset hk hl).symm).trans
  (curry_sum_equiv 𝕜 (fin k) (fin l) G G')

variables {𝕜 G G'}

@[simp] lemma curry_fin_finset_apply (hk : s.card = k) (hl : sᶜ.card = l)
  (f : G [×n]→L[𝕜] G') (mk : fin k → G) (ml : fin l → G) :
  curry_fin_finset 𝕜 G G' hk hl f mk ml =
    f (λ i, sum.elim mk ml ((fin_sum_equiv_of_finset hk hl).symm i)) :=
rfl

@[simp] lemma curry_fin_finset_symm_apply (hk : s.card = k) (hl : sᶜ.card = l)
  (f : G [×k]→L[𝕜] G [×l]→L[𝕜] G') (m : fin n → G) :
  (curry_fin_finset 𝕜 G G' hk hl).symm f m =
    f (λ i, m $ fin_sum_equiv_of_finset hk hl (sum.inl i))
      (λ i, m $ fin_sum_equiv_of_finset hk hl (sum.inr i)) :=
rfl

@[simp] lemma curry_fin_finset_symm_apply_piecewise_const (hk : s.card = k) (hl : sᶜ.card = l)
  (f : G [×k]→L[𝕜] G [×l]→L[𝕜] G') (x y : G) :
  (curry_fin_finset 𝕜 G G' hk hl).symm f (s.piecewise (λ _, x) (λ _, y)) = f (λ _, x) (λ _, y) :=
multilinear_map.curry_fin_finset_symm_apply_piecewise_const hk hl _ x y

@[simp] lemma curry_fin_finset_symm_apply_const (hk : s.card = k) (hl : sᶜ.card = l)
  (f : G [×k]→L[𝕜] G [×l]→L[𝕜] G') (x : G) :
  (curry_fin_finset 𝕜 G G' hk hl).symm f (λ _, x) = f (λ _, x) (λ _, x) :=
rfl

@[simp] lemma curry_fin_finset_apply_const (hk : s.card = k) (hl : sᶜ.card = l)
  (f : G [×n]→L[𝕜] G') (x y : G) :
  curry_fin_finset 𝕜 G G' hk hl f (λ _, x) (λ _, y) = f (s.piecewise (λ _, x) (λ _, y)) :=
begin
  refine (curry_fin_finset_symm_apply_piecewise_const hk hl _ _ _).symm.trans _, -- `rw` fails
  rw linear_isometry_equiv.symm_apply_apply
end

end

end continuous_multilinear_map

end currying
