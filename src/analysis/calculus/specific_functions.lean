/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.iterated_deriv
import analysis.inner_product_space.euclidean_dist

/-!
# Infinitely smooth bump function

In this file we construct several infinitely smooth functions with properties that an analytic
function cannot have:

* `exp_neg_inv_glue` is equal to zero for `x ≤ 0` and is strictly positive otherwise; it is given by
  `x ↦ exp (-1/x)` for `x > 0`;

* `real.smooth_transition` is equal to zero for `x ≤ 0` and is equal to one for `x ≥ 1`; it is given
  by `exp_neg_inv_glue x / (exp_neg_inv_glue x + exp_neg_inv_glue (1 - x))`;

* `f : times_cont_diff_bump_of_inner c`, where `c` is a point in an inner product space, is
  a bundled smooth function such that

  - `f` is equal to `1` in `metric.closed_ball c f.r`;
  - `support f = metric.ball c f.R`;
  - `0 ≤ f x ≤ 1` for all `x`.

  The structure `times_cont_diff_bump_of_inner` contains the data required to construct the
  function: real numbers `r`, `R`, and proofs of `0 < r < R`. The function itself is available
  through `coe_fn`.

* `f : times_cont_diff_bump c`, where `c` is a point in a finite dimensional real vector space, is a
  bundled smooth function such that

  - `f` is equal to `1` in `euclidean.closed_ball c f.r`;
  - `support f = euclidean.ball c f.R`;
  - `0 ≤ f x ≤ 1` for all `x`.

  The structure `times_cont_diff_bump` contains the data required to construct the function: real
  numbers `r`, `R`, and proofs of `0 < r < R`. The function itself is available through `coe_fn`.
-/

noncomputable theory
open_locale classical topological_space

open polynomial real filter set function

/-- `exp_neg_inv_glue` is the real function given by `x ↦ exp (-1/x)` for `x > 0` and `0`
for `x ≤ 0`. It is a basic building block to construct smooth partitions of unity. Its main property
is that it vanishes for `x ≤ 0`, it is positive for `x > 0`, and the junction between the two
behaviors is flat enough to retain smoothness. The fact that this function is `C^∞` is proved in
`exp_neg_inv_glue.smooth`. -/
def exp_neg_inv_glue (x : ℝ) : ℝ := if x ≤ 0 then 0 else exp (-x⁻¹)

namespace exp_neg_inv_glue

/-- Our goal is to prove that `exp_neg_inv_glue` is `C^∞`. For this, we compute its successive
derivatives for `x > 0`. The `n`-th derivative is of the form `P_aux n (x) exp(-1/x) / x^(2 n)`,
where `P_aux n` is computed inductively. -/
noncomputable def P_aux : ℕ → polynomial ℝ
| 0 := 1
| (n+1) := X^2 * (P_aux n).derivative  + (1 - C ↑(2 * n) * X) * (P_aux n)

/-- Formula for the `n`-th derivative of `exp_neg_inv_glue`, as an auxiliary function `f_aux`. -/
def f_aux (n : ℕ) (x : ℝ) : ℝ :=
if x ≤ 0 then 0 else (P_aux n).eval x * exp (-x⁻¹) / x^(2 * n)

/-- The `0`-th auxiliary function `f_aux 0` coincides with `exp_neg_inv_glue`, by definition. -/
lemma f_aux_zero_eq : f_aux 0 = exp_neg_inv_glue :=
begin
   ext x,
   by_cases h : x ≤ 0,
   { simp [exp_neg_inv_glue, f_aux, h] },
   { simp [h, exp_neg_inv_glue, f_aux, ne_of_gt (not_le.1 h), P_aux] }
end

/-- For positive values, the derivative of the `n`-th auxiliary function `f_aux n`
(given in this statement in unfolded form) is the `n+1`-th auxiliary function, since
the polynomial `P_aux (n+1)` was chosen precisely to ensure this. -/
lemma f_aux_deriv (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
  has_deriv_at (λx, (P_aux n).eval x * exp (-x⁻¹) / x^(2 * n))
    ((P_aux (n+1)).eval x * exp (-x⁻¹) / x^(2 * (n + 1))) x :=
begin
  have A : ∀k:ℕ, 2 * (k + 1) - 1 = 2 * k + 1,
  { assume k,
    rw tsub_eq_iff_eq_add_of_le,
    { ring },
    { simpa [mul_add] using add_le_add (zero_le (2 * k)) one_le_two } },
  convert (((P_aux n).has_deriv_at x).mul
               (((has_deriv_at_exp _).comp x (has_deriv_at_inv hx).neg))).div
            (has_deriv_at_pow (2 * n) x) (pow_ne_zero _ hx) using 1,
  field_simp [hx, P_aux],
  -- `ring_exp` can't solve `p ∨ q` goal generated by `mul_eq_mul_right_iff`
  cases n; simp [nat.succ_eq_add_one, A, -mul_eq_mul_right_iff]; ring_exp
end

/-- For positive values, the derivative of the `n`-th auxiliary function `f_aux n`
is the `n+1`-th auxiliary function. -/
lemma f_aux_deriv_pos (n : ℕ) (x : ℝ) (hx : 0 < x) :
  has_deriv_at (f_aux n) ((P_aux (n+1)).eval x * exp (-x⁻¹) / x^(2 * (n + 1))) x :=
begin
  apply (f_aux_deriv n x (ne_of_gt hx)).congr_of_eventually_eq,
  filter_upwards [lt_mem_nhds hx],
  assume y hy,
  simp [f_aux, hy.not_le]
end

/-- To get differentiability at `0` of the auxiliary functions, we need to know that their limit
is `0`, to be able to apply general differentiability extension theorems. This limit is checked in
this lemma. -/
lemma f_aux_limit (n : ℕ) :
  tendsto (λx, (P_aux n).eval x * exp (-x⁻¹) / x^(2 * n)) (𝓝[Ioi 0] 0) (𝓝 0) :=
begin
  have A : tendsto (λx, (P_aux n).eval x) (𝓝[Ioi 0] 0) (𝓝 ((P_aux n).eval 0)) :=
  (P_aux n).continuous_within_at,
  have B : tendsto (λx, exp (-x⁻¹) / x^(2 * n)) (𝓝[Ioi 0] 0) (𝓝 0),
  { convert (tendsto_pow_mul_exp_neg_at_top_nhds_0 (2 * n)).comp tendsto_inv_zero_at_top,
    ext x,
    field_simp },
  convert A.mul B;
  simp [mul_div_assoc]
end

/-- Deduce from the limiting behavior at `0` of its derivative and general differentiability
extension theorems that the auxiliary function `f_aux n` is differentiable at `0`,
with derivative `0`. -/
lemma f_aux_deriv_zero (n : ℕ) : has_deriv_at (f_aux n) 0 0 :=
begin
  -- we check separately differentiability on the left and on the right
  have A : has_deriv_within_at (f_aux n) (0 : ℝ) (Iic 0) 0,
  { apply (has_deriv_at_const (0 : ℝ) (0 : ℝ)).has_deriv_within_at.congr,
    { assume y hy,
      simp at hy,
      simp [f_aux, hy] },
    { simp [f_aux, le_refl] } },
  have B : has_deriv_within_at (f_aux n) (0 : ℝ) (Ici 0) 0,
  { have diff : differentiable_on ℝ (f_aux n) (Ioi 0) :=
      λx hx, (f_aux_deriv_pos n x hx).differentiable_at.differentiable_within_at,
    -- next line is the nontrivial bit of this proof, appealing to differentiability
    -- extension results.
    apply has_deriv_at_interval_left_endpoint_of_tendsto_deriv diff _ self_mem_nhds_within,
    { refine (f_aux_limit (n+1)).congr' _,
      apply mem_of_superset self_mem_nhds_within (λx hx, _),
      simp [(f_aux_deriv_pos n x hx).deriv] },
    { have : f_aux n 0 = 0, by simp [f_aux, le_refl],
      simp only [continuous_within_at, this],
      refine (f_aux_limit n).congr' _,
      apply mem_of_superset self_mem_nhds_within (λx hx, _),
      have : ¬(x ≤ 0), by simpa using hx,
      simp [f_aux, this] } },
  simpa using A.union B,
end

/-- At every point, the auxiliary function `f_aux n` has a derivative which is
equal to `f_aux (n+1)`. -/
lemma f_aux_has_deriv_at (n : ℕ) (x : ℝ) : has_deriv_at (f_aux n) (f_aux (n+1) x) x :=
begin
  -- check separately the result for `x < 0`, where it is trivial, for `x > 0`, where it is done
  -- in `f_aux_deriv_pos`, and for `x = 0`, done in
  -- `f_aux_deriv_zero`.
  rcases lt_trichotomy x 0 with hx|hx|hx,
  { have : f_aux (n+1) x = 0, by simp [f_aux, le_of_lt hx],
    rw this,
    apply (has_deriv_at_const x (0 : ℝ)).congr_of_eventually_eq,
    filter_upwards [gt_mem_nhds hx],
    assume y hy,
    simp [f_aux, hy.le] },
  { have : f_aux (n + 1) 0 = 0, by simp [f_aux, le_refl],
    rw [hx, this],
    exact f_aux_deriv_zero n },
  { have : f_aux (n+1) x = (P_aux (n+1)).eval x * exp (-x⁻¹) / x^(2 * (n+1)),
      by simp [f_aux, not_le_of_gt hx],
    rw this,
    exact f_aux_deriv_pos n x hx },
end

/-- The successive derivatives of the auxiliary function `f_aux 0` are the
functions `f_aux n`, by induction. -/
lemma f_aux_iterated_deriv (n : ℕ) : iterated_deriv n (f_aux 0) = f_aux n :=
begin
  induction n with n IH,
  { simp },
  { simp [iterated_deriv_succ, IH],
    ext x,
    exact (f_aux_has_deriv_at n x).deriv }
end

/-- The function `exp_neg_inv_glue` is smooth. -/
protected theorem times_cont_diff {n} : times_cont_diff ℝ n exp_neg_inv_glue :=
begin
  rw ← f_aux_zero_eq,
  apply times_cont_diff_of_differentiable_iterated_deriv (λ m hm, _),
  rw f_aux_iterated_deriv m,
  exact λ x, (f_aux_has_deriv_at m x).differentiable_at
end

/-- The function `exp_neg_inv_glue` vanishes on `(-∞, 0]`. -/
lemma zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : exp_neg_inv_glue x = 0 :=
by simp [exp_neg_inv_glue, hx]

/-- The function `exp_neg_inv_glue` is positive on `(0, +∞)`. -/
lemma pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < exp_neg_inv_glue x :=
by simp [exp_neg_inv_glue, not_le.2 hx, exp_pos]

/-- The function exp_neg_inv_glue` is nonnegative. -/
lemma nonneg (x : ℝ) : 0 ≤ exp_neg_inv_glue x :=
begin
  cases le_or_gt x 0,
  { exact ge_of_eq (zero_of_nonpos h) },
  { exact le_of_lt (pos_of_pos h) }
end

end exp_neg_inv_glue

/-- An infinitely smooth function `f : ℝ → ℝ` such that `f x = 0` for `x ≤ 0`,
`f x = 1` for `1 ≤ x`, and `0 < f x < 1` for `0 < x < 1`. -/
def real.smooth_transition (x : ℝ) : ℝ :=
exp_neg_inv_glue x / (exp_neg_inv_glue x + exp_neg_inv_glue (1 - x))

namespace real

namespace smooth_transition

variables {x : ℝ}

open exp_neg_inv_glue

lemma pos_denom (x) : 0 < exp_neg_inv_glue x + exp_neg_inv_glue (1 - x) :=
((@zero_lt_one ℝ _ _).lt_or_lt x).elim
  (λ hx, add_pos_of_pos_of_nonneg (pos_of_pos hx) (nonneg _))
  (λ hx, add_pos_of_nonneg_of_pos (nonneg _) (pos_of_pos $ sub_pos.2 hx))

lemma one_of_one_le (h : 1 ≤ x) : smooth_transition x = 1 :=
(div_eq_one_iff_eq $ (pos_denom x).ne').2 $ by rw [zero_of_nonpos (sub_nonpos.2 h), add_zero]

lemma zero_of_nonpos (h : x ≤ 0) : smooth_transition x = 0 :=
by rw [smooth_transition, zero_of_nonpos h, zero_div]

lemma le_one (x : ℝ) : smooth_transition x ≤ 1 :=
(div_le_one (pos_denom x)).2 $ le_add_of_nonneg_right (nonneg _)

lemma nonneg (x : ℝ) : 0 ≤ smooth_transition x :=
div_nonneg (exp_neg_inv_glue.nonneg _) (pos_denom x).le

lemma lt_one_of_lt_one (h : x < 1) : smooth_transition x < 1 :=
(div_lt_one $ pos_denom x).2 $ lt_add_of_pos_right _ $ pos_of_pos $ sub_pos.2 h

lemma pos_of_pos (h : 0 < x) : 0 < smooth_transition x :=
div_pos (exp_neg_inv_glue.pos_of_pos h) (pos_denom x)

protected lemma times_cont_diff {n} : times_cont_diff ℝ n smooth_transition :=
exp_neg_inv_glue.times_cont_diff.div
  (exp_neg_inv_glue.times_cont_diff.add $ exp_neg_inv_glue.times_cont_diff.comp $
    times_cont_diff_const.sub times_cont_diff_id) $
  λ x, (pos_denom x).ne'

protected lemma times_cont_diff_at {x n} : times_cont_diff_at ℝ n smooth_transition x :=
smooth_transition.times_cont_diff.times_cont_diff_at

end smooth_transition

end real

variable {E : Type*}

/-- `f : times_cont_diff_bump_of_inner c`, where `c` is a point in an inner product space, is a
bundled smooth function such that

- `f` is equal to `1` in `metric.closed_ball c f.r`;
- `support f = metric.ball c f.R`;
- `0 ≤ f x ≤ 1` for all `x`.

The structure `times_cont_diff_bump_of_inner` contains the data required to construct the function:
real numbers `r`, `R`, and proofs of `0 < r < R`. The function itself is available through
`coe_fn`. -/
structure times_cont_diff_bump_of_inner (c : E) :=
(r R : ℝ)
(r_pos : 0 < r)
(r_lt_R : r < R)

namespace times_cont_diff_bump_of_inner

lemma R_pos {c : E} (f : times_cont_diff_bump_of_inner c) : 0 < f.R := f.r_pos.trans f.r_lt_R

instance (c : E) : inhabited (times_cont_diff_bump_of_inner c) := ⟨⟨1, 2, zero_lt_one, one_lt_two⟩⟩

variables [inner_product_space ℝ E] {c : E} (f : times_cont_diff_bump_of_inner c) {x : E}

/-- The function defined by `f : times_cont_diff_bump_of_inner c`. Use automatic coercion to
function instead. -/
def to_fun (f : times_cont_diff_bump_of_inner c) : E → ℝ :=
λ x, real.smooth_transition ((f.R - dist x c) / (f.R - f.r))

instance : has_coe_to_fun (times_cont_diff_bump_of_inner c) (λ _, E → ℝ) := ⟨to_fun⟩

open real (smooth_transition) real.smooth_transition metric

lemma one_of_mem_closed_ball (hx : x ∈ closed_ball c f.r) :
  f x = 1 :=
one_of_one_le $ (one_le_div (sub_pos.2 f.r_lt_R)).2 $ sub_le_sub_left hx _

lemma nonneg : 0 ≤ f x := nonneg _

lemma le_one : f x ≤ 1 := le_one _

lemma pos_of_mem_ball (hx : x ∈ ball c f.R) : 0 < f x :=
pos_of_pos $ div_pos (sub_pos.2 hx) (sub_pos.2 f.r_lt_R)

lemma lt_one_of_lt_dist (h : f.r < dist x c) : f x < 1 :=
lt_one_of_lt_one $ (div_lt_one (sub_pos.2 f.r_lt_R)).2 $ sub_lt_sub_left h _

lemma zero_of_le_dist (hx : f.R ≤ dist x c) : f x = 0 :=
zero_of_nonpos $ div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hx) (sub_nonneg.2 f.r_lt_R.le)

lemma support_eq : support (f : E → ℝ) = metric.ball c f.R :=
begin
  ext x,
  suffices : f x ≠ 0 ↔ dist x c < f.R, by simpa [mem_support],
  cases lt_or_le (dist x c) f.R with hx hx,
  { simp [hx, (f.pos_of_mem_ball hx).ne'] },
  { simp [hx.not_lt, f.zero_of_le_dist hx] }
end

lemma eventually_eq_one_of_mem_ball (h : x ∈ ball c f.r) :
  f =ᶠ[𝓝 x] 1 :=
((is_open_lt (continuous_id.dist continuous_const) continuous_const).eventually_mem h).mono $
  λ z hz, f.one_of_mem_closed_ball (le_of_lt hz)

lemma eventually_eq_one : f =ᶠ[𝓝 c] 1 :=
f.eventually_eq_one_of_mem_ball (mem_ball_self f.r_pos)

protected lemma times_cont_diff_at {n} :
  times_cont_diff_at ℝ n f x :=
begin
  rcases em (x = c) with rfl|hx,
  { refine times_cont_diff_at.congr_of_eventually_eq _ f.eventually_eq_one,
    rw pi.one_def,
    exact times_cont_diff_at_const },
  { exact real.smooth_transition.times_cont_diff_at.comp x
      (times_cont_diff_at.div_const $ times_cont_diff_at_const.sub $
        times_cont_diff_at_id.dist times_cont_diff_at_const hx) }
end

protected lemma times_cont_diff {n} :
  times_cont_diff ℝ n f :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ y, f.times_cont_diff_at

protected lemma times_cont_diff_within_at {s n} :
  times_cont_diff_within_at ℝ n f s x :=
f.times_cont_diff_at.times_cont_diff_within_at

end times_cont_diff_bump_of_inner

/-- `f : times_cont_diff_bump c`, where `c` is a point in a finite dimensional real vector space, is
a bundled smooth function such that

  - `f` is equal to `1` in `euclidean.closed_ball c f.r`;
  - `support f = euclidean.ball c f.R`;
  - `0 ≤ f x ≤ 1` for all `x`.

The structure `times_cont_diff_bump` contains the data required to construct the function: real
numbers `r`, `R`, and proofs of `0 < r < R`. The function itself is available through `coe_fn`.-/
structure times_cont_diff_bump [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E] (c : E)
  extends times_cont_diff_bump_of_inner (to_euclidean c)

namespace times_cont_diff_bump

variables [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E] {c x : E}
  (f : times_cont_diff_bump c)

/-- The function defined by `f : times_cont_diff_bump c`. Use automatic coercion to function
instead. -/
def to_fun (f : times_cont_diff_bump c) : E → ℝ := f.to_times_cont_diff_bump_of_inner ∘ to_euclidean

instance : has_coe_to_fun (times_cont_diff_bump c) (λ _, E → ℝ) := ⟨to_fun⟩

instance (c : E) : inhabited (times_cont_diff_bump c) := ⟨⟨default _⟩⟩

lemma R_pos : 0 < f.R := f.to_times_cont_diff_bump_of_inner.R_pos

lemma coe_eq_comp : ⇑f = f.to_times_cont_diff_bump_of_inner ∘ to_euclidean := rfl

lemma one_of_mem_closed_ball (hx : x ∈ euclidean.closed_ball c f.r) :
  f x = 1 :=
f.to_times_cont_diff_bump_of_inner.one_of_mem_closed_ball hx

lemma nonneg : 0 ≤ f x := f.to_times_cont_diff_bump_of_inner.nonneg

lemma le_one : f x ≤ 1 := f.to_times_cont_diff_bump_of_inner.le_one

lemma pos_of_mem_ball (hx : x ∈ euclidean.ball c f.R) : 0 < f x :=
f.to_times_cont_diff_bump_of_inner.pos_of_mem_ball hx

lemma lt_one_of_lt_dist (h : f.r < euclidean.dist x c) : f x < 1 :=
f.to_times_cont_diff_bump_of_inner.lt_one_of_lt_dist h

lemma zero_of_le_dist (hx : f.R ≤ euclidean.dist x c) : f x = 0 :=
f.to_times_cont_diff_bump_of_inner.zero_of_le_dist hx

lemma support_eq : support (f : E → ℝ) = euclidean.ball c f.R :=
by rw [euclidean.ball_eq_preimage, ← f.to_times_cont_diff_bump_of_inner.support_eq,
  ← support_comp_eq_preimage, coe_eq_comp]

lemma closure_support_eq : closure (support f) = euclidean.closed_ball c f.R :=
by rw [f.support_eq, euclidean.closure_ball _ f.R_pos]

lemma compact_closure_support : is_compact (closure (support f)) :=
by { rw f.closure_support_eq, exact euclidean.is_compact_closed_ball }

lemma eventually_eq_one_of_mem_ball (h : x ∈ euclidean.ball c f.r) :
  f =ᶠ[𝓝 x] 1 :=
to_euclidean.continuous_at (f.to_times_cont_diff_bump_of_inner.eventually_eq_one_of_mem_ball h)

lemma eventually_eq_one : f =ᶠ[𝓝 c] 1 :=
f.eventually_eq_one_of_mem_ball $ euclidean.mem_ball_self f.r_pos

protected lemma times_cont_diff {n} :
  times_cont_diff ℝ n f :=
f.to_times_cont_diff_bump_of_inner.times_cont_diff.comp (to_euclidean : E ≃L[ℝ] _).times_cont_diff

protected lemma times_cont_diff_at {n} :
  times_cont_diff_at ℝ n f x :=
f.times_cont_diff.times_cont_diff_at

protected lemma times_cont_diff_within_at {s n} :
  times_cont_diff_within_at ℝ n f s x :=
f.times_cont_diff_at.times_cont_diff_within_at

lemma exists_closure_support_subset {s : set E} (hs : s ∈ 𝓝 c) :
  ∃ f : times_cont_diff_bump c, closure (support f) ⊆ s :=
let ⟨R, h0, hR⟩ := euclidean.nhds_basis_closed_ball.mem_iff.1 hs
in ⟨⟨⟨R / 2, R, half_pos h0, half_lt_self h0⟩⟩, by rwa closure_support_eq⟩

lemma exists_closure_subset {R : ℝ} (hR : 0 < R)
  {s : set E} (hs : is_closed s) (hsR : s ⊆ euclidean.ball c R) :
  ∃ f : times_cont_diff_bump c, f.R = R ∧ s ⊆ euclidean.ball c f.r :=
begin
  rcases euclidean.exists_pos_lt_subset_ball hR hs hsR with ⟨r, hr, hsr⟩,
  exact ⟨⟨⟨r, R, hr.1, hr.2⟩⟩, rfl, hsr⟩
end

end times_cont_diff_bump

open finite_dimensional metric

/-- If `E` is a finite dimensional normed space over `ℝ`, then for any point `x : E` and its
neighborhood `s` there exists an infinitely smooth function with the following properties:

* `f y = 1` in a neighborhood of `x`;
* `f y = 0` outside of `s`;
*  moreover, `closure (support f) ⊆ s` and `closure (support f)` is a compact set;
* `f y ∈ [0, 1]` for all `y`.

This lemma is a simple wrapper around lemmas about bundled smooth bump functions, see
`times_cont_diff_bump`. -/
lemma exists_times_cont_diff_bump_function_of_mem_nhds [normed_group E] [normed_space ℝ E]
  [finite_dimensional ℝ E] {x : E} {s : set E} (hs : s ∈ 𝓝 x) :
  ∃ f : E → ℝ, f =ᶠ[𝓝 x] 1 ∧ (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧ times_cont_diff ℝ ⊤ f ∧
    is_compact (closure $ support f) ∧ closure (support f) ⊆ s :=
let ⟨f, hf⟩ := times_cont_diff_bump.exists_closure_support_subset hs in
⟨f, f.eventually_eq_one, λ y, ⟨f.nonneg, f.le_one⟩, f.times_cont_diff,
  f.compact_closure_support, hf⟩
