/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.formal_multilinear_series
import analysis.specific_limits

/-!
# Analytic functions

A function is analytic in one dimension around `0` if it can be written as a converging power series
`Σ pₙ zⁿ`. This definition can be extended to any dimension (even in infinite dimension) by
requiring that `pₙ` is a continuous `n`-multilinear map. In general, `pₙ` is not unique (in two
dimensions, taking `p₂ (x, y) (x', y') = x y'` or `y x'` gives the same map when applied to a
vector `(x, y) (x, y)`). A way to guarantee uniqueness is to take a symmetric `pₙ`, but this is not
always possible in nonzero characteristic (in characteristic 2, the previous example has no
symmetric representative). Therefore, we do not insist on symmetry or uniqueness in the definition,
and we only require the existence of a converging series.

The general framework is important to say that the exponential map on bounded operators on a Banach
space is analytic, as well as the inverse on invertible operators.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `p.radius`: the largest `r : ennreal` such that `∥p n∥ * r^n` grows subexponentially, defined as
  a liminf.
* `p.le_radius_of_bound`, `p.bound_of_lt_radius`, `p.geometric_bound_of_lt_radius`: relating the
  value of the radius with the growth of `∥p n∥ * r^n`.
* `p.partial_sum n x`: the sum `∑_{i = 0}^{n-1} pᵢ xⁱ`.
* `p.sum x`: the sum `∑'_{i = 0}^{∞} pᵢ xⁱ`.

Additionally, let `f` be a function from `E` to `F`.

* `has_fpower_series_on_ball f p x r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₙ yⁿ`.
* `has_fpower_series_at f p x`: on some ball of center `x` with positive radius, holds
  `has_fpower_series_on_ball f p x r`.
* `analytic_at 𝕜 f x`: there exists a power series `p` such that holds
  `has_fpower_series_at f p x`.

We develop the basic properties of these notions, notably:
* If a function admits a power series, it is continuous (see
  `has_fpower_series_on_ball.continuous_on` and `has_fpower_series_at.continuous_at` and
  `analytic_at.continuous_at`).
* In a complete space, the sum of a formal power series with positive radius is well defined on the
  disk of convergence, see `formal_multilinear_series.has_fpower_series_on_ball`.
* If a function admits a power series in a ball, then it is analytic at any point `y` of this ball,
  and the power series there can be expressed in terms of the initial power series `p` as
  `p.change_origin y`. See `has_fpower_series_on_ball.change_origin`. It follows in particular that
  the set of points at which a given function is analytic is open, see `is_open_analytic_at`.

## Implementation details

We only introduce the radius of convergence of a power series, as `p.radius`.
For a power series in finitely many dimensions, there is a finer (directional, coordinate-dependent)
notion, describing the polydisk of convergence. This notion is more specific, and not necessary to
build the general theory. We do not define it here.
-/

noncomputable theory

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]

open_locale topological_space classical big_operators nnreal
open set filter asymptotics

/-! ### The radius of a formal multilinear series -/

namespace formal_multilinear_series

/-- The radius of a formal multilinear series is the largest `r` such that the sum `Σ pₙ yⁿ`
converges for all `∥y∥ < r`. -/
def radius (p : formal_multilinear_series 𝕜 E F) : ennreal :=
⨆ (r : ℝ≥0) (hr : ∃ C, ∀ n, nnnorm (p n) * r ^ n ≤ C), (r : ennreal)

/-- If `∥pₙ∥ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
lemma le_radius_of_bound (p : formal_multilinear_series 𝕜 E F) (C : ℝ≥0) {r : ℝ≥0}
  (h : ∀ (n : ℕ), nnnorm (p n) * r^n ≤ C) : (r : ennreal) ≤ p.radius :=
le_supr_of_le r (le_supr (λ _, (r : ennreal)) $ Exists.intro C h)

/-- If `∥pₙ∥ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
lemma le_radius_of_is_O (p : formal_multilinear_series 𝕜 E F) {r : ℝ≥0}
  (h : is_O (λ n, ∥p n∥ * r^n) (λ n, (1 : ℝ)) at_top) : (r : ennreal) ≤ p.radius :=
begin
  rcases is_O_one_nat_at_top_iff.1 h with ⟨C, hC⟩,
  refine p.le_radius_of_bound (nnreal.of_real C)
    (λ n, nnreal.coe_le_coe.1 (le_trans _ $ nnreal.le_coe_of_real _)),
  simpa using hC n
end

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` tends to zero exponentially. -/
lemma geometric_bound_of_lt_radius (p : formal_multilinear_series 𝕜 E F) {r : ℝ≥0}
  (h : (r : ennreal) < p.radius) : ∃ (a < 1) C, ∀ n, nnnorm (p n) * r^n ≤ C * a^n :=
begin
  simp only [radius, lt_supr_iff] at h,
  rcases h with ⟨t, ⟨C, hC⟩, rt⟩,
  rw ennreal.coe_lt_coe at rt,
  refine ⟨r / t, nnreal.div_lt_one_of_lt rt, C, λ n, _⟩,
  have tpos : t ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le _) rt),
  calc nnnorm (p n) * r ^ n = (nnnorm (p n) * t ^ n) * (r / t) ^ n :
    by field_simp [tpos, mul_right_comm]
  ... ≤ C * (r / t) ^ n : mul_le_mul_of_nonneg_right (hC n) (zero_le _)
end

lemma lt_radius_tfae' (p : formal_multilinear_series 𝕜 E F) (r : ℝ≥0) :
  tfae [∃ (a < 1) C, ∀ n, nnnorm (p n) * r ^ n ≤ C * a ^ n,
    ∃ (a ∈ Ioo (0 : ℝ≥0) 1) (C > 0), ∀ n, nnnorm (p n) * r ^ n ≤ C * a ^ n,
    ∃ a < 1, ∀ᶠ n in at_top, nnnorm (p n) * r ^ n ≤ a ^ n,
    ∃ a ∈ Ioo (0 : ℝ≥0) 1, ∀ᶠ n in at_top, nnnorm (p n) * r ^ n ≤ a ^ n,
    ∃ a ∈ Ioo (0 : ℝ≥0) 1, ∀ C > 0, ∀ᶠ n in at_top, nnnorm (p n) * r ^ n ≤ C * a ^ n,
    ∃ (a < 1) C, ∀ n, ∥p n∥ * r ^ n ≤ C * a ^ n,
    ∃ (a ∈ Ioo (0 : ℝ) 1) (C > 0), ∀ n, ∥p n∥ * r ^ n ≤ C * a ^ n,
    ∃ a < 1, ∀ᶠ n in at_top, ∥p n∥ * r ^ n ≤ a ^ n,
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᶠ n in at_top, ∥p n∥ * r ^ n ≤ a ^ n,
    ∃ a ∈ Ioo (0 : ℝ) 1, is_O (λ n, ∥p n∥ * r ^ n) (pow a) at_top,
    ∃ a ∈ Ioo (-1 : ℝ) 1, is_O (λ n, ∥p n∥ * r ^ n) (pow a) at_top,
    ∃ a ∈ Ioo (0 : ℝ) 1, is_o (λ n, ∥p n∥ * r ^ n) (pow a) at_top,
    ∃ a ∈ Ioo (-1 : ℝ) 1, is_o (λ n, ∥p n∥ * r ^ n) (pow a) at_top] :=
begin
  /- 6-13 come from `tfae_exists_lt_is_o_pow (λ n, ∥p n∥ * r ^ n) 1`. -/
  have H := tfae_exists_lt_is_o_pow (λ n, ∥p n∥ * r ^ n) 1,
  have A : ∀ n, abs (∥p n∥ * r ^ n) = ∥p n∥ * r ^ n := λ n, by simp [abs_mul],
  tfae_have : 6 ↔ 7, by simpa only [exists_prop, or_true, true_and, zero_lt_one, A] using H.out 4 5,
  tfae_have : 7 ↔ 8, by simpa only [A] using H.out 5 6,
  tfae_have : 8 ↔ 9, by simpa only [A] using H.out 6 7,
  tfae_have : 9 ↔ 10, by simpa only [A] using H.out 7 3,
  tfae_have : 10 ↔ 11, from H.out 3 2,
  tfae_have : 11 ↔ 12, from H.out 2 1,
  tfae_have : 12 ↔ 13, from H.out 1 0,
  /- Add 1 and 2 -/
  tfae_have : 1 → 6,
  { rintro ⟨a, ha, C, H⟩, exact ⟨a, ha, C, by exact_mod_cast H⟩ },
  tfae_have : 7 → 2,
  { rintro ⟨a, ha, C, hC, H⟩,
    lift C to ℝ≥0 using hC.lt.le, lift a to ℝ≥0 using ha.1.le,
    refine ⟨a, ha, C, hC, λ n, _⟩,
    exact_mod_cast H n },
  tfae_have : 2 → 1, { rintro ⟨a, ha, C, hC, H⟩, exact ⟨a, ha.2, C, H⟩ },
  /- Add 3, 4, and 5 -/
  tfae_have : 3 → 8, { rintro ⟨a, ha, H⟩, refine ⟨a, ha, _⟩, exact_mod_cast H },
  tfae_have : 12 → 5,
  { rintro ⟨a, ha, H⟩,
    lift a to ℝ≥0 using ha.1.le,
    refine ⟨a, ha, λ C hC, (H.def hC).mono $ λ n hn, nnreal.coe_le_coe.1 _⟩,
    rw [real.norm_eq_abs, A, real.norm_eq_abs] at hn,
    simpa using hn },
  tfae_have : 5 → 4, from λ ⟨a, ha, H⟩, ⟨a, ha, by simpa only [one_mul] using H 1 zero_lt_one⟩,
  tfae_have : 4 → 3, { rintro ⟨a, ha, H⟩, exact ⟨a, ha.2, H⟩ },
  tfae_finish
end

lemma lt_radius_tfae (p : formal_multilinear_series 𝕜 E F) {r : ℝ≥0} (hr : r ≠ 0) :
  tfae [↑r < p.radius,
    ∃ (a < 1) C, ∀ n, nnnorm (p n) * r ^ n ≤ C * a ^ n,
    ∃ (a ∈ Ioo (0 : ℝ≥0) 1) (C > 0), ∀ n, nnnorm (p n) * r ^ n ≤ C * a ^ n,
    ∃ a < 1, ∀ᶠ n in at_top, nnnorm (p n) * r ^ n ≤ a ^ n,
    ∃ a ∈ Ioo (0 : ℝ≥0) 1, ∀ᶠ n in at_top, nnnorm (p n) * r ^ n ≤ a ^ n,
    ∃ a ∈ Ioo (0 : ℝ≥0) 1, ∀ C > 0, ∀ᶠ n in at_top, nnnorm (p n) * r ^ n ≤ C * a ^ n,
    ∃ (a < 1) C, ∀ n, ∥p n∥ * r ^ n ≤ C * a ^ n,
    ∃ (a ∈ Ioo (0 : ℝ) 1) (C > 0), ∀ n, ∥p n∥ * r ^ n ≤ C * a ^ n,
    ∃ a < 1, ∀ᶠ n in at_top, ∥p n∥ * r ^ n ≤ a ^ n,
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᶠ n in at_top, ∥p n∥ * r ^ n ≤ a ^ n,
    ∃ a ∈ Ioo (0 : ℝ) 1, is_O (λ n, ∥p n∥ * r ^ n) (pow a) at_top,
    ∃ a ∈ Ioo (-1 : ℝ) 1, is_O (λ n, ∥p n∥ * r ^ n) (pow a) at_top,
    ∃ a ∈ Ioo (0 : ℝ) 1, is_o (λ n, ∥p n∥ * r ^ n) (pow a) at_top,
    ∃ a ∈ Ioo (-1 : ℝ) 1, is_o (λ n, ∥p n∥ * r ^ n) (pow a) at_top] :=
begin
  refine (list.tfae_cons_of_mem _).2 ⟨_, p.lt_radius_tfae' r⟩,
  show _ ∈ _, from or.inl rfl,
  refine ⟨p.geometric_bound_of_lt_radius, λ h, _⟩,
  rcases ((p.lt_radius_tfae' r).out 0 1).1 h with ⟨a, ha, C, hC, H⟩,
  simp only [← nnreal.div_le_iff (pow_ne_zero _ ha.1.ne'), mul_div_assoc, ← div_pow] at H,
  refine lt_of_lt_of_le _ (p.le_radius_of_bound C H),
  rw [ennreal.coe_lt_coe, nnreal.lt_div_iff ha.1.ne'],
  calc r * a < r * 1 : mul_lt_mul_of_pos_left ha.2 (zero_lt_iff_ne_zero.2 hr)
  ... = r : mul_one r
end

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
lemma bound_of_lt_radius (p : formal_multilinear_series 𝕜 E F) {r : ℝ≥0}
  (h : (r : ennreal) < p.radius) : ∃ (C : ℝ≥0), ∀ n, nnnorm (p n) * r^n ≤ C :=
let ⟨a, ha, C, h⟩ := p.geometric_bound_of_lt_radius h
in ⟨C, λ n, (h n).trans $ mul_le_of_le_one_right (zero_le _) (pow_le_one _ (zero_le _) ha.le)⟩

/-- The radius of the sum of two formal series is at least the minimum of their two radii. -/
lemma min_radius_le_radius_add (p q : formal_multilinear_series 𝕜 E F) :
  min p.radius q.radius ≤ (p + q).radius :=
begin
  refine le_of_forall_ge_of_dense (λ r hr, _),
  lift r to ℝ≥0 using (ne_top_of_lt hr),
  obtain ⟨Cp, hCp⟩ : ∃ (C : ℝ≥0), ∀ n, nnnorm (p n) * r^n ≤ C :=
    p.bound_of_lt_radius (lt_of_lt_of_le hr (min_le_left _ _)),
  obtain ⟨Cq, hCq⟩ : ∃ (C : ℝ≥0), ∀ n, nnnorm (q n) * r^n ≤ C :=
    q.bound_of_lt_radius (lt_of_lt_of_le hr (min_le_right _ _)),
  refine (p + q).le_radius_of_bound (Cp + Cq) (λ n, _),
  calc nnnorm (p n + q n) * r ^ n ≤ (nnnorm (p n) + nnnorm (q n)) * r ^ n :
    mul_le_mul_of_nonneg_right (nnnorm_add_le (p n) (q n)) (zero_le (r ^ n))
  ... ≤ Cp + Cq : by { rw add_mul, exact add_le_add (hCp n) (hCq n) }
end

lemma radius_neg (p : formal_multilinear_series 𝕜 E F) : (-p).radius = p.radius :=
by simp [formal_multilinear_series.radius, nnnorm_neg]

/-- Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the sum `Σ pₙ xⁿ`. A
priori, it only behaves well when `∥x∥ < p.radius`. -/
protected def sum (p : formal_multilinear_series 𝕜 E F) (x : E) : F := ∑' n : ℕ , p n (λ i, x)

/-- Given a formal multilinear series `p` and a vector `x`, then `p.partial_sum n x` is the sum
`Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`. -/
def partial_sum (p : formal_multilinear_series 𝕜 E F) (n : ℕ) (x : E) : F :=
∑ k in finset.range n, p k (λ(i : fin k), x)

/-- The partial sums of a formal multilinear series are continuous. -/
lemma partial_sum_continuous (p : formal_multilinear_series 𝕜 E F) (n : ℕ) :
  continuous (p.partial_sum n) :=
by continuity

end formal_multilinear_series


/-! ### Expanding a function as a power series -/
section

variables {f g : E → F} {p pf pg : formal_multilinear_series 𝕜 E F} {x : E} {r r' : ennreal}

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series on the ball of radius `r > 0` around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `∥y∥ < r`. -/
structure has_fpower_series_on_ball
  (f : E → F) (p : formal_multilinear_series 𝕜 E F) (x : E) (r : ennreal) : Prop :=
(r_le    : r ≤ p.radius)
(r_pos   : 0 < r)
(has_sum : ∀ {y}, y ∈ emetric.ball (0 : E) r → has_sum (λn:ℕ, p n (λ(i : fin n), y)) (f (x + y)))

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `y` in a neighborhood of `0`. -/
def has_fpower_series_at (f : E → F) (p : formal_multilinear_series 𝕜 E F) (x : E) :=
∃ r, has_fpower_series_on_ball f p x r

variable (𝕜)
/-- Given a function `f : E → F`, we say that `f` is analytic at `x` if it admits a convergent power
series expansion around `x`. -/
def analytic_at (f : E → F) (x : E) :=
∃ (p : formal_multilinear_series 𝕜 E F), has_fpower_series_at f p x

variable {𝕜}

lemma has_fpower_series_on_ball.has_fpower_series_at (hf : has_fpower_series_on_ball f p x r) :
  has_fpower_series_at f p x := ⟨r, hf⟩

lemma has_fpower_series_at.analytic_at (hf : has_fpower_series_at f p x) : analytic_at 𝕜 f x :=
⟨p, hf⟩

lemma has_fpower_series_on_ball.analytic_at (hf : has_fpower_series_on_ball f p x r) :
  analytic_at 𝕜 f x :=
hf.has_fpower_series_at.analytic_at

lemma has_fpower_series_on_ball.radius_pos (hf : has_fpower_series_on_ball f p x r) :
  0 < p.radius :=
lt_of_lt_of_le hf.r_pos hf.r_le

lemma has_fpower_series_at.radius_pos (hf : has_fpower_series_at f p x) :
  0 < p.radius :=
let ⟨r, hr⟩ := hf in hr.radius_pos

lemma has_fpower_series_on_ball.mono
  (hf : has_fpower_series_on_ball f p x r) (r'_pos : 0 < r') (hr : r' ≤ r) :
  has_fpower_series_on_ball f p x r' :=
⟨le_trans hr hf.1, r'_pos, λ y hy, hf.has_sum (emetric.ball_subset_ball hr hy)⟩

lemma has_fpower_series_on_ball.add
  (hf : has_fpower_series_on_ball f pf x r) (hg : has_fpower_series_on_ball g pg x r) :
  has_fpower_series_on_ball (f + g) (pf + pg) x r :=
{ r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg),
  r_pos := hf.r_pos,
  has_sum := λ y hy, (hf.has_sum hy).add (hg.has_sum hy) }

lemma has_fpower_series_at.add
  (hf : has_fpower_series_at f pf x) (hg : has_fpower_series_at g pg x) :
  has_fpower_series_at (f + g) (pf + pg) x :=
begin
  rcases hf with ⟨rf, hrf⟩,
  rcases hg with ⟨rg, hrg⟩,
  have P : 0 < min rf rg, by simp [hrf.r_pos, hrg.r_pos],
  exact ⟨min rf rg, (hrf.mono P (min_le_left _ _)).add (hrg.mono P (min_le_right _ _))⟩
end

lemma analytic_at.add (hf : analytic_at 𝕜 f x) (hg : analytic_at 𝕜 g x) :
  analytic_at 𝕜 (f + g) x :=
let ⟨pf, hpf⟩ := hf, ⟨qf, hqf⟩ := hg in (hpf.add hqf).analytic_at

lemma has_fpower_series_on_ball.neg (hf : has_fpower_series_on_ball f pf x r) :
  has_fpower_series_on_ball (-f) (-pf) x r :=
{ r_le    := by { rw pf.radius_neg, exact hf.r_le },
  r_pos   := hf.r_pos,
  has_sum := λ y hy, (hf.has_sum hy).neg }

lemma has_fpower_series_at.neg
  (hf : has_fpower_series_at f pf x) : has_fpower_series_at (-f) (-pf) x :=
let ⟨rf, hrf⟩ := hf in hrf.neg.has_fpower_series_at

lemma analytic_at.neg (hf : analytic_at 𝕜 f x) : analytic_at 𝕜 (-f) x :=
let ⟨pf, hpf⟩ := hf in hpf.neg.analytic_at

lemma has_fpower_series_on_ball.sub
  (hf : has_fpower_series_on_ball f pf x r) (hg : has_fpower_series_on_ball g pg x r) :
  has_fpower_series_on_ball (f - g) (pf - pg) x r :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma has_fpower_series_at.sub
  (hf : has_fpower_series_at f pf x) (hg : has_fpower_series_at g pg x) :
  has_fpower_series_at (f - g) (pf - pg) x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma analytic_at.sub (hf : analytic_at 𝕜 f x) (hg : analytic_at 𝕜 g x) :
  analytic_at 𝕜 (f - g) x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma has_fpower_series_on_ball.coeff_zero (hf : has_fpower_series_on_ball f pf x r)
  (v : fin 0 → E) : pf 0 v = f x :=
begin
  have v_eq : v = (λ i, 0), by { ext i, apply fin_zero_elim i },
  have zero_mem : (0 : E) ∈ emetric.ball (0 : E) r, by simp [hf.r_pos],
  have : ∀ i ≠ 0, pf i (λ j, 0) = 0,
  { assume i hi,
    have : 0 < i := bot_lt_iff_ne_bot.mpr hi,
    apply continuous_multilinear_map.map_coord_zero _ (⟨0, this⟩ : fin i),
    refl },
  have A := (hf.has_sum zero_mem).unique (has_sum_single _ this),
  simpa [v_eq] using A.symm,
end

lemma has_fpower_series_at.coeff_zero (hf : has_fpower_series_at f pf x) (v : fin 0 → E) :
  pf 0 v = f x :=
let ⟨rf, hrf⟩ := hf in hrf.coeff_zero v

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence. -/
lemma has_fpower_series_on_ball.uniform_geometric_approx {r' : ℝ≥0}
  (hf : has_fpower_series_on_ball f p x r) (h : (r' : ennreal) < r) :
  ∃ (a C : ℝ≥0), a < 1 ∧ (∀ y ∈ metric.ball (0 : E) r', ∀ n,
  ∥f (x + y) - p.partial_sum n y∥ ≤ C * a ^ n) :=
begin
  obtain ⟨a, ha, C, hC⟩ : ∃ (a < 1) C, ∀ n, nnnorm (p n) * r' ^n ≤ C * a^n :=
    p.geometric_bound_of_lt_radius (h.trans_le hf.r_le),
  refine ⟨a, C / (1 - a), ha, λ y hy n, _⟩,
  have yr' : ∥y∥ < r', by { rw ball_0_eq at hy, exact hy },
  have : y ∈ emetric.ball (0 : E) r,
  { rw [emetric.mem_ball, edist_eq_coe_nnnorm],
    apply lt_trans _ h,
    exact_mod_cast yr' },
  push_cast [ha.le],
  rw [norm_sub_rev, ← mul_div_right_comm],
  apply norm_sub_le_of_geometric_bound_of_has_sum ha _ (hf.has_sum this),
  assume n,
  calc ∥(p n) (λ (i : fin n), y)∥ ≤ ∥p n∥ * (∏ i : fin n, ∥y∥) :
      continuous_multilinear_map.le_op_norm _ _
    ... = nnnorm (p n) * (nnnorm y)^n : by simp
    ... ≤ nnnorm (p n) * r' ^ n :
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (nnreal.coe_nonneg _) (le_of_lt yr') _)
      (nnreal.coe_nonneg _)
    ... ≤ C * a ^ n : by exact_mod_cast hC n,
end

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f (x + y)`
is the uniform limit of `p.partial_sum n y` there. -/
lemma has_fpower_series_on_ball.tendsto_uniformly_on {r' : ℝ≥0}
  (hf : has_fpower_series_on_ball f p x r) (h : (r' : ennreal) < r) :
  tendsto_uniformly_on (λ n y, p.partial_sum n y)
    (λ y, f (x + y)) at_top (metric.ball (0 : E) r') :=
begin
  rcases hf.uniform_geometric_approx h with ⟨a, C, ha, hC⟩,
  refine metric.tendsto_uniformly_on_iff.2 (λ ε εpos, _),
  have L : tendsto (λ n, (C : ℝ) * a^n) at_top (𝓝 ((C : ℝ) * 0)) :=
    tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 a.2 ha),
  rw mul_zero at L,
  refine (L.eventually (gt_mem_nhds εpos)).mono (λ n hn y hy, _),
  rw dist_eq_norm,
  exact (hC y hy n).trans_lt hn
end

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partial_sum n y` there. -/
lemma has_fpower_series_on_ball.tendsto_locally_uniformly_on
  (hf : has_fpower_series_on_ball f p x r) :
  tendsto_locally_uniformly_on (λ n y, p.partial_sum n y) (λ y, f (x + y))
    at_top (emetric.ball (0 : E) r) :=
begin
  assume u hu x hx,
  rcases ennreal.lt_iff_exists_nnreal_btwn.1 hx with ⟨r', xr', hr'⟩,
  have : emetric.ball (0 : E) r' ∈ 𝓝 x :=
    mem_nhds_sets emetric.is_open_ball xr',
  refine ⟨emetric.ball (0 : E) r', mem_nhds_within_of_mem_nhds this, _⟩,
  simpa [metric.emetric_ball_nnreal] using hf.tendsto_uniformly_on hr' u hu
end

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partial_sum n (y - x)` there. -/
lemma has_fpower_series_on_ball.tendsto_uniformly_on' {r' : ℝ≥0}
  (hf : has_fpower_series_on_ball f p x r) (h : (r' : ennreal) < r) :
  tendsto_uniformly_on (λ n y, p.partial_sum n (y - x)) f at_top (metric.ball (x : E) r') :=
begin
  convert (hf.tendsto_uniformly_on h).comp (λ y, y - x),
  { ext z, simp },
  { ext z, simp [dist_eq_norm] }
end

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the  partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partial_sum n (y - x)` there. -/
lemma has_fpower_series_on_ball.tendsto_locally_uniformly_on'
  (hf : has_fpower_series_on_ball f p x r) :
  tendsto_locally_uniformly_on (λ n y, p.partial_sum n (y - x)) f at_top (emetric.ball (x : E) r) :=
begin
  have A : continuous_on (λ (y : E), y - x) (emetric.ball (x : E) r) :=
    (continuous_id.sub continuous_const).continuous_on,
  convert (hf.tendsto_locally_uniformly_on).comp (λ (y : E), y - x) _ A,
  { ext z, simp },
  { assume z, simp [edist_eq_coe_nnnorm, edist_eq_coe_nnnorm_sub] }
end

/-- If a function admits a power series expansion on a disk, then it is continuous there. -/
lemma has_fpower_series_on_ball.continuous_on
  (hf : has_fpower_series_on_ball f p x r) : continuous_on f (emetric.ball x r) :=
hf.tendsto_locally_uniformly_on'.continuous_on $ λ n,
  ((p.partial_sum_continuous n).comp (continuous_id.sub continuous_const)).continuous_on

lemma has_fpower_series_at.continuous_at (hf : has_fpower_series_at f p x) : continuous_at f x :=
let ⟨r, hr⟩ := hf in hr.continuous_on.continuous_at (emetric.ball_mem_nhds x (hr.r_pos))

lemma analytic_at.continuous_at (hf : analytic_at 𝕜 f x) : continuous_at f x :=
let ⟨p, hp⟩ := hf in hp.continuous_at

/-- In a complete space, the sum of a converging power series `p` admits `p` as a power series.
This is not totally obvious as we need to check the convergence of the series. -/
lemma formal_multilinear_series.has_fpower_series_on_ball [complete_space F]
  (p : formal_multilinear_series 𝕜 E F) (h : 0 < p.radius) :
  has_fpower_series_on_ball p.sum p 0 p.radius :=
{ r_le    := le_refl _,
  r_pos   := h,
  has_sum := λ y hy, begin
    rw zero_add,
    replace hy : (nnnorm y : ennreal) < p.radius,
      by { convert hy, exact (edist_eq_coe_nnnorm _).symm },
    obtain ⟨a, ha, C, hC⟩ : ∃ (a < 1) C, ∀ n, nnnorm (p n) * (nnnorm y)^n ≤ C * a^n :=
      p.geometric_bound_of_lt_radius hy,
    refine (summable_of_norm_bounded (λ n, (C : ℝ) * a ^ n)
      ((summable_geometric_of_lt_1 a.2 ha).mul_left _) (λ n, _)).has_sum,
    calc ∥(p n) (λ (i : fin n), y)∥
      ≤ ∥p n∥ * (∏ i : fin n, ∥y∥) : continuous_multilinear_map.le_op_norm _ _
      ... = nnnorm (p n) * (nnnorm y)^n : by simp
      ... ≤ C * a ^ n : by exact_mod_cast hC n
  end }

lemma has_fpower_series_on_ball.sum [complete_space F] (h : has_fpower_series_on_ball f p x r)
  {y : E} (hy : y ∈ emetric.ball (0 : E) r) : f (x + y) = p.sum y :=
begin
  have A := h.has_sum hy,
  have B := (p.has_fpower_series_on_ball h.radius_pos).has_sum (lt_of_lt_of_le hy h.r_le),
  simpa using A.unique B
end

/-- The sum of a converging power series is continuous in its disk of convergence. -/
lemma formal_multilinear_series.continuous_on [complete_space F] :
  continuous_on p.sum (emetric.ball 0 p.radius) :=
begin
  by_cases h : 0 < p.radius,
  { exact (p.has_fpower_series_on_ball h).continuous_on },
  { simp at h,
    simp [h, continuous_on_empty] }
end

end

/-!
### Changing origin in a power series

If a function is analytic in a disk `D(x, R)`, then it is analytic in any disk contained in that
one. Indeed, one can write
$$
f (x + y + z) = \sum_{n} p_n (y + z)^n = \sum_{n, k} \binom{n}{k} p_n y^{n-k} z^k
= \sum_{k} \Bigl(\sum_{n} \binom{n}{k} p_n y^{n-k}\Bigr) z^k.
$$
The corresponding power series has thus a `k`-th coefficient equal to
$\sum_{n} \binom{n}{k} p_n y^{n-k}$. In the general case where `pₙ` is a multilinear map, this has
to be interpreted suitably: instead of having a binomial coefficient, one should sum over all
possible subsets `s` of `fin n` of cardinal `k`, and attribute `z` to the indices in `s` and
`y` to the indices outside of `s`.

In this paragraph, we implement this. The new power series is called `p.change_origin y`. Then, we
check its convergence and the fact that its sum coincides with the original sum. The outcome of this
discussion is that the set of points where a function is analytic is open.
-/

namespace formal_multilinear_series

variables (p : formal_multilinear_series 𝕜 E F) {x y : E} {r : ℝ≥0}

/--
Changing the origin of a formal multilinear series `p`, so that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense.

Here, we don't use the bracket notation `⟨n, s, hs⟩` in place of the argument `i` in the lambda,
as this leads to a bad definition with auxiliary `_match` statements,
but we will try to use pattern matching in lambdas as much as possible in the proofs below
to increase readability.
-/
def change_origin (x : E) : formal_multilinear_series 𝕜 E F :=
λ k, ∑' i : Σ (n : ℕ), {s : finset (fin n) // finset.card s = k}, (p i.1).restr i.2 i.2.2 x

/-- Auxiliary lemma controlling the summability of the sequence appearing in the definition of
`p.change_origin`, first version. -/
-- Note here and below it is necessary to use `@` and provide implicit arguments using `_`,
-- so that it is possible to use pattern matching in the lambda.
-- Overall this seems a good trade-off in readability.
lemma change_origin_summable_aux1 (h : (nnnorm x + r : ennreal) < p.radius) :
  @summable ℝ _ _ _ ((λ ⟨n, s⟩, ∥p n∥ * ∥x∥ ^ (n - s.card) * r ^ s.card) :
    (Σ (n : ℕ), finset (fin n)) → ℝ) :=
begin
  obtain ⟨a, ha, C, hC⟩ : ∃ (a < 1) C, ∀ n, nnnorm (p n) * (nnnorm x + r) ^ n ≤ C * a^n :=
    p.geometric_bound_of_lt_radius h,
  let Bnnnorm : (Σ (n : ℕ), finset (fin n)) → ℝ≥0 :=
    λ ⟨n, s⟩, nnnorm (p n) * (nnnorm x) ^ (n - s.card) * r ^ s.card,
  have : ((λ ⟨n, s⟩, ∥p n∥ * ∥x∥ ^ (n - s.card) * r ^ s.card) :
    (Σ (n : ℕ), finset (fin n)) → ℝ) = (λ b, (Bnnnorm b : ℝ)),
    by { ext ⟨n, s⟩, simp [Bnnnorm, nnreal.coe_pow, coe_nnnorm] },
  rw [this, nnreal.summable_coe, ← ennreal.tsum_coe_ne_top_iff_summable],
  apply ne_of_lt,
  calc (∑' b, ↑(Bnnnorm b))
  = (∑' n, (∑' s, ↑(Bnnnorm ⟨n, s⟩))) : by exact ennreal.tsum_sigma' _
  ... ≤ (∑' n, (((nnnorm (p n) * (nnnorm x + r)^n) : ℝ≥0) : ennreal)) :
    begin
      refine ennreal.tsum_le_tsum (λ n, _),
      rw [tsum_fintype, ← ennreal.coe_finset_sum, ennreal.coe_le_coe],
      apply le_of_eq,
      calc ∑ s : finset (fin n), Bnnnorm ⟨n, s⟩
      = ∑ s : finset (fin n), nnnorm (p n) * ((nnnorm x) ^ (n - s.card) * r ^ s.card) :
        by simp [← mul_assoc]
      ... = nnnorm (p n) * (nnnorm x + r) ^ n :
      by { rw [add_comm, ← finset.mul_sum, ← fin.sum_pow_mul_eq_add_pow], congr' with s : 1, ring }
    end
  ... ≤ (∑' (n : ℕ), (C * a ^ n : ennreal)) :
    tsum_le_tsum (λ n, by exact_mod_cast hC n) ennreal.summable ennreal.summable
  ... < ⊤ :
    by simp [ennreal.mul_eq_top, ha, ennreal.tsum_mul_left, ennreal.tsum_geometric,
              ennreal.lt_top_iff_ne_top]
end

/-- Auxiliary lemma controlling the summability of the sequence appearing in the definition of
`p.change_origin`, second version. -/
lemma change_origin_summable_aux2 (h : (nnnorm x + r : ennreal) < p.radius) :
  @summable ℝ _ _ _ ((λ ⟨k, n, s, hs⟩, ∥(p n).restr s hs x∥ * ↑r ^ k) :
    (Σ (k : ℕ) (n : ℕ), {s : finset (fin n) // finset.card s = k}) → ℝ) :=
begin
  let Bnorm : (Σ (n : ℕ), finset (fin n)) → ℝ := λ ⟨n, s⟩, ∥p n∥ * ∥x∥ ^ (n - s.card) * r ^ s.card,
  have SBnorm : summable Bnorm := p.change_origin_summable_aux1 h,
  let Anorm : (Σ (n : ℕ), finset (fin n)) → ℝ := λ ⟨n, s⟩, ∥(p n).restr s rfl x∥ * r ^ s.card,
  have SAnorm : summable Anorm,
  { refine summable_of_norm_bounded _ SBnorm (λ i, _),
    rcases i with ⟨n, s⟩,
    suffices H : ∥(p n).restr s rfl x∥ * (r : ℝ) ^ s.card ≤
      (∥p n∥ * ∥x∥ ^ (n - finset.card s) * r ^ s.card),
    { have : ∥(r: ℝ)∥ = r, by rw [real.norm_eq_abs, abs_of_nonneg (nnreal.coe_nonneg _)],
      simpa [Anorm, Bnorm, this] using H },
    exact mul_le_mul_of_nonneg_right ((p n).norm_restr s rfl x)
      (pow_nonneg (nnreal.coe_nonneg _) _) },
  let e : (Σ (n : ℕ), finset (fin n)) ≃
      (Σ (k : ℕ) (n : ℕ), {s : finset (fin n) // finset.card s = k}) :=
    { to_fun := λ ⟨n, s⟩, ⟨s.card, n, s, rfl⟩,
      inv_fun := λ ⟨k, n, s, hs⟩, ⟨n, s⟩,
      left_inv := λ ⟨n, s⟩, rfl,
      right_inv := λ ⟨k, n, s, hs⟩, by { induction hs, refl } },
  rw ← e.summable_iff,
  convert SAnorm,
  ext ⟨n, s⟩,
  refl
end

/-- An auxiliary definition for `change_origin_radius`. -/
def change_origin_summable_aux_j (k : ℕ) :
  (Σ (n : ℕ), {s : finset (fin n) // finset.card s = k})
    → (Σ (k : ℕ) (n : ℕ), {s : finset (fin n) // finset.card s = k}) :=
λ ⟨n, s, hs⟩, ⟨k, n, s, hs⟩

lemma change_origin_summable_aux_j_injective (k : ℕ) :
  function.injective (change_origin_summable_aux_j k) :=
begin
  rintros ⟨_, ⟨_, _⟩⟩ ⟨_, ⟨_, _⟩⟩ a,
  simp only [change_origin_summable_aux_j, true_and, eq_self_iff_true, heq_iff_eq, sigma.mk.inj_iff] at a,
  rcases a with ⟨rfl, a⟩,
  simpa using a,
end

/-- Auxiliary lemma controlling the summability of the sequence appearing in the definition of
`p.change_origin`, third version. -/
lemma change_origin_summable_aux3 (k : ℕ) (h : (nnnorm x : ennreal) < p.radius) :
  @summable ℝ _ _ _ (λ ⟨n, s, hs⟩, ∥(p n).restr s hs x∥ :
  (Σ (n : ℕ), {s : finset (fin n) // finset.card s = k}) → ℝ) :=
begin
  obtain ⟨r, rpos, hr⟩ : ∃ (r : ℝ≥0), 0 < r ∧ ((nnnorm x + r) : ennreal) < p.radius :=
    ennreal.lt_iff_exists_add_pos_lt.mp h,
  have S : @summable ℝ _ _ _ ((λ ⟨n, s, hs⟩, ∥(p n).restr s hs x∥ * (r : ℝ) ^ k) :
    (Σ (n : ℕ), {s : finset (fin n) // finset.card s = k}) → ℝ),
  { convert (p.change_origin_summable_aux2 hr).comp_injective
      (change_origin_summable_aux_j_injective k),
    -- again, cleanup that could be done by `tidy`:
    ext ⟨_, ⟨_, _⟩⟩, refl },
  have : (r : ℝ)^k ≠ 0, by simp [pow_ne_zero, nnreal.coe_eq_zero, ne_of_gt rpos],
  apply (summable_mul_right_iff this).2,
  convert S,
  -- again, cleanup that could be done by `tidy`:
  ext ⟨_, ⟨_, _⟩⟩, refl,
end

-- FIXME this causes a deterministic timeout with `-T50000`
/-- The radius of convergence of `p.change_origin x` is at least `p.radius - ∥x∥`. In other words,
`p.change_origin x` is well defined on the largest ball contained in the original ball of
convergence.-/
lemma change_origin_radius : p.radius - nnnorm x ≤ (p.change_origin x).radius :=
begin
  by_cases h : p.radius ≤ nnnorm x,
  { have : radius p - ↑(nnnorm x) = 0 := ennreal.sub_eq_zero_of_le h,
    rw this,
    exact zero_le _ },
  replace h : (nnnorm x : ennreal) < p.radius, by simpa using h,
  refine le_of_forall_ge_of_dense (λ r hr, _),
  cases r, { simpa using hr },
  rw [ennreal.lt_sub_iff_add_lt, add_comm] at hr,
  let A : (Σ (k : ℕ) (n : ℕ), {s : finset (fin n) // finset.card s = k}) → ℝ :=
    λ ⟨k, n, s, hs⟩, ∥(p n).restr s hs x∥ * (r : ℝ) ^ k,
  have SA : summable A := p.change_origin_summable_aux2 hr,
  have A_nonneg : ∀ i, 0 ≤ A i,
  { rintros ⟨k, n, s, hs⟩,
    change 0 ≤ ∥(p n).restr s hs x∥ * (r : ℝ) ^ k,
    refine mul_nonneg (norm_nonneg _) (pow_nonneg (nnreal.coe_nonneg _) _) },
  have tsum_nonneg : 0 ≤ tsum A := tsum_nonneg A_nonneg,
  apply le_radius_of_bound _ (nnreal.of_real (tsum A)) (λ k, _),
  rw [← nnreal.coe_le_coe, nnreal.coe_mul, nnreal.coe_pow, coe_nnnorm,
      nnreal.coe_of_real _ tsum_nonneg],
  calc ∥change_origin p x k∥ * ↑r ^ k
  = ∥@tsum (E [×k]→L[𝕜] F) _ _ _ (λ i, (p i.1).restr i.2.1 i.2.2 x :
    (Σ (n : ℕ), {s : finset (fin n) // finset.card s = k}) → (E [×k]→L[𝕜] F))∥ * ↑r ^ k : rfl
  ... ≤ tsum (λ i, ∥(p i.1).restr i.2.1 i.2.2 x∥ :
    (Σ (n : ℕ), {s : finset (fin n) // finset.card s = k}) → ℝ) * ↑r ^ k :
      begin
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (nnreal.coe_nonneg _) _),
        apply norm_tsum_le_tsum_norm,
        convert p.change_origin_summable_aux3 k h,
        ext a,
        tidy
      end
  ... = tsum (λ i, ∥(p i.1).restr i.2.1 i.2.2 x∥ * ↑r ^ k :
    (Σ (n : ℕ), {s : finset (fin n) // finset.card s = k}) → ℝ) :
      by { rw tsum_mul_right, convert p.change_origin_summable_aux3 k h, tidy }
  ... = tsum (A ∘ change_origin_summable_aux_j k) : by { congr, tidy }
  ... ≤ tsum A : tsum_comp_le_tsum_of_inj SA A_nonneg (change_origin_summable_aux_j_injective k)
end

-- From this point on, assume that the space is complete, to make sure that series that converge
-- in norm also converge in `F`.
variable [complete_space F]

/-- The `k`-th coefficient of `p.change_origin` is the sum of a summable series. -/
lemma change_origin_has_sum (k : ℕ) (h : (nnnorm x : ennreal) < p.radius) :
  @has_sum (E [×k]→L[𝕜] F) _ _ _  ((λ i, (p i.1).restr i.2.1 i.2.2 x) :
    (Σ (n : ℕ), {s : finset (fin n) // finset.card s = k}) → (E [×k]→L[𝕜] F))
  (p.change_origin x k) :=
begin
  apply summable.has_sum,
  apply summable_of_summable_norm,
  convert p.change_origin_summable_aux3 k h,
  tidy
end

/-- Summing the series `p.change_origin x` at a point `y` gives back `p (x + y)`-/
theorem change_origin_eval (h : (nnnorm x + nnnorm y : ennreal) < p.radius) :
  has_sum ((λk:ℕ, p.change_origin x k (λ (i : fin k), y))) (p.sum (x + y)) :=
begin
  /- The series on the left is a series of series. If we order the terms differently, we get back
  to `p.sum (x + y)`, in which the `n`-th term is expanded by multilinearity. In the proof below,
  the term on the left is the sum of a series of terms `A`, the sum on the right is the sum of a
  series of terms `B`, and we show that they correspond to each other by reordering to conclude the
  proof. -/
  have radius_pos : 0 < p.radius := lt_of_le_of_lt (zero_le _) h,
  -- `A` is the terms of the series whose sum gives the series for `p.change_origin`
  let A : (Σ (k : ℕ) (n : ℕ), {s : finset (fin n) // s.card = k}) → F :=
    λ ⟨k, n, s, hs⟩, (p n).restr s hs x (λ(i : fin k), y),
  -- `B` is the terms of the series whose sum gives `p (x + y)`, after expansion by multilinearity.
  let B : (Σ (n : ℕ), finset (fin n)) → F := λ ⟨n, s⟩, (p n).restr s rfl x (λ (i : fin s.card), y),
  let Bnorm : (Σ (n : ℕ), finset (fin n)) → ℝ := λ ⟨n, s⟩, ∥p n∥ * ∥x∥ ^ (n - s.card) * ∥y∥ ^ s.card,
  have SBnorm : summable Bnorm, by convert p.change_origin_summable_aux1 h,
  have SB : summable B,
  { refine summable_of_norm_bounded _ SBnorm _,
    rintros ⟨n, s⟩,
    calc ∥(p n).restr s rfl x (λ (i : fin s.card), y)∥
      ≤ ∥(p n).restr s rfl x∥ * ∥y∥ ^ s.card :
        begin
          convert ((p n).restr s rfl x).le_op_norm (λ (i : fin s.card), y),
          simp [(finset.prod_const (∥y∥))],
        end
      ... ≤ (∥p n∥ * ∥x∥ ^ (n - s.card)) * ∥y∥ ^ s.card :
        mul_le_mul_of_nonneg_right ((p n).norm_restr _ _ _) (pow_nonneg (norm_nonneg _) _) },
  -- Check that indeed the sum of `B` is `p (x + y)`.
  have has_sum_B : has_sum B (p.sum (x + y)),
  { have K1 : ∀ n, has_sum (λ (s : finset (fin n)), B ⟨n, s⟩) (p n (λ (i : fin n), x + y)),
    { assume n,
      have : (p n) (λ (i : fin n), y + x) = ∑ s : finset (fin n),
        p n (finset.piecewise s (λ (i : fin n), y) (λ (i : fin n), x)) :=
        (p n).map_add_univ (λ i, y) (λ i, x),
      simp [add_comm y x] at this,
      rw this,
      exact has_sum_fintype _ },
    have K2 : has_sum (λ (n : ℕ), (p n) (λ (i : fin n), x + y)) (p.sum (x + y)),
    { have : x + y ∈ emetric.ball (0 : E) p.radius,
      { apply lt_of_le_of_lt _ h,
        rw [edist_eq_coe_nnnorm, ← ennreal.coe_add, ennreal.coe_le_coe],
        exact norm_add_le x y },
      simpa using (p.has_fpower_series_on_ball radius_pos).has_sum this },
    exact has_sum.sigma_of_has_sum K2 K1 SB },
  -- Deduce that the sum of `A` is also `p (x + y)`, as the terms `A` and `B` are the same up to
  -- reordering
  have has_sum_A : has_sum A (p.sum (x + y)),
  { let e : (Σ (n : ℕ), finset (fin n)) ≃
      (Σ (k : ℕ) (n : ℕ), {s : finset (fin n) // finset.card s = k}) :=
    { to_fun := λ ⟨n, s⟩, ⟨s.card, n, s, rfl⟩,
      inv_fun := λ ⟨k, n, s, hs⟩, ⟨n, s⟩,
      left_inv := λ ⟨n, s⟩, rfl,
      right_inv := λ ⟨k, n, s, hs⟩, by { induction hs, refl } },
    have : A ∘ e = B, by { ext ⟨⟩, refl },
    rw ← e.has_sum_iff,
    convert has_sum_B },
  -- Summing `A ⟨k, c⟩` with fixed `k` and varying `c` is exactly the `k`-th term in the series
  -- defining `p.change_origin`, by definition
  have J : ∀k, has_sum (λ c, A ⟨k, c⟩) (p.change_origin x k (λ(i : fin k), y)),
  { assume k,
    have : (nnnorm x : ennreal) < radius p := lt_of_le_of_lt (le_add_right (le_refl _)) h,
    convert continuous_multilinear_map.has_sum_eval (p.change_origin_has_sum k this)
      (λ(i : fin k), y),
    ext i,
    tidy },
  exact has_sum_A.sigma J
end

end formal_multilinear_series

section

variables [complete_space F] {f : E → F} {p : formal_multilinear_series 𝕜 E F} {x y : E}
{r : ennreal}

/-- If a function admits a power series expansion `p` on a ball `B (x, r)`, then it also admits a
power series on any subball of this ball (even with a different center), given by `p.change_origin`.
-/
theorem has_fpower_series_on_ball.change_origin
  (hf : has_fpower_series_on_ball f p x r) (h : (nnnorm y : ennreal) < r) :
  has_fpower_series_on_ball f (p.change_origin y) (x + y) (r - nnnorm y) :=
{ r_le := begin
    apply le_trans _ p.change_origin_radius,
    exact ennreal.sub_le_sub hf.r_le (le_refl _)
  end,
  r_pos := by simp [h],
  has_sum := begin
    assume z hz,
    have A : (nnnorm y : ennreal) + nnnorm z < r,
    { have : edist z 0 < r - ↑(nnnorm y) := hz,
      rwa [edist_eq_coe_nnnorm, ennreal.lt_sub_iff_add_lt, add_comm] at this },
    convert p.change_origin_eval (lt_of_lt_of_le A hf.r_le),
    have : y + z ∈ emetric.ball (0 : E) r := calc
      edist (y + z) 0 ≤ ↑(nnnorm y) + ↑(nnnorm z) :
        by { rw [edist_eq_coe_nnnorm, ← ennreal.coe_add, ennreal.coe_le_coe], exact norm_add_le y z }
      ... < r : A,
    simpa only [add_assoc] using hf.sum this
  end }

lemma has_fpower_series_on_ball.analytic_at_of_mem
  (hf : has_fpower_series_on_ball f p x r) (h : y ∈ emetric.ball x r) :
  analytic_at 𝕜 f y :=
begin
  have : (nnnorm (y - x) : ennreal) < r, by simpa [edist_eq_coe_nnnorm_sub] using h,
  have := hf.change_origin this,
  rw [add_sub_cancel'_right] at this,
  exact this.analytic_at
end

variables (𝕜 f)
lemma is_open_analytic_at : is_open {x | analytic_at 𝕜 f x} :=
begin
  rw is_open_iff_forall_mem_open,
  assume x hx,
  rcases hx with ⟨p, r, hr⟩,
  refine ⟨emetric.ball x r, λ y hy, hr.analytic_at_of_mem hy, emetric.is_open_ball, _⟩,
  simp only [edist_self, emetric.mem_ball, hr.r_pos]
end
variables {𝕜 f}

end
