/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
import analysis.special_functions.pow.asymptotics

/-!
# Continuity of power functions

This file contains lemmas about continuity of the power functions on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`.
-/

noncomputable theory

open_locale classical real topology nnreal ennreal filter big_operators complex_conjugate
open filter finset set

section cpow_limits

/-!
## Continuity for complex powers
-/

open complex

variables {α : Type*}

lemma zero_cpow_eq_nhds {b : ℂ} (hb : b ≠ 0) :
  (λ (x : ℂ), (0 : ℂ) ^ x) =ᶠ[𝓝 b] 0 :=
begin
  suffices : ∀ᶠ (x : ℂ) in (𝓝 b), x ≠ 0,
  from this.mono (λ x hx, by { dsimp only, rw [zero_cpow hx, pi.zero_apply]} ),
  exact is_open.eventually_mem is_open_ne hb,
end

lemma cpow_eq_nhds {a b : ℂ} (ha : a ≠ 0) :
  (λ x, x ^ b) =ᶠ[𝓝 a] λ x, exp (log x * b) :=
begin
  suffices : ∀ᶠ (x : ℂ) in (𝓝 a), x ≠ 0,
    from this.mono (λ x hx, by { dsimp only, rw [cpow_def_of_ne_zero hx], }),
  exact is_open.eventually_mem is_open_ne ha,
end

lemma cpow_eq_nhds' {p : ℂ × ℂ} (hp_fst : p.fst ≠ 0) :
  (λ x, x.1 ^ x.2) =ᶠ[𝓝 p] λ x, exp (log x.1 * x.2) :=
begin
  suffices : ∀ᶠ (x : ℂ × ℂ) in (𝓝 p), x.1 ≠ 0,
    from this.mono (λ x hx, by { dsimp only, rw cpow_def_of_ne_zero hx, }),
  refine is_open.eventually_mem _ hp_fst,
  change is_open {x : ℂ × ℂ | x.1 = 0}ᶜ,
  rw is_open_compl_iff,
  exact is_closed_eq continuous_fst continuous_const,
end

/- Continuity of `λ x, a ^ x`: union of these two lemmas is optimal. -/

lemma continuous_at_const_cpow {a b : ℂ} (ha : a ≠ 0) : continuous_at (λ x, a ^ x) b :=
begin
  have cpow_eq : (λ x:ℂ, a ^ x) = λ x, exp (log a * x),
    by { ext1 b, rw [cpow_def_of_ne_zero ha], },
  rw cpow_eq,
  exact continuous_exp.continuous_at.comp (continuous_at.mul continuous_at_const continuous_at_id),
end

lemma continuous_at_const_cpow' {a b : ℂ} (h : b ≠ 0) : continuous_at (λ x, a ^ x) b :=
begin
  by_cases ha : a = 0,
  { rw [ha, continuous_at_congr (zero_cpow_eq_nhds h)], exact continuous_at_const, },
  { exact continuous_at_const_cpow ha, },
end

/-- The function `z ^ w` is continuous in `(z, w)` provided that `z` does not belong to the interval
`(-∞, 0]` on the real line. See also `complex.continuous_at_cpow_zero_of_re_pos` for a version that
works for `z = 0` but assumes `0 < re w`. -/
lemma continuous_at_cpow {p : ℂ × ℂ} (hp_fst : 0 < p.fst.re ∨ p.fst.im ≠ 0) :
  continuous_at (λ x : ℂ × ℂ, x.1 ^ x.2) p :=
begin
  have hp_fst_ne_zero : p.fst ≠ 0,
    by { intro h, cases hp_fst; { rw h at hp_fst, simpa using hp_fst, }, },
  rw continuous_at_congr (cpow_eq_nhds' hp_fst_ne_zero),
  refine continuous_exp.continuous_at.comp _,
  refine continuous_at.mul (continuous_at.comp _ continuous_fst.continuous_at)
    continuous_snd.continuous_at,
  exact continuous_at_clog hp_fst,
end

lemma continuous_at_cpow_const {a b : ℂ} (ha : 0 < a.re ∨ a.im ≠ 0) :
  continuous_at (λ x, cpow x b) a :=
tendsto.comp (@continuous_at_cpow (a, b) ha) (continuous_at_id.prod continuous_at_const)

lemma filter.tendsto.cpow {l : filter α} {f g : α → ℂ} {a b : ℂ} (hf : tendsto f l (𝓝 a))
  (hg : tendsto g l (𝓝 b)) (ha : 0 < a.re ∨ a.im ≠ 0) :
  tendsto (λ x, f x ^ g x) l (𝓝 (a ^ b)) :=
(@continuous_at_cpow (a,b) ha).tendsto.comp (hf.prod_mk_nhds hg)

lemma filter.tendsto.const_cpow {l : filter α} {f : α → ℂ} {a b : ℂ} (hf : tendsto f l (𝓝 b))
  (h : a ≠ 0 ∨ b ≠ 0) :
  tendsto (λ x, a ^ f x) l (𝓝 (a ^ b)) :=
begin
  cases h,
  { exact (continuous_at_const_cpow h).tendsto.comp hf, },
  { exact (continuous_at_const_cpow' h).tendsto.comp hf, },
end

variables [topological_space α] {f g : α → ℂ} {s : set α} {a : α}

lemma continuous_within_at.cpow (hf : continuous_within_at f s a) (hg : continuous_within_at g s a)
  (h0 : 0 < (f a).re ∨ (f a).im ≠ 0) :
  continuous_within_at (λ x, f x ^ g x) s a :=
hf.cpow hg h0

lemma continuous_within_at.const_cpow {b : ℂ} (hf : continuous_within_at f s a)
  (h : b ≠ 0 ∨ f a ≠ 0) :
  continuous_within_at (λ x, b ^ f x) s a :=
hf.const_cpow h

lemma continuous_at.cpow (hf : continuous_at f a) (hg : continuous_at g a)
  (h0 : 0 < (f a).re ∨ (f a).im ≠ 0) :
  continuous_at (λ x, f x ^ g x) a :=
hf.cpow hg h0

lemma continuous_at.const_cpow {b : ℂ} (hf : continuous_at f a) (h : b ≠ 0 ∨ f a ≠ 0) :
  continuous_at (λ x, b ^ f x) a :=
hf.const_cpow h

lemma continuous_on.cpow (hf : continuous_on f s) (hg : continuous_on g s)
  (h0 : ∀ a ∈ s, 0 < (f a).re ∨ (f a).im ≠ 0) :
  continuous_on (λ x, f x ^ g x) s :=
λ a ha, (hf a ha).cpow (hg a ha) (h0 a ha)

lemma continuous_on.const_cpow {b : ℂ} (hf : continuous_on f s) (h : b ≠ 0 ∨ ∀ a ∈ s, f a ≠ 0) :
  continuous_on (λ x, b ^ f x) s :=
λ a ha, (hf a ha).const_cpow (h.imp id $ λ h, h a ha)

lemma continuous.cpow (hf : continuous f) (hg : continuous g)
  (h0 : ∀ a, 0 < (f a).re ∨ (f a).im ≠ 0) :
  continuous (λ x, f x ^ g x) :=
continuous_iff_continuous_at.2 $ λ a, (hf.continuous_at.cpow hg.continuous_at (h0 a))

lemma continuous.const_cpow {b : ℂ} (hf : continuous f) (h : b ≠ 0 ∨ ∀ a, f a ≠ 0) :
  continuous (λ x, b ^ f x) :=
continuous_iff_continuous_at.2 $ λ a, (hf.continuous_at.const_cpow $ h.imp id $ λ h, h a)

lemma continuous_on.cpow_const {b : ℂ} (hf : continuous_on f s)
  (h : ∀ (a : α), a ∈ s → 0 < (f a).re ∨ (f a).im ≠ 0) :
  continuous_on (λ x, (f x) ^ b) s :=
hf.cpow continuous_on_const h

end cpow_limits

section rpow_limits

/-!
## Continuity for real powers
-/

namespace real

lemma continuous_at_const_rpow {a b : ℝ} (h : a ≠ 0) : continuous_at (rpow a) b :=
begin
  have : rpow a = λ x : ℝ, ((a : ℂ) ^ (x : ℂ)).re, by { ext1 x, rw [rpow_eq_pow, rpow_def], },
  rw this,
  refine complex.continuous_re.continuous_at.comp _,
  refine (continuous_at_const_cpow _).comp complex.continuous_of_real.continuous_at,
  norm_cast,
  exact h,
end

lemma continuous_at_const_rpow' {a b : ℝ} (h : b ≠ 0) : continuous_at (rpow a) b :=
begin
  have : rpow a = λ x : ℝ, ((a : ℂ) ^ (x : ℂ)).re, by { ext1 x, rw [rpow_eq_pow, rpow_def], },
  rw this,
  refine complex.continuous_re.continuous_at.comp _,
  refine (continuous_at_const_cpow' _).comp complex.continuous_of_real.continuous_at,
  norm_cast,
  exact h,
end

lemma rpow_eq_nhds_of_neg {p : ℝ × ℝ} (hp_fst : p.fst < 0) :
  (λ x : ℝ × ℝ, x.1 ^ x.2) =ᶠ[𝓝 p] λ x, exp (log x.1 * x.2) * cos (x.2 * π) :=
begin
  suffices : ∀ᶠ (x : ℝ × ℝ) in (𝓝 p), x.1 < 0,
    from this.mono (λ x hx, by { dsimp only, rw rpow_def_of_neg hx, }),
  exact is_open.eventually_mem (is_open_lt continuous_fst continuous_const) hp_fst,
end

lemma rpow_eq_nhds_of_pos {p : ℝ × ℝ} (hp_fst : 0 < p.fst) :
  (λ x : ℝ × ℝ, x.1 ^ x.2) =ᶠ[𝓝 p] λ x, exp (log x.1 * x.2) :=
begin
  suffices : ∀ᶠ (x : ℝ × ℝ) in (𝓝 p), 0 < x.1,
    from this.mono (λ x hx, by { dsimp only, rw rpow_def_of_pos hx, }),
  exact is_open.eventually_mem (is_open_lt continuous_const continuous_fst) hp_fst,
end

lemma continuous_at_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
  continuous_at (λ p : ℝ × ℝ, p.1 ^ p.2) p :=
begin
  rw ne_iff_lt_or_gt at hp,
  cases hp,
  { rw continuous_at_congr (rpow_eq_nhds_of_neg hp),
    refine continuous_at.mul _ (continuous_cos.continuous_at.comp _),
    { refine continuous_exp.continuous_at.comp (continuous_at.mul _ continuous_snd.continuous_at),
      refine (continuous_at_log _).comp continuous_fst.continuous_at,
      exact hp.ne, },
    { exact continuous_snd.continuous_at.mul continuous_at_const, }, },
  { rw continuous_at_congr (rpow_eq_nhds_of_pos hp),
    refine continuous_exp.continuous_at.comp (continuous_at.mul _ continuous_snd.continuous_at),
    refine (continuous_at_log _).comp continuous_fst.continuous_at,
    exact hp.lt.ne.symm, },
end

lemma continuous_at_rpow_of_pos (p : ℝ × ℝ) (hp : 0 < p.2) :
  continuous_at (λ p : ℝ × ℝ, p.1 ^ p.2) p :=
begin
  cases p with x y,
  obtain hx|rfl := ne_or_eq x 0,
  { exact continuous_at_rpow_of_ne (x, y) hx },
  have A : tendsto (λ p : ℝ × ℝ, exp (log p.1 * p.2)) (𝓝[≠] 0 ×ᶠ 𝓝 y) (𝓝 0) :=
    tendsto_exp_at_bot.comp
      ((tendsto_log_nhds_within_zero.comp tendsto_fst).at_bot_mul hp tendsto_snd),
  have B : tendsto (λ p : ℝ × ℝ, p.1 ^ p.2) (𝓝[≠] 0 ×ᶠ 𝓝 y) (𝓝 0) :=
    squeeze_zero_norm (λ p, abs_rpow_le_exp_log_mul p.1 p.2) A,
  have C : tendsto (λ p : ℝ × ℝ, p.1 ^ p.2) (𝓝[{0}] 0 ×ᶠ 𝓝 y) (pure 0),
  { rw [nhds_within_singleton, tendsto_pure, pure_prod, eventually_map],
    exact (lt_mem_nhds hp).mono (λ y hy, zero_rpow hy.ne') },
  simpa only [← sup_prod, ← nhds_within_union, compl_union_self, nhds_within_univ, nhds_prod_eq,
    continuous_at, zero_rpow hp.ne'] using B.sup (C.mono_right (pure_le_nhds _))
end

lemma continuous_at_rpow (p : ℝ × ℝ) (h : p.1 ≠ 0 ∨ 0 < p.2) :
  continuous_at (λ p : ℝ × ℝ, p.1 ^ p.2) p :=
h.elim (λ h, continuous_at_rpow_of_ne p h) (λ h, continuous_at_rpow_of_pos p h)

lemma continuous_at_rpow_const (x : ℝ) (q : ℝ) (h : x ≠ 0 ∨ 0 < q) :
  continuous_at (λ (x : ℝ), x ^ q) x :=
begin
  change continuous_at ((λ p : ℝ × ℝ, p.1 ^ p.2) ∘ (λ y : ℝ, (y, q))) x,
  apply continuous_at.comp,
  { exact continuous_at_rpow (x, q) h },
  { exact (continuous_id'.prod_mk continuous_const).continuous_at }
end

end real

section

variable {α : Type*}

lemma filter.tendsto.rpow {l : filter α} {f g : α → ℝ} {x y : ℝ}
  (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) :
  tendsto (λ t, f t ^ g t) l (𝓝 (x ^ y)) :=
(real.continuous_at_rpow (x, y) h).tendsto.comp (hf.prod_mk_nhds hg)

lemma filter.tendsto.rpow_const {l : filter α} {f : α → ℝ} {x p : ℝ}
  (hf : tendsto f l (𝓝 x)) (h : x ≠ 0 ∨ 0 ≤ p) :
  tendsto (λ a, f a ^ p) l (𝓝 (x ^ p)) :=
if h0 : 0 = p then h0 ▸ by simp [tendsto_const_nhds]
else hf.rpow tendsto_const_nhds (h.imp id $ λ h', h'.lt_of_ne h0)

variables [topological_space α] {f g : α → ℝ} {s : set α} {x : α} {p : ℝ}

lemma continuous_at.rpow (hf : continuous_at f x) (hg : continuous_at g x) (h : f x ≠ 0 ∨ 0 < g x) :
  continuous_at (λ t, f t ^ g t) x :=
hf.rpow hg h

lemma continuous_within_at.rpow (hf : continuous_within_at f s x) (hg : continuous_within_at g s x)
  (h : f x ≠ 0 ∨ 0 < g x) :
  continuous_within_at (λ t, f t ^ g t) s x :=
hf.rpow hg h

lemma continuous_on.rpow (hf : continuous_on f s) (hg : continuous_on g s)
  (h : ∀ x ∈ s, f x ≠ 0 ∨ 0 < g x) :
  continuous_on (λ t, f t ^ g t) s :=
λ t ht, (hf t ht).rpow (hg t ht) (h t ht)

lemma continuous.rpow (hf : continuous f) (hg : continuous g) (h : ∀ x, f x ≠ 0 ∨ 0 < g x) :
  continuous (λ x, f x ^ g x) :=
continuous_iff_continuous_at.2 $ λ x, (hf.continuous_at.rpow hg.continuous_at (h x))

lemma continuous_within_at.rpow_const (hf : continuous_within_at f s x) (h : f x ≠ 0 ∨ 0 ≤ p) :
  continuous_within_at (λ x, f x ^ p) s x :=
hf.rpow_const h

lemma continuous_at.rpow_const (hf : continuous_at f x) (h : f x ≠ 0 ∨ 0 ≤ p) :
  continuous_at (λ x, f x ^ p) x :=
hf.rpow_const h

lemma continuous_on.rpow_const (hf : continuous_on f s) (h : ∀ x ∈ s, f x ≠ 0 ∨ 0 ≤ p) :
  continuous_on (λ x, f x ^ p) s :=
λ x hx, (hf x hx).rpow_const (h x hx)

lemma continuous.rpow_const (hf : continuous f) (h : ∀ x, f x ≠ 0 ∨ 0 ≤ p) :
  continuous (λ x, f x ^ p) :=
continuous_iff_continuous_at.2 $ λ x, hf.continuous_at.rpow_const (h x)

end

end rpow_limits

/-! ## Continuity results for `cpow`, part II

These results involve relating real and complex powers, so cannot be done higher up.
-/
section cpow_limits2

namespace complex

/-- See also `continuous_at_cpow` and `complex.continuous_at_cpow_of_re_pos`. -/
lemma continuous_at_cpow_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) :
  continuous_at (λ x : ℂ × ℂ, x.1 ^ x.2) (0, z) :=
begin
  have hz₀ : z ≠ 0, from ne_of_apply_ne re hz.ne',
  rw [continuous_at, zero_cpow hz₀, tendsto_zero_iff_norm_tendsto_zero],
  refine squeeze_zero (λ _, norm_nonneg _) (λ _, abs_cpow_le _ _) _,
  simp only [div_eq_mul_inv, ← real.exp_neg],
  refine tendsto.zero_mul_is_bounded_under_le _ _,
  { convert (continuous_fst.norm.tendsto _).rpow ((continuous_re.comp continuous_snd).tendsto _) _;
      simp [hz, real.zero_rpow hz.ne'] },
  { simp only [(∘), real.norm_eq_abs, abs_of_pos (real.exp_pos _)],
    rcases exists_gt (|im z|) with ⟨C, hC⟩,
    refine ⟨real.exp (π * C), eventually_map.2 _⟩,
    refine (((continuous_im.comp continuous_snd).abs.tendsto (_, z)).eventually
      (gt_mem_nhds hC)).mono (λ z hz, real.exp_le_exp.2 $ (neg_le_abs_self _).trans _),
    rw _root_.abs_mul,
    exact mul_le_mul (abs_le.2 ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩) hz.le
      (_root_.abs_nonneg _) real.pi_pos.le }
end

/-- See also `continuous_at_cpow` for a version that assumes `p.1 ≠ 0` but makes no
assumptions about `p.2`. -/
lemma continuous_at_cpow_of_re_pos {p : ℂ × ℂ} (h₁ : 0 ≤ p.1.re ∨ p.1.im ≠ 0) (h₂ : 0 < p.2.re) :
  continuous_at (λ x : ℂ × ℂ, x.1 ^ x.2) p :=
begin
  cases p with z w,
  rw [← not_lt_zero_iff, lt_iff_le_and_ne, not_and_distrib, ne.def, not_not, not_le_zero_iff] at h₁,
  rcases h₁ with h₁|(rfl : z = 0),
  exacts [continuous_at_cpow h₁, continuous_at_cpow_zero_of_re_pos h₂]
end

/-- See also `continuous_at_cpow_const` for a version that assumes `z ≠ 0` but makes no
assumptions about `w`. -/
lemma continuous_at_cpow_const_of_re_pos {z w : ℂ} (hz : 0 ≤ re z ∨ im z ≠ 0) (hw : 0 < re w) :
  continuous_at (λ x, x ^ w) z :=
tendsto.comp (@continuous_at_cpow_of_re_pos (z, w) hz hw)
  (continuous_at_id.prod continuous_at_const)

/-- Continuity of `(x, y) ↦ x ^ y` as a function on `ℝ × ℂ`. -/
lemma continuous_at_of_real_cpow (x : ℝ) (y : ℂ) (h : 0 < y.re ∨ x ≠ 0) :
  continuous_at (λ p, ↑p.1 ^ p.2 : ℝ × ℂ → ℂ) (x, y) :=
begin
  rcases lt_trichotomy 0 x with hx | rfl | hx,
  { -- x > 0 : easy case
    have : continuous_at (λ p, ⟨↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) (x, y),
      from continuous_of_real.continuous_at.prod_map continuous_at_id,
    refine (continuous_at_cpow (or.inl _)).comp this,
    rwa of_real_re },
  { -- x = 0 : reduce to continuous_at_cpow_zero_of_re_pos
    have A : continuous_at (λ p, p.1 ^ p.2 : ℂ × ℂ → ℂ) ⟨↑(0:ℝ), y⟩,
    { rw of_real_zero,
      apply continuous_at_cpow_zero_of_re_pos,
      tauto },
    have B : continuous_at (λ p, ⟨↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) ⟨0, y⟩,
      from continuous_of_real.continuous_at.prod_map continuous_at_id,
    exact @continuous_at.comp (ℝ × ℂ) (ℂ × ℂ) ℂ _ _ _ _ (λ p, ⟨↑p.1, p.2⟩) ⟨0, y⟩ A B },
  { -- x < 0 : difficult case
    suffices : continuous_at (λ p, (-↑p.1) ^ p.2 * exp (π * I * p.2) : ℝ × ℂ → ℂ) (x, y),
    { refine this.congr (eventually_of_mem (prod_mem_nhds (Iio_mem_nhds hx) univ_mem) _),
      exact λ p hp, (of_real_cpow_of_nonpos (le_of_lt hp.1) p.2).symm },
    have A : continuous_at (λ p, ⟨-↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) (x, y),
      from continuous_at.prod_map (continuous_of_real.continuous_at.neg) continuous_at_id,
    apply continuous_at.mul,
    { refine (continuous_at_cpow (or.inl _)).comp A,
      rwa [neg_re, of_real_re, neg_pos] },
    { exact (continuous_exp.comp (continuous_const.mul continuous_snd)).continuous_at } },
end

lemma continuous_at_of_real_cpow_const (x : ℝ) (y : ℂ) (h : 0 < y.re ∨ x ≠ 0) :
  continuous_at (λ a, a ^ y : ℝ → ℂ) x :=
@continuous_at.comp _ _ _ _ _ _ _ _ x (continuous_at_of_real_cpow x y h)
  (continuous_id.prod_mk continuous_const).continuous_at

lemma continuous_of_real_cpow_const {y : ℂ} (hs : 0 < y.re) : continuous (λ x, x ^ y : ℝ → ℂ) :=
continuous_iff_continuous_at.mpr (λ x, continuous_at_of_real_cpow_const x y (or.inl hs))

end complex

end cpow_limits2

/-! ## Limits and continuity for `ℝ≥0` powers -/
namespace nnreal

lemma continuous_at_rpow {x : ℝ≥0} {y : ℝ} (h : x ≠ 0 ∨ 0 < y) :
  continuous_at (λp:ℝ≥0×ℝ, p.1^p.2) (x, y) :=
begin
  have : (λp:ℝ≥0×ℝ, p.1^p.2) = real.to_nnreal ∘ (λp:ℝ×ℝ, p.1^p.2) ∘ (λp:ℝ≥0 × ℝ, (p.1.1, p.2)),
  { ext p,
    rw [coe_rpow, real.coe_to_nnreal _ (real.rpow_nonneg_of_nonneg p.1.2 _)],
    refl },
  rw this,
  refine continuous_real_to_nnreal.continuous_at.comp (continuous_at.comp _ _),
  { apply real.continuous_at_rpow,
    simp only [ne.def] at h,
    rw ← (nnreal.coe_eq_zero x) at h,
    exact h },
  { exact ((continuous_subtype_val.comp continuous_fst).prod_mk continuous_snd).continuous_at }
end

lemma eventually_pow_one_div_le (x : ℝ≥0) {y : ℝ≥0} (hy : 1 < y) :
  ∀ᶠ (n : ℕ) in at_top, x ^ (1 / n : ℝ) ≤ y :=
begin
  obtain ⟨m, hm⟩ := add_one_pow_unbounded_of_pos x (tsub_pos_of_lt hy),
  rw [tsub_add_cancel_of_le hy.le] at hm,
  refine eventually_at_top.2 ⟨m + 1, λ n hn, _⟩,
  simpa only [nnreal.rpow_one_div_le_iff (nat.cast_pos.2 $ m.succ_pos.trans_le hn),
    nnreal.rpow_nat_cast] using hm.le.trans (pow_le_pow hy.le (m.le_succ.trans hn)),
end

end nnreal

open filter

lemma filter.tendsto.nnrpow {α : Type*} {f : filter α} {u : α → ℝ≥0} {v : α → ℝ} {x : ℝ≥0} {y : ℝ}
  (hx : tendsto u f (𝓝 x)) (hy : tendsto v f (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) :
  tendsto (λ a, (u a) ^ (v a)) f (𝓝 (x ^ y)) :=
tendsto.comp (nnreal.continuous_at_rpow h) (hx.prod_mk_nhds hy)

namespace nnreal

lemma continuous_at_rpow_const {x : ℝ≥0} {y : ℝ} (h : x ≠ 0 ∨ 0 ≤ y) :
  continuous_at (λ z, z^y) x :=
h.elim (λ h, tendsto_id.nnrpow tendsto_const_nhds (or.inl h)) $
  λ h, h.eq_or_lt.elim
    (λ h, h ▸ by simp only [rpow_zero, continuous_at_const])
    (λ h, tendsto_id.nnrpow tendsto_const_nhds (or.inr h))

lemma continuous_rpow_const {y : ℝ} (h : 0 ≤ y) :
  continuous (λ x : ℝ≥0, x^y) :=
continuous_iff_continuous_at.2 $ λ x, continuous_at_rpow_const (or.inr h)

end nnreal

/-! ## Continuity for `ℝ≥0∞` powers -/
namespace ennreal

lemma eventually_pow_one_div_le {x : ℝ≥0∞} (hx : x ≠ ∞) {y : ℝ≥0∞} (hy : 1 < y) :
  ∀ᶠ (n : ℕ) in at_top, x ^ (1 / n : ℝ) ≤ y :=
begin
  lift x to ℝ≥0 using hx,
  by_cases y = ∞,
  { exact eventually_of_forall (λ n, h.symm ▸ le_top) },
  { lift y to ℝ≥0 using h,
    have := nnreal.eventually_pow_one_div_le x (by exact_mod_cast hy : 1 < y),
    refine this.congr (eventually_of_forall $ λ n, _),
    rw [coe_rpow_of_nonneg x (by positivity : 0 ≤ (1 / n : ℝ)), coe_le_coe] },
end

private lemma continuous_at_rpow_const_of_pos {x : ℝ≥0∞} {y : ℝ} (h : 0 < y) :
  continuous_at (λ a : ℝ≥0∞, a ^ y) x :=
begin
  by_cases hx : x = ⊤,
  { rw [hx, continuous_at],
    convert tendsto_rpow_at_top h,
    simp [h] },
  lift x to ℝ≥0 using hx,
  rw continuous_at_coe_iff,
  convert continuous_coe.continuous_at.comp
    (nnreal.continuous_at_rpow_const (or.inr h.le)) using 1,
  ext1 x,
  simp [coe_rpow_of_nonneg _ h.le]
end

@[continuity]
lemma continuous_rpow_const {y : ℝ} : continuous (λ a : ℝ≥0∞, a ^ y) :=
begin
  apply continuous_iff_continuous_at.2 (λ x, _),
  rcases lt_trichotomy 0 y with hy|rfl|hy,
  { exact continuous_at_rpow_const_of_pos hy },
  { simp only [rpow_zero], exact continuous_at_const },
  { obtain ⟨z, hz⟩ : ∃ z, y = -z := ⟨-y, (neg_neg _).symm⟩,
    have z_pos : 0 < z, by simpa [hz] using hy,
    simp_rw [hz, rpow_neg],
    exact continuous_inv.continuous_at.comp (continuous_at_rpow_const_of_pos z_pos) }
end

lemma tendsto_const_mul_rpow_nhds_zero_of_pos {c : ℝ≥0∞} (hc : c ≠ ∞) {y : ℝ} (hy : 0 < y) :
  tendsto (λ x : ℝ≥0∞, c * x ^ y) (𝓝 0) (𝓝 0) :=
begin
  convert ennreal.tendsto.const_mul (ennreal.continuous_rpow_const.tendsto 0) _,
  { simp [hy] },
  { exact or.inr hc }
end

end ennreal

lemma filter.tendsto.ennrpow_const {α : Type*} {f : filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} (r : ℝ)
  (hm : tendsto m f (𝓝 a)) :
  tendsto (λ x, (m x) ^ r) f (𝓝 (a ^ r)) :=
(ennreal.continuous_rpow_const.tendsto a).comp hm
