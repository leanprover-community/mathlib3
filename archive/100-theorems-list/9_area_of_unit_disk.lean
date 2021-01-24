/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Benjamin Davidson, Andrew Souther
-/

import topology.metric_space.basic
import measure_theory.interval_integral
import measure_theory.prod
import analysis.special_functions.trigonometric
import analysis.mean_inequalities

/-!
Freek № 9: The area of the unit disc is `π`.
-/
open set interval_integral metric real filter measure_theory

-- **Measure Theory stuff**

open_locale classical

variable {α : Type*}
variables [measurable_space α] {μ : measure α} [sigma_finite μ] {f g : α → ℝ} {s : set α}

/-- Docstring needed! -/
def region_between (f g : α → ℝ) (s : set α) : set (α × ℝ) :=
{ p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Ioo (f p.1) (g p.1) }

/-- The region between two measurable functions on a measurable set is measurable. -/
lemma is_measurable_region_between (hf : measurable f) (hg: measurable g) (hs : is_measurable s) :
  is_measurable (region_between f g s) :=
begin
  dsimp only [region_between, Ioo, mem_set_of_eq, set_of_and],
  refine is_measurable.inter _ ((is_measurable_lt (hf.comp measurable_fst) measurable_snd).inter
    (is_measurable_lt measurable_snd (hg.comp measurable_fst))),
  convert hs.prod is_measurable.univ,
  simp only [and_true, mem_univ],
end

/-- The volume of the region between two measurable functions on a measurable set can be
    respresented as a left integral. -/
theorem volume_region_between_eq_lintegral
  (hf : measurable f) (hg : measurable g) (hs : is_measurable s) :
  μ.prod volume (region_between f g s) = ∫⁻ y in s, ennreal.of_real ((g - f) y) ∂μ :=
begin
  rw measure.prod_apply,
  { have h : (λ x, volume {a | x ∈ s ∧ a ∈ Ioo (f x) (g x)})
            = s.indicator (λ x, ennreal.of_real (g x - f x)),
    { funext x,
      rw indicator_apply,
      split_ifs,
      { have hx : {a | x ∈ s ∧ a ∈ Ioo (f x) (g x)} = Ioo (f x) (g x) := by simp [h, Ioo],
        simp only [hx, volume_Ioo, sub_zero] },
      { have hx : {a | x ∈ s ∧ a ∈ Ioo (f x) (g x)} = ∅ := by simp [h],
        simp only [hx, measure_empty] } },
    dsimp only [region_between, preimage_set_of_eq],
    rw [h, lintegral_indicator];
    simp only [hs, pi.sub_apply] },
  { exact is_measurable_region_between hf hg hs },
end

/-- If two functions are integrable (and measurable) on a measurable set, and one function is less
    than or equal to the other everywhere on that set, then the volume of the region between the
    two functions can be respresented as an integral. -/
theorem volume_region_between_eq_integral
  (f_int : integrable_on f s μ) (g_int : integrable_on g s μ)
  (f_meas : measurable f) (g_meas : measurable g) (hs : is_measurable s)
  (hfg : ∀ x ∈ s, f x ≤ g x) :
  μ.prod volume (region_between f g s) = ennreal.of_real (∫ y in s, (g - f) y ∂μ) :=
begin
  let u : α → nnreal := λ x, if h : x ∈ s then ⟨g x - f x, by linarith [hfg _ h]⟩ else 0,
  have h : g - f =ᵐ[μ.restrict s] (λ x, ((u x):ℝ))
        ∧ (λ y, ennreal.of_real ((g - f) y)) =ᵐ[μ.restrict s] (λ x, ((u x):ennreal)),
  { split;
    rw eventually_eq_iff_exists_mem;
    use s;
    simp only [measure.ae, mem_set_of_eq, filter.mem_mk, measure.restrict_apply hs.compl,
              measure_empty, compl_inter_self, eq_self_iff_true, true_and];
    intros x hx;
    simp only [u, pi.sub_apply];
    split_ifs,
    { rw subtype.coe_mk },
    { rw ennreal.of_real_eq_coe_nnreal } },
  rw [volume_region_between_eq_lintegral, integral_congr_ae h.1, lintegral_congr_ae h.2,
      lintegral_coe_eq_integral],
  exacts [(integrable_congr h.1).mp (g_int.sub f_int), f_meas, g_meas, hs],
end

-- **FTC-2 stuff**

open_locale topological_space

variables {E : Type*} [measurable_space E] [normed_group E] [normed_space ℝ E]
  [borel_space E] [complete_space E] [topological_space.second_countable_topology E]

-- Corollary of FTC-2 for the open set.
theorem integral_eq_sub_of_has_deriv_at'_of_le {f f' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
  (hcont : continuous_on f (interval a b))
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hcont' : continuous_on f' (interval a b)) :
  ∫ y in a..b, f' y = f b - f a :=
integral_eq_sub_of_has_deriv_at' hcont (by rwa [min_eq_left hab, max_eq_right hab]) hcont'


-- **Ben's assorted auxiliary assumptions (all affirmed)**

lemma sqrt_ne_zero {x : ℝ} (hlt : 0 < x) : sqrt x ≠ 0 :=
(sqrt_pos.mpr hlt).ne.symm

lemma div_sqrt {x : ℝ} : x / sqrt x = sqrt x :=
begin
  cases le_or_lt x 0,
  { rw [sqrt_eq_zero'.mpr h, div_zero] },
  { rw [div_eq_iff (sqrt_ne_zero h), mul_self_sqrt h.le] },
end

lemma add_sqr {a b : ℝ} : (a + b)^2 = a^2 + b^2 + 2 * a * b := by ring

lemma sqr_add_le_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a^2 + b^2 ≤ (a+b)^2 :=
by simp only [add_sqr, add_mul, add_le_add_iff_right, ← pow_two, le_add_iff_nonneg_right,
  mul_nonneg (mul_nonneg zero_le_two ha) hb]

lemma sqr_add_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) : a^2 + b^2 ≤ (a+b)^2 :=
by simp only [add_sqr, add_mul, add_le_add_iff_right, ← pow_two, le_add_iff_nonneg_right,
  mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos zero_le_two ha) hb]

lemma sqr_abs {a : ℝ} : (abs a) ^ 2 = a ^ 2 :=
by rw [← sqrt_sqr_eq_abs, sqr_sqrt (pow_two_nonneg a)]

lemma lt_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x < sqrt y ↔ x ^ 2 < y :=
by rw [mul_self_lt_mul_self_iff hx (sqrt_nonneg y), pow_two, mul_self_sqrt hy]

theorem sqr_lt {a b : ℝ} : a^2 < b ↔ -sqrt b < a ∧ a < sqrt b :=
begin
  split,
  { simpa only [← sqrt_lt (pow_two_nonneg a), sqrt_sqr_eq_abs] using abs_lt.mp },
  { rw [← abs_lt, ← sqr_abs],
    exact λ h, (lt_sqrt (abs_nonneg a) (sqrt_pos.mp (lt_of_le_of_lt (abs_nonneg a) h)).le).mp h },
end

lemma sqr_lt_left {a b : ℝ} (h : a^2 < b) : -sqrt b < a := (sqr_lt.mp h).1

lemma sqr_lt_right {a b : ℝ} (h : a^2 < b) : a < sqrt b := (sqr_lt.mp h).2

lemma sqr_lt_sqr {x y : ℝ} (h : abs x < y) : x ^ 2 < y ^ 2 :=
by simpa only [sqr_abs] using pow_lt_pow_of_lt_left h (abs_nonneg x) zero_lt_two

lemma sqr_lt_sqr' {x y : ℝ} (h1 : -y < x) (h2 : x < y) : x ^ 2 < y ^ 2 :=
sqr_lt_sqr (abs_lt.mpr ⟨h1, h2⟩)


-- **Freek № 9**

def disc {r : ℝ} (h : 0 < r) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}

/-- The area of a disc with radius `r`, which can be represented as the region between the two
    curves `λ x, - sqrt (r ^ 2 - x ^ 2)` and `λ x, sqrt (r ^ 2 - x ^ 2)`, is `π * r ^ 2`. -/
theorem volume_disc {r : ℝ} (hr : 0 < r) :
  volume.prod volume (disc hr) = ennreal.of_real (pi * r ^ 2) :=
begin
  have : disc hr = region_between (λ x, -sqrt (r^2 - x^2)) (λ x, sqrt (r^2 - x^2)) (Ioc (-r) r),
  { ext p,
    simp only [disc, region_between, mem_set_of_eq, mem_Ioo, mem_Ioc, pi.neg_apply],
    split;
    intro h,
    { split,
      { rw ← sqrt_sqr hr.le,
        have h' : p.1^2 < r^2 := by linarith [pow_two_nonneg p.2],
        exact ⟨sqr_lt_left h', (sqr_lt_right h').le⟩ },
      { rw [add_comm, ← lt_sub_iff_add_lt] at h,
        exact sqr_lt.mp h} },
    { rw [add_comm, ← lt_sub_iff_add_lt],
      exact sqr_lt.mpr h.2 } },
  have H : ∀ {f : ℝ → ℝ}, continuous f → integrable_on f (Ioc (-r) r) :=
    λ f hc, (hc.integrable_on_compact compact_Icc).mono_set Ioc_subset_Icc_self,
  obtain ⟨hc1, hc2⟩ := ⟨(continuous_const.sub (continuous_pow 2)).sqrt, continuous_const.mul hc1⟩,
  convert volume_region_between_eq_integral (H hc1.neg) (H hc1) (hc1.neg).measurable hc1.measurable
    is_measurable_Ioc (λ x hx, le_trans (neg_nonpos.mpr (sqrt_nonneg _)) (sqrt_nonneg _)),
  simp only [pi.sub_apply, sub_neg_eq_add, ← two_mul],
  rw [← integral_of_le, integral_eq_sub_of_has_deriv_at'_of_le (neg_le_self hr.le)
      (((continuous_const.mul (continuous_arcsin.comp (continuous_id.div continuous_const
        (λ x, hr.ne.symm)))).add (continuous_id.mul hc1)).continuous_on) _ hc2.continuous_on],
  { simp only [id.def, add_zero, sqrt_zero, arcsin_neg, pi.div_apply, function.comp_app,
              neg_square, mul_zero, sub_self, neg_div, div_self hr.ne.symm, arcsin_one],
    rw [mul_neg_eq_neg_mul_symm, sub_neg_eq_add, ← mul_div_assoc, add_halves', mul_comm] },
  { rintros x ⟨hx1, hx2⟩,
    convert ((has_deriv_at_const x (r^2)).mul ((has_deriv_at_arcsin _ _).comp x
      ((has_deriv_at_id' x).div (has_deriv_at_const x r) hr.ne.symm))).add
        ((has_deriv_at_id' x).mul (((has_deriv_at_id' x).pow.const_sub (r^2)).sqrt _)),
    { have h : sqrt (1 - x ^ 2 / r ^ 2) * r ^ 2 = r * sqrt (r ^ 2 - x ^ 2),
      { rw [← sqrt_sqr (pow_nonneg hr.le 2), ← sqrt_mul, sub_mul, sqrt_sqr (pow_nonneg hr.le 2),
            div_mul_eq_mul_div_comm, pow_two, mul_div_cancel_left _ (pow_ne_zero 2 hr.ne.symm),
            ← mul_assoc, ← sub_mul, mul_comm, sqrt_mul (pow_nonneg hr.le 2), sqrt_sqr hr.le,
            one_mul],
        simpa only [sub_nonneg, sqrt_sqr (pow_nonneg hr.le 2), div_le_one (pow_pos hr 2)] using
          (sqr_lt_sqr' hx1 hx2).le },
      field_simp,
      rw [h, mul_div_assoc, ← div_div_eq_div_mul, div_self hr.ne.symm, mul_one_div, mul_left_comm,
          ← pow_two, neg_div, mul_div_mul_left (x^2) (sqrt (r^2-x^2)) two_ne_zero, ← add_assoc,
          add_right_comm, tactic.ring.add_neg_eq_sub, div_sub_div_same, div_sqrt, two_mul] },
    { by_contra hnot,
      rw [not_not, eq_neg_iff_eq_neg, ← div_neg, eq_comm,
          div_eq_one_iff_eq (neg_ne_zero.mpr hr.ne.symm)] at hnot,
      exact hx1.ne.symm hnot },
    { by_contra hnot,
      rw [not_not, div_eq_one_iff_eq hr.ne.symm] at hnot,
      exact hx2.ne hnot },
    { simpa only [sub_ne_zero] using (sqr_lt_sqr' hx1 hx2).ne.symm } },
  { exact neg_le_self hr.le },
end

/-- The area of the unit disc is `π`. -/
theorem volume_unit_disc : volume.prod volume (disc zero_lt_one) = ennreal.of_real pi :=
by simpa only [one_pow, mul_one] using volume_disc zero_lt_one

--Definition of the unit disc.
def unit_disc := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}

/-- The area of the unit disc, which can be represented as the region between the two curves
    `λ x, -sqrt (1 - x ^ 2)` and `λ x, sqrt (1 - x ^ 2)`, is `π`. -/
theorem volume_unit_disc' : volume.prod volume unit_disc = ennreal.of_real pi :=
begin
  have : unit_disc = region_between (λ x, -sqrt (1 - x^2)) (λ x, sqrt (1 - x^2)) (Ioc (-(1:ℝ)) 1),
  { ext p,
    simp only [unit_disc, region_between, mem_set_of_eq, mem_Ioo, mem_Ioc, pi.neg_apply],
    split;
    intro h,
    { split,
      { rw ← sqrt_one,
        have h' : p.1^2 < 1 := by linarith [pow_two_nonneg p.2],
        exact ⟨sqr_lt_left h', (sqr_lt_right h').le⟩ },
      { rw [add_comm, ← lt_sub_iff_add_lt] at h,
        exact sqr_lt.mp h} },
    { rw [add_comm, ← lt_sub_iff_add_lt],
      exact sqr_lt.mpr h.2 } },
  have h : ∀ {f : ℝ → ℝ}, continuous f → integrable_on f (Ioc (-(1:ℝ)) 1) :=
    λ f hc, (hc.integrable_on_compact compact_Icc).mono_set Ioc_subset_Icc_self,
  obtain ⟨hc1, hc2⟩ := ⟨(continuous_const.sub (continuous_pow 2)).sqrt, continuous_const.mul hc1⟩,
  convert volume_region_between_eq_integral (h hc1.neg) (h hc1) (hc1.neg).measurable hc1.measurable
    is_measurable_Ioc (λ x hx, le_trans (neg_nonpos.mpr (sqrt_nonneg _)) (sqrt_nonneg _)),
  simp only [sub_neg_eq_add, pi.sub_apply, ← two_mul],
  rw [← integral_of_le, integral_eq_sub_of_has_deriv_at'_of_le (neg_le_self zero_le_one)
      ((continuous_arcsin.add (continuous_id.mul hc1)).continuous_on) _ hc2.continuous_on],
  { simp only [arcsin_one, arcsin_neg_one, one_pow, add_zero, nat.neg_one_pow_two, sub_self,
              sqrt_zero, mul_zero, sub_neg_eq_add, add_halves'] },
  { rintros x ⟨hx1, hx2⟩,
    convert (has_deriv_at_arcsin hx1.ne.symm hx2.ne).add ((has_deriv_at_id' x).mul
      (((has_deriv_at_id' x).pow.const_sub 1).sqrt _)),
    { simp only [one_mul, mul_one, zero_sub, nat.cast_bit0, pow_one, nat.cast_one, neg_div],
      rw mul_div_mul_left;
      field_simp [add_left_comm, ← pow_two, tactic.ring.add_neg_eq_sub, div_sqrt, ← two_mul] },
    { nlinarith } },
  { exact neg_le_self zero_le_one },
end


-- **`region_under` stuff**

def region_under (g : α → ℝ) (s : set α) : set (α × ℝ) :=
{ p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Ico 0 (g p.1) }

/-- The volume "under" a function is measurable. -/
lemma is_measurable_region_under (hg : measurable g) (hs : is_measurable s) :
  is_measurable (region_under g s) :=
begin
  dsimp only [region_under, Ico, mem_set_of_eq, set_of_and],
  refine is_measurable.inter _ ((is_measurable_le measurable_const measurable_snd).inter
    (is_measurable_lt measurable_snd (hv.comp measurable_fst))),
  convert hs.prod is_measurable.univ,
  simp only [and_true, mem_univ],
end

/-- The volume "under" a function can be respresented as a left integral -/
theorem volume_region_under_eq_lintegral (hg : measurable g) (hs : is_measurable s) :
  (μ.prod volume) (region_under g s) = ∫⁻ y in s, ennreal.of_real (g y) ∂μ :=
begin
  rw measure.prod_apply,
  { have h : (λ x, volume {a | x ∈ s ∧ a ∈ Ico 0 (g x)}) = s.indicator (λ x, ennreal.of_real (g x)),
    { funext x,
      rw indicator_apply,
      split_ifs,
      { have hx : {a | x ∈ s ∧ a ∈ Ico 0 (g x)} = Ico 0 (g x) := by simp [h, Ico],
        simp only [hx, volume_Ico, sub_zero] },
      { have hx : {a | x ∈ s ∧ a ∈ Ico 0 (g x)} = ∅ := by simp [h],
        simp only [hx, measure_empty] } },
    dsimp only [region_under, preimage_set_of_eq],
    rwa [h, lintegral_indicator] },
  { exact is_measurable_region_under hg hs },
end


/- **Old Stuff**

-- Attempt I - via `is_measurable_unit_disc`:

lemma indicator_eq_self_of_subset {S s : set ℝ} {f: ℝ → ℝ} (h: s ⊆ S) (H: s.indicator f = f) :
  S.indicator f = f :=
begin
  rw indicator_eq_self at H ⊢,
  exact subset.trans H h,
end

-- Monotocity of the `L^p` norm for 2 summands.
lemma sqr_add_le_add_abs_sqr (a b : ℝ) : a^2 + b^2 ≤ (abs a + abs b)^2 :=
by simpa only [sqr_abs] using sqr_add_le_of_nonneg (abs_nonneg a) (abs_nonneg b)

-- Turns term of type `ℝ × ℝ` into term of type `fin 2 → ℝ`. Used in Minkowski's inequality below.
def fin_from_prod (p : ℝ × ℝ) : fin 2 → ℝ :=
λ a : fin 2, if a = 0 then p.1 else p.2

-- Minkowski's inequality for two summands and real power `p`.
lemma real.Lp_add_two_le (f g : ℝ × ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (abs (f.1 + g.1) ^ p + abs (f.2 + g.2) ^ p) ^ (1 / p)
  ≤ (abs f.1 ^ p + abs f.2 ^ p) ^ (1 / p) + (abs g.1 ^ p + abs g.2 ^ p) ^ (1 / p) :=
by simpa [fin.sum_univ_succ (λ (i : fin 2), abs (fin_from_prod f i + fin_from_prod g i) ^ p),
          fin.sum_univ_succ (λ (i : fin 2), abs (fin_from_prod f i) ^ p),
          fin.sum_univ_succ (λ (i : fin 2), abs (fin_from_prod g i) ^ p),
          univ_unique, finset.sum_singleton]
    using real.Lp_add_le (finset.univ : finset (fin 2)) (fin_from_prod f) (fin_from_prod g) hp

-- Minkowski's inequality for two summands and natural power `p`.
lemma real.Lp_add_two_le' (f g : ℝ × ℝ) {p : ℕ} (hp : 1 ≤ p) :
    (abs (f.1 + g.1) ^ p + abs (f.2 + g.2) ^ p) ^ (1 / (p:ℝ))
  ≤ (abs f.1 ^ p + abs f.2 ^ p) ^ (1 / (p:ℝ)) + (abs g.1 ^ p + abs g.2 ^ p) ^ (1 / (p:ℝ)) :=
by convert real.Lp_add_two_le f g (by exact_mod_cast hp : 1 ≤ (p:ℝ)) using 3; simp

/-- The unit disc is open. -/
lemma is_open_unit_disc : is_open unit_disc :=
begin
  rw is_open_iff,
  intros p hp,
  use (1/2) * (1 - sqrt ((p.1) ^ 2 + (p.2) ^ 2)),
  split,
  { norm_num,
    rw ← sqrt_one,
    exact (sqrt_lt (add_nonneg (pow_two_nonneg p.1) (pow_two_nonneg p.2))).2 hp },
  { intros q hq,
    let h := real.Lp_add_two_le' (q.1 - p.1, q.2 - p.2) p one_le_two,
    simp only [unit_disc, dist, mem_ball, mem_set_of_eq, max_lt_iff, sqrt_one, sub_add_cancel,
              ← sqrt_lt (add_nonneg (pow_two_nonneg q.1) (pow_two_nonneg q.2))] at hp hq h ⊢,
    calc  sqrt (q.1 ^ 2 + q.2 ^ 2)
        ≤ sqrt ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) + sqrt (p.1 ^ 2 + p.2 ^ 2) :
          by rw [sqrt_eq_rpow,
                ← abs_of_nonneg (pow_two_nonneg q.1), ← abs_of_nonneg (pow_two_nonneg q.2),
                ← abs_of_nonneg (pow_two_nonneg (q.1 - p.1)),
                ← abs_of_nonneg (pow_two_nonneg (q.2 - p.2)),
                ← abs_of_nonneg (pow_two_nonneg p.1), ← abs_of_nonneg (pow_two_nonneg p.2),
                abs_pow q.1 2, abs_pow q.2 2, abs_pow p.1 2, abs_pow p.2 2,
                abs_pow (q.1 - p.1) 2, abs_pow (q.2 - p.2) 2];
            exact_mod_cast h
    ... ≤ abs (q.1 - p.1) + abs (q.2 - p.2) + sqrt (p.1 ^ 2 + p.2 ^ 2) :
          add_le_add_right (by rw sqrt_le_iff; exact ⟨add_nonneg (abs_nonneg _) (abs_nonneg _),
            sqr_add_le_add_abs_sqr (q.1 - p.1) (q.2 - p.2)⟩) (sqrt (p.1 ^ 2 + p.2 ^ 2))
    ... < 1 : by linarith [add_lt_add hq.1 hq.2] },
end

/-- Once we know that the unit disc is open, we know that it is measurable. -/
lemma is_measurable_unit_disc : is_measurable unit_disc :=
is_open_unit_disc.is_measurable

theorem area_of_unit_disc : volume.prod volume unit_disc = ennreal.of_real pi :=
begin
  have h1 : unit_disc = {p : ℝ × ℝ | -sqrt (1 - p.1^2) < p.2 ∧ p.2 < sqrt (1 - p.1^2)},
  { ext p,
    dsimp only [unit_disc, mem_set_of_eq],
    rw [add_comm, ← lt_sub_iff_add_lt],
    exact sqr_lt },
  have h2 : (Ioc (-1) 1).indicator (λ y, 2 * sqrt (1 - y^2)) = λ y, 2 * sqrt (1 - y^2),
  { ext a,
    rw [indicator_apply_eq_self, mul_eq_zero],
    intros ha,
    right,
    apply sqrt_eq_zero_of_nonpos,
    rw [sub_nonpos, ← sqrt_le (pow_two_nonneg a), sqrt_one, sqrt_sqr_eq_abs, le_abs],
    simp only [mem_Ioc, not_and_distrib, not_lt, not_le, ← mul_zero] at ha,
    cases ha,
    { exact or.inr (le_neg.mp ha) },
    { exact or.inl ha.le } },
  obtain ⟨hc1, hc2⟩ := ⟨(continuous_const.sub (continuous_pow 2)).sqrt, continuous_const.mul hc1⟩,
  rw measure.prod_apply is_measurable_unit_disc,
  { simp only [h1, preimage_set_of_eq, Ioo_def, volume_Ioo, neg_mul_eq_neg_mul_symm, one_mul,
              sub_neg_eq_add, ← two_mul],
    convert lintegral_coe_eq_integral (λ x, nnreal.of_real ((λ y, 2 * sqrt (1 - y^2)) x)) _;
    simp only [nnreal.coe_of_real _ (mul_nonneg zero_le_two (sqrt_nonneg _))],
    { rw [← h2, integral_indicator, ← integral_of_le,
          integral_eq_sub_of_has_deriv_at'_of_le (neg_le_self zero_le_one)
            ((continuous_arcsin.add (continuous_id.mul hc1)).continuous_on) _ hc2.continuous_on],
      { simp only [arcsin_one, arcsin_neg_one, one_pow, add_zero, nat.neg_one_pow_two, sub_self,
                  sqrt_zero, mul_zero, sub_neg_eq_add, add_halves'] },
      { rintros x ⟨hx1, hx2⟩,
        convert (has_deriv_at_arcsin hx1.ne.symm hx2.ne).add ((has_deriv_at_id' x).mul
                  (((has_deriv_at_id' x).pow.const_sub 1).sqrt _)),
        { simp only [one_mul, mul_one, zero_sub, nat.cast_bit0, pow_one, nat.cast_one, neg_div],
          rw mul_div_mul_left;
          field_simp [add_left_comm, ← pow_two, tactic.ring.add_neg_eq_sub, div_sqrt, ← two_mul] },
        { nlinarith } },
      exacts [neg_le_self zero_le_one, is_measurable_Ioc] },
    { rw ← indicator_eq_self_of_subset Ioc_subset_Icc_self h2,
      exact (hc2.integrable_on_compact compact_Icc).indicator is_measurable_Icc } },
  { apply_instance },
end


-- Attempt II - via `region_under` and `region_between`, `lintegral` version:

/-- The area of the unit disc, which can be represented as the region between the two curves
    `λ x, -sqrt (1 - x^2)` and `λ x, sqrt (1 - x^2)`, is `π`. -/
theorem volume_unit_disc'' : volume.prod volume unit_disc = ennreal.of_real pi :=
begin
  have : unit_disc = region_between (λ x, -sqrt (1 - x^2)) (λ x, sqrt (1 - x^2)) (Ioc (-(1:ℝ)) 1),
  { ext p,
    simp only [unit_disc, region_between, mem_set_of_eq, mem_Ioo, mem_Ioc, pi.neg_apply],
    split;
    intro h,
    { split,
      { rw ← sqrt_one,
        have h' : p.1^2 < 1 := by linarith [pow_two_nonneg p.2],
        exact ⟨sqr_lt_left h', (sqr_lt_right h').le⟩ },
      { rw [add_comm, ← lt_sub_iff_add_lt] at h,
        exact sqr_lt.mp h} },
    { rw [add_comm, ← lt_sub_iff_add_lt],
      exact sqr_lt.mpr h.2 } },
  obtain ⟨hc1, hc2⟩ := ⟨(continuous_const.sub (continuous_pow 2)).sqrt, continuous_const.mul hc1⟩,
  convert volume_region_between_eq_lintegral (hc1.measurable).neg (hc1.measurable)
            is_measurable_Ioc,
  simp only [pi.sub_apply, sub_neg_eq_add, ← two_mul],
  symmetry,
  convert lintegral_coe_eq_integral (λ x, (λ y, nnreal.of_real (2 * sqrt (1 - y^2))) x) _,
  { simp only [nnreal.coe_of_real _ (mul_nonneg zero_le_two (sqrt_nonneg _))],
    rw [← integral_of_le, integral_eq_sub_of_has_deriv_at'_of_le (neg_le_self zero_le_one)
        ((continuous_arcsin.add (continuous_id.mul hc1)).continuous_on) _ hc2.continuous_on],
    { simp only [arcsin_one, arcsin_neg_one, one_pow, add_zero, nat.neg_one_pow_two, sub_self,
                sqrt_zero, mul_zero, sub_neg_eq_add, add_halves'] },
    { rintros x ⟨hx1, hx2⟩,
      convert (has_deriv_at_arcsin hx1.ne.symm hx2.ne).add ((has_deriv_at_id' x).mul
                (((has_deriv_at_id' x).pow.const_sub 1).sqrt _)),
      { simp only [one_mul, mul_one, zero_sub, nat.cast_bit0, pow_one, nat.cast_one, neg_div],
        rw mul_div_mul_left;
        field_simp [add_left_comm, ← pow_two, tactic.ring.add_neg_eq_sub, div_sqrt, ← two_mul] },
      { nlinarith } },
    { exact neg_le_self zero_le_one } },
  { exact (((hc2.max continuous_const).integrable_on_compact compact_Icc).mono_set
      Ioc_subset_Icc_self).integrable },
  { apply_instance },
end

/-- The area of a disc with radius `r`, which can be represented as the region between the two
    curves `λ x, - sqrt (r ^ 2 - x ^ 2)` and `λ x, sqrt (r ^ 2 - x ^ 2)`, is `π * r ^ 2`. -/
theorem volume_disc' {r : ℝ} (hr : 0 < r) :
  volume.prod volume (disc hr) = ennreal.of_real (pi * r ^ 2) :=
begin
  have : disc hr = region_between (λ x, -sqrt (r^2 - x^2)) (λ x, sqrt (r^2 - x^2)) (Ioc (-r) r),
  { ext p,
    simp only [disc, region_between, mem_set_of_eq, mem_Ioo, mem_Ioc, pi.neg_apply],
    split;
    intro h,
    { split,
      { rw ← sqrt_sqr hr.le,
        have h' : p.1^2 < r^2 := by linarith [pow_two_nonneg p.2],
        exact ⟨sqr_lt_left h', (sqr_lt_right h').le⟩ },
      { rw [add_comm, ← lt_sub_iff_add_lt] at h,
        exact sqr_lt.mp h} },
    { rw [add_comm, ← lt_sub_iff_add_lt],
      exact sqr_lt.mpr h.2 } },
  obtain ⟨hc1, hc2⟩ := ⟨(continuous_const.sub (continuous_pow 2)).sqrt, continuous_const.mul hc1⟩,
  convert volume_region_between_eq_lintegral (hc1.measurable).neg (hc1.measurable)
          is_measurable_Ioc,
  simp only [pi.sub_apply, sub_neg_eq_add, ← two_mul],
  symmetry,
  convert lintegral_coe_eq_integral (λ x, (λ y, nnreal.of_real (2 * sqrt (r^2 - y^2))) x) _,
  { simp only [nnreal.coe_of_real _ (mul_nonneg zero_le_two (sqrt_nonneg _))],
    rw [← integral_of_le,
        integral_eq_sub_of_has_deriv_at'_of_le (neg_le_self hr.le) (((continuous_const.mul
          (continuous_arcsin.comp (continuous_id.div continuous_const (λ x, hr.ne.symm)))).add
            (continuous_id.mul hc1)).continuous_on) _ hc2.continuous_on],
    { simp only [id.def, add_zero, sqrt_zero, arcsin_neg, pi.div_apply, function.comp_app,
                neg_square, mul_zero, sub_self, neg_div, div_self hr.ne.symm, arcsin_one],
      rw [mul_neg_eq_neg_mul_symm, sub_neg_eq_add, ← mul_div_assoc, add_halves', mul_comm] },
    { rintros x ⟨hx1, hx2⟩,
      convert ((has_deriv_at_const x (r^2)).mul ((has_deriv_at_arcsin _ _).comp x
        ((has_deriv_at_id' x).div (has_deriv_at_const x r) hr.ne.symm))).add
          ((has_deriv_at_id' x).mul (((has_deriv_at_id' x).pow.const_sub (r^2)).sqrt _)),
      { have h : sqrt (1 - x ^ 2 / r ^ 2) * r ^ 2 = r * sqrt (r ^ 2 - x ^ 2),
        { rw [← sqrt_sqr (pow_nonneg hr.le 2), ← sqrt_mul, sub_mul, sqrt_sqr (pow_nonneg hr.le 2),
              div_mul_eq_mul_div_comm, pow_two, mul_div_cancel_left _ (pow_ne_zero 2 hr.ne.symm),
              ← mul_assoc, ← sub_mul, mul_comm, sqrt_mul (pow_nonneg hr.le 2), sqrt_sqr hr.le,
              one_mul],
          simpa only [sub_nonneg, sqrt_sqr (pow_nonneg hr.le 2), div_le_one (pow_pos hr 2)] using
            (sqr_lt_sqr' hx1 hx2).le },
        field_simp,
        rw [h, mul_div_assoc, ← div_div_eq_div_mul, div_self hr.ne.symm, mul_one_div, mul_left_comm,
            ← pow_two, neg_div, mul_div_mul_left (x^2) (sqrt (r^2-x^2)) two_ne_zero, ← add_assoc,
            add_right_comm, tactic.ring.add_neg_eq_sub, div_sub_div_same, div_sqrt, two_mul] },
      { by_contra hnot,
        rw [not_not, eq_neg_iff_eq_neg, ← div_neg, eq_comm,
            div_eq_one_iff_eq (neg_ne_zero.mpr hr.ne.symm)] at hnot,
        exact hx1.ne.symm hnot },
      { by_contra hnot,
        rw [not_not, div_eq_one_iff_eq hr.ne.symm] at hnot,
        exact hx2.ne hnot },
      { simpa only [sub_ne_zero] using (sqr_lt_sqr' hx1 hx2).ne.symm } },
    { exact neg_le_self hr.le } },
  { exact (((hc2.max continuous_const).integrable_on_compact compact_Icc).mono_set
      Ioc_subset_Icc_self).integrable },
  { apply_instance },
end


-- **Attempt III - via `region_under` and `region_between`, `integral` version**

/-- The volume of the region between two functions can be respresented as an integral. -/
theorem volume_region_between_eq_integral'
  (u_int : integrable_on u s μ) (v_int : integrable_on v s μ)
  (u_meas : measurable u) (v_meas : measurable v) (hs : is_measurable s)
  (huv : ∀ x ∈ s, u x ≤ v x) :
  μ.prod volume (region_between u v s) = ennreal.of_real (∫ y in s, (v - u) y ∂μ) :=
begin
  let g : α → nnreal := λ x, if h : x ∈ s then ⟨v x - u x, by linarith [huv _ h]⟩ else 0,
  have h1 : (λ x, volume (prod.mk x ⁻¹' region_between u v s)) = s.indicator (λ x, ((g x):ennreal)),
  { simp only [region_between, preimage_set_of_eq],
    funext x,
    rw indicator_apply,
    split_ifs,
    { have hx : {a | x ∈ s ∧ a ∈ Ioo (u x) (v x)} = Ioo (u x) (v x) := by simp [h, Ioo],
      simp only [g, hx, volume_Ioo, sub_zero],
      split_ifs,
      rw ennreal.of_real_eq_coe_nnreal },
    { have hx : {a | x ∈ s ∧ a ∈ Ioo (u x) (v x)} = ∅ := by simp [h],
      simp only [hx, measure_empty] } },
  have h2 : v - u =ᵐ[μ.restrict s] (λ x, ((g x):ℝ)),
  { rw eventually_eq_iff_exists_mem,
    use s,
    simp only [measure.ae, mem_set_of_eq, filter.mem_mk, measure.restrict_apply hs.compl,
              measure_empty, compl_inter_self, eq_self_iff_true, true_and],
    intros x hx,
    simp only [g, pi.sub_apply],
    split_ifs,
    rw subtype.coe_mk },
  rw [measure.prod_apply, h1, lintegral_indicator, integral_congr_ae h2, lintegral_coe_eq_integral],
  exacts [(integrable_congr h2).mp (v_int.sub u_int), hs,
          is_measurable_region_between u_meas v_meas hs],
end

-/
