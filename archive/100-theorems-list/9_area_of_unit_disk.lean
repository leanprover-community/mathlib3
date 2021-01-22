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


-- **Ben's assorted sqrt, sqr, and abs lemmas**

-- A stronger version of Andrew's `lt_sqrt`.
lemma lt_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x < sqrt y ↔ x ^ 2 < y :=
by rw [mul_self_lt_mul_self_iff hx (sqrt_nonneg y), pow_two, mul_self_sqrt hy]

lemma lt_sqrt_of_sqr_lt {a b : ℝ} (h : a^2 < b) : a < sqrt b :=
begin
  by_contra hnot,
  rw [le_antisymm (le_sqrt_of_sqr_le _) (not_lt.mp hnot), sqr_sqrt] at h,
  exacts [h.false, (lt_of_le_of_lt (pow_two_nonneg _) h).le, h.le],
end

lemma sqrt_ne_zero_iff {x : ℝ} (hle : 0 ≤ x) : sqrt x ≠ 0 ↔ x ≠ 0 :=
by rw [not_iff_not, sqrt_eq_zero hle]

lemma sqrt_ne_zero {x : ℝ} (hlt : 0 < x) : sqrt x ≠ 0 :=
(sqrt_pos.mpr hlt).ne.symm

-- A stronger version of James' `aux_sqrt_lemma`.
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

lemma le_abs {a b : ℝ} : a ≤ abs b ↔ a ≤ b ∨ a ≤ -b := le_max_iff

lemma abs_le_left {a b : ℝ} (h : abs a ≤ b) : -b ≤ a := (abs_le.mp h).1

lemma abs_le_right {a b : ℝ} (h : abs a ≤ b) : a ≤ b := (abs_le.mp h).2

lemma abs_lt_left {a b : ℝ} (h : abs a < b) : -b < a := (abs_lt.mp h).1

lemma abs_lt_right {a b : ℝ} (h : abs a < b) : a < b := (abs_lt.mp h).2

theorem sqr_le {a b : ℝ} (h : a^2 ≤ b) : -sqrt b ≤ a ∧ a ≤ sqrt b :=
abs_le.mp (by simpa [← sqrt_sqr_eq_abs] using sqrt_le_sqrt h)

theorem sqr_le_of_nonneg {a b : ℝ} (h : 0 ≤ b) : a^2 ≤ b ↔ -sqrt b ≤ a ∧ a ≤ sqrt b :=
⟨sqr_le, (by rw [← abs_le, ← sqr_abs]; exact (le_sqrt (abs_nonneg a) h).mp)⟩

lemma sqr_le_left {a b : ℝ} (h : a^2 ≤ b) : -sqrt b ≤ a := (sqr_le h).1

lemma sqr_le_right {a b : ℝ} (h : a^2 ≤ b) : a ≤ sqrt b := (sqr_le h).2

theorem sqr_lt {a b : ℝ} : a^2 < b ↔ -sqrt b < a ∧ a < sqrt b :=
begin
  split,
  { simpa only [← sqrt_lt (pow_two_nonneg a), sqrt_sqr_eq_abs] using abs_lt.mp },
  { rw [← abs_lt, ← sqr_abs],
    exact λ h, (lt_sqrt (abs_nonneg a) (sqrt_pos.mp (lt_of_le_of_lt (abs_nonneg a) h)).le).mp h },
end

-- Originally Andrew's `opposite_sqrt_lt_of_sqr_lt`.
lemma sqr_lt_left {a b : ℝ} (h : a^2 < b) : -sqrt b < a := (sqr_lt.mp h).1

lemma sqr_lt_right {a b : ℝ} (h : a^2 < b) : a < sqrt b := (sqr_lt.mp h).2


-- **FTC-2 stuff**

open_locale topological_space

variables {E : Type*} [measurable_space E] [normed_group E] [normed_space ℝ E]
  [borel_space E] [complete_space E] [topological_space.second_countable_topology E]
  {a b : ℝ} {f f' : ℝ → E}

-- FTC-2 for the open set. **(PR #5733)**
theorem integral_eq_sub_of_has_deriv_at'' (hcont : continuous_on f (interval a b))
  (hderiv : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_at f (f' x) x)
  (hcont' : continuous_on f' (interval a b)) :
  ∫ y in a..b, f' y = f b - f a :=
begin
  refine integral_eq_sub_of_has_deriv_right hcont _ hcont',
  intros y hy',
  obtain (hy | hy) : y ∈ Ioo (min a b) (max a b) ∨ min a b = y ∧ y < max a b :=
    by simpa only [le_iff_lt_or_eq, or_and_distrib_right, mem_Ioo, mem_Ico] using hy',
  { exact (hderiv y hy).has_deriv_within_at },
  { have : tendsto f' (𝓝[Ioi y] y) (𝓝 (f' y)) :=
      tendsto.mono_left (by simpa only [← nhds_within_Icc_eq_nhds_within_Ici hy.2, interval, hy.1]
                          using hcont'.continuous_within_at (left_mem_Icc.mpr min_le_max))
        (nhds_within_mono y Ioi_subset_Ici_self),
    exact has_deriv_at_interval_left_endpoint_of_tendsto_deriv
      (λ x hx, (hderiv x hx).has_deriv_within_at.differentiable_within_at)
        ((hcont y (Ico_subset_Icc_self hy')).mono Ioo_subset_Icc_self) (Ioo_mem_nhds_within_Ioi hy')
          (by rwa tendsto_congr' (eventually_of_mem (Ioo_mem_nhds_within_Ioi hy')
            (λ x hx, (hderiv x hx).deriv))) },
  end

theorem integral_eq_sub_of_has_deriv_at'_of_le (hab : a ≤ b)
  (hcont : continuous_on f (interval a b))
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hcont' : continuous_on f' (interval a b)) :
  ∫ y in a..b, f' y = f b - f a :=
integral_eq_sub_of_has_deriv_at'' hcont (by rwa [min_eq_left hab, max_eq_right hab]) hcont'


-- **Attempt I - via `is_measurable_unit_disc`**

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

--Definition of the unit disc.
def unit_disc := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}

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


-- **Attempt II - via `volume_under` and `volume_between`, `lintegral` version**

variables {α : Type*} [measure_space α] [sigma_finite (volume : measure α)]

open_locale classical

def volume_between (u v : α → ℝ) (s : set α) : set (α × ℝ) :=
{ p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Ioo (u p.1) (v p.1) }

def volume_under (v : α → ℝ) (s : set α) : set (α × ℝ) :=
{ p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Ico 0 (v p.1) }

variables {u v : α → ℝ} {s : set α}

/-- The volume between two functions is measurable. -/
lemma is_measurable_volume_between (hu : measurable u) (hv: measurable v) (hs : is_measurable s) :
  is_measurable (volume_between u v s) :=
begin
  dsimp only [volume_between, Ioo, mem_set_of_eq, set_of_and],
  refine is_measurable.inter _ ((is_measurable_lt (hu.comp measurable_fst) measurable_snd).inter
    (is_measurable_lt measurable_snd (hv.comp measurable_fst))),
  have h : {p : α × ℝ | p.1 ∈ s} = {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ (univ : set ℝ)} := by simp,
  convert hs.prod is_measurable.univ,
end

/-- The volume between two functions can be respresented as a left integral -/
theorem volume_between_eq_lintegral (hu : measurable u) (hv : measurable v) (hs : is_measurable s) :
  volume.prod volume (volume_between u v s) = ∫⁻ y in s, ennreal.of_real ((v - u) y) :=
begin
  rw measure.prod_apply (is_measurable_volume_between hu hv hs),
  { have h : (λ x, volume {a | x ∈ s ∧ a ∈ Ioo (u x) (v x)}) = s.indicator (λ x, ennreal.of_real (v x - u x)),
    { funext x,
      rw indicator_apply,
      split_ifs,
      { have hx : {a | x ∈ s ∧ a ∈ Ioo (u x) (v x)} = Ioo (u x) (v x) := by simp [h, Ioo],
        simp only [hx, volume_Ioo, sub_zero] },
      { have hx : {a | x ∈ s ∧ a ∈ Ioo (u x) (v x)} = ∅ := by simp [h],
        simp only [hx, measure_empty] } },
    dsimp only [volume_between, preimage_set_of_eq],
    rw [h, lintegral_indicator];
    simp only [hs, pi.sub_apply], },
  { apply_instance },
end

/-- The volume "under" a function is measurable. -/
lemma is_measurable_volume_under (hv : measurable v) (hs : is_measurable s) :
  is_measurable (volume_under v s) :=
begin
  dsimp only [volume_under, Ico, mem_set_of_eq, set_of_and],
  refine is_measurable.inter _ ((is_measurable_le measurable_const measurable_snd).inter
    (is_measurable_lt measurable_snd (hv.comp measurable_fst))),
  have : {p : α × ℝ | p.1 ∈ s} = {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ (univ : set ℝ)} := by simp,
  convert hs.prod is_measurable.univ,
end

/-- The volume "under" a function can be respresented as a left integral -/
theorem volume_under_eq_lintegral (hv : measurable v) (hs : is_measurable s) :
  (volume.prod volume) (volume_under v s) = ∫⁻ y in s, ennreal.of_real (v y) :=
begin
  rw measure.prod_apply (is_measurable_volume_under hv hs),
  { have h : (λ x, volume {a | x ∈ s ∧ a ∈ Ico 0 (v x)}) = s.indicator (λ x, ennreal.of_real (v x)),
    { funext x,
      rw indicator_apply,
      split_ifs,
      { have hx : {a | x ∈ s ∧ a ∈ Ico 0 (v x)} = Ico 0 (v x) := by simp [h, Ico],
        simp only [hx, volume_Ico, sub_zero] },
      { have hx : {a | x ∈ s ∧ a ∈ Ico 0 (v x)} = ∅ := by simp [h],
        simp only [hx, measure_empty] } },
    dsimp only [volume_under, preimage_set_of_eq],
    rwa [h, lintegral_indicator] },
  { apply_instance },
end

/-- The area of the unit disc, which can be represented as the area between the two curves
    `λ x, -sqrt (1 - x^2)` and `λ x, sqrt (1 - x^2)`, is `π`. -/
theorem volume_unit_disc' : volume.prod volume unit_disc = ennreal.of_real pi :=
begin
  have : unit_disc = volume_between (λ x, -sqrt (1 - x^2)) (λ x, sqrt (1 - x^2)) (Ioc (-(1:ℝ)) 1),
  { ext p,
    simp only [unit_disc, volume_between, mem_set_of_eq, mem_Ioo, mem_Ioc, pi.neg_apply],
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
  convert volume_between_eq_lintegral (hc1.measurable).neg (hc1.measurable) is_measurable_Ioc,
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
end

def disc {r : ℝ} (h : 0 < r) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}

/-- The area of a disc with radius `r`, which can be represented as the region between the two
    curves `λ x, - sqrt (r ^ 2 - x ^ 2)` and `λ x, sqrt (r ^ 2 - x ^ 2)`, is `π * r ^ 2`. -/
theorem volume_disc {r : ℝ} (hr : 0 < r) :
  volume.prod volume (disc hr) = ennreal.of_real (pi * r ^ 2) :=
begin
  have : disc hr = volume_between (λ x, -sqrt (r^2 - x^2)) (λ x, sqrt (r^2 - x^2)) (Ioc (-r) r),
  { ext p,
    simp only [disc, volume_between, mem_set_of_eq, mem_Ioo, mem_Ioc, pi.neg_apply],
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
  convert volume_between_eq_lintegral (hc1.measurable).neg (hc1.measurable) is_measurable_Ioc,
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
          simpa only [sub_nonneg, sqrt_sqr (pow_nonneg hr.le 2), div_le_one (pow_pos hr 2), sqr_abs]
            using pow_le_pow_of_le_left (abs_nonneg x) (abs_le.mpr ⟨hx1.le, hx2.le⟩) 2 },
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
      { simpa only [sub_ne_zero, sqr_abs] using
          (pow_lt_pow_of_lt_left (abs_lt.mpr ⟨hx1, hx2⟩) (abs_nonneg x) zero_lt_two).ne.symm } },
    { exact neg_le_self hr.le } },
  { exact (((hc2.max continuous_const).integrable_on_compact compact_Icc).mono_set
      Ioc_subset_Icc_self).integrable },
end

/-- The area of the unit disc is `π`. -/
theorem volume_unit_disc : volume.prod volume (disc zero_lt_one) = ennreal.of_real pi :=
by simpa only [one_pow, mul_one] using volume_disc zero_lt_one


-- **Attempt III - via `volume_under` and `volume_between`, `integral` version**

/-- The volume between two functions can be respresented as an integral -/
theorem volume_between_eq_integral (u_int : integrable_on u s) (v_int : integrable_on v s)
  (u_meas : measurable u) (v_meas : measurable v) (hs : is_measurable s)
  (huv : ∀ x ∈ s, u x ≤ v x) :
  volume.prod volume (volume_between u v s) = ennreal.of_real (∫ y in s, (v - u) y) :=
begin
  rw measure.prod_apply (is_measurable_volume_between u_meas v_meas hs),
  { let g : α → nnreal := λ x, if h : x ∈ s then ⟨v x - u x, by linarith [huv _ h]⟩ else 0,
    have h1 : (λ x, volume (prod.mk x ⁻¹' volume_between u v s)) = s.indicator (λ x, ↑(g x)),
    { simp only [volume_between, preimage_set_of_eq],
      funext x,
      rw indicator_apply,
      split_ifs,
      { have hx : {a | x ∈ s ∧ a ∈ Ioo (u x) (v x)} = Ioo (u x) (v x) := by simp [h, Ioo],
        simp only [g, hx, volume_Ioo, sub_zero],
        split_ifs,
        rw ennreal.of_real_eq_coe_nnreal },
      { have hx : {a | x ∈ s ∧ a ∈ Ioo (u x) (v x)} = ∅ := by simp [h],
        simp only [hx, measure_empty] } },
    have h2 : v - u =ᵐ[volume.restrict s] (λ x, ((g x):ℝ)),
    { rw eventually_eq_iff_exists_mem,
      use s,
      simp only [measure.ae, mem_set_of_eq, filter.mem_mk, measure.restrict_apply hs.compl,
                measure_empty, compl_inter_self, eq_self_iff_true, true_and],
      intros x hx,
      simp only [g, pi.sub_apply],
      split_ifs,
      rw subtype.coe_mk },
    rw [h1, lintegral_indicator, integral_congr_ae h2, lintegral_coe_eq_integral],
    exacts [(integrable_congr h2).mp (v_int.sub u_int), hs] },
  { apply_instance },
end
