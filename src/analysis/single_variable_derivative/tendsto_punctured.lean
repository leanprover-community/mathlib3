import .dependencies
import data.real.basic
import analysis.normed_space

open real filter

def tendsto_punctured (f : ℝ → ℝ) (L : ℝ)
:= ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x ≠ 0 → abs x < δ → abs (f x - L) < ε

private lemma tendsto_mul_zero_of_one (f : ℝ → ℝ) (g : ℝ → ℝ) (L0 : ℝ)
: tendsto f (nhds 0) (nhds 0) → tendsto_punctured g 1 → f 0 = 0 → g 0 = L0 → tendsto (f * g) (nhds 0) (nhds 0) :=
begin
  simp only [tendsto_nhds_of_metric, tendsto_punctured, dist, sub_zero, pi.mul_apply], 
  intros Hf Hg Hf0 Hg0 ε he, 
  cases (Hf (min (abs (ε/(1 + ε))) 1) (lt_min (abs_pos_of_ne_zero (div_ne_zero (ne_of_gt he) (ne_of_gt (add_pos (by norm_num) he)))) (by norm_num))) with δ_f Hf1, 
  cases (Hg (min ε 1) (lt_min he (by norm_num))) with δ_g Hg1,
  cases Hf1 with hd_f Hf2, cases Hg1 with hd_g Hg2, 
  existsi (min δ_f δ_g), existsi (lt_min hd_f hd_g),
  intros x hx, cases (lt_min_iff.mp hx) with hxf hxg,
  cases classical.em (x = 0) with xhole xpunc,
  { simpa [xhole, Hf0] },
  { have Hf3 := lt_min_iff.mp (Hf2 hxf),
    have Hg3 := lt_min_iff.mp (Hg2 x xpunc hxg),
    have Hg4 : abs (g x) < 1 + ε,
      have Hg4'1 := lt_sub_iff_add_lt'.mp ((abs_lt.mp (Hg3.1)).1),
      have Hg4'2 := sub_lt_iff_lt_add'.mp (abs_lt.mp (Hg3.1)).2,
      apply abs_lt.mpr, split;linarith,
    rw [abs_of_pos (div_pos he (add_pos (by norm_num : (1 : ℝ) > 0) he))] at Hf3,
    rw [abs_mul, ←@div_mul_cancel _ _ ε (1 + ε) (ne_of_gt (add_pos (by norm_num : (1 : ℝ) > 0) he))],
    apply mul_lt_mul' (le_of_lt (Hf3.1)) Hg4 (abs_nonneg _) (div_pos he (add_pos (by norm_num : (1 : ℝ) > 0) he)) }
end

lemma tendsto_mul_zero_of_nonzero (f : ℝ → ℝ) (g : ℝ → ℝ) (L0 : ℝ) (L : ℝ) (hL : L ≠ 0)
: tendsto f (nhds 0) (nhds 0) → tendsto_punctured g L → f 0 = 0 → g 0 = L0 → tendsto (f * g) (nhds 0) (nhds 0) :=
begin
  intros tf0 tgL f0 g0,
  change tendsto (λ x, f x * g x) (nhds 0) (nhds 0),
  conv { congr, funext, rw [←div_mul_cancel (g x) hL, ←mul_assoc] },
  rw [←zero_mul L] {occs := occurrences.pos [2]},
  apply tendsto_mul, {
    apply tendsto_mul_zero_of_one,
    { exact tf0 },
    { intros ε he, cases (tgL (abs(L) * ε) (mul_pos (abs_pos_iff.mpr hL) he)) with δ tgL1, cases tgL1 with hd tgL2,
      existsi δ, existsi hd, intros x hx hxd,
      have tgL3 := tgL2 x hx hxd,
      change abs (g x / L - 1) < ε,
      rwa [←mul_lt_mul_left (abs_pos_iff.mpr hL), ←abs_mul, mul_sub, mul_div_cancel' _ hL, mul_one] },
    { exact f0 },
    { rwa div_right_inj hL } },
  { exact tendsto_const_nhds }
end

lemma tendsto_mul_zero_of_zero (f : ℝ → ℝ) (g : ℝ → ℝ) (L : ℝ)
: tendsto f (nhds 0) (nhds 0) → tendsto_punctured g L → f 0 = 0 → g 0 = 0 → tendsto (f * g) (nhds 0) (nhds 0) :=
begin
  cases classical.em (L = 0),
  { rw h, intros tf0 tg0 f0 g0,
    rw [←zero_mul (0 : ℝ)] {occs := occurrences.pos [2]},
    apply tendsto_mul tf0,
    { simp [tendsto_nhds_of_metric, dist],
      intros ε he, cases (tg0 ε he) with δ tg1, cases tg1 with hd tg2,
      existsi δ, existsi hd, intros x hxd,
      have tg3 := tg2 x,
      cases classical.em (x = 0) with hx hx,
      { simpa [hx, g0] },
      { have tg4 := tg3 hx hxd, rwa sub_zero at tg4 } } },
  { apply tendsto_mul_zero_of_nonzero, exact h }
end

lemma tendsto_punctured_of_tendsto (f : ℝ → ℝ) (L : ℝ) : tendsto f (nhds 0) (nhds L) → tendsto_punctured f L :=
begin
  intro,
  simp only [tendsto_nhds_of_metric, dist, sub_zero, tendsto_punctured] at a ⊢,
  intros e he, have a' := a e he, cases a' with d a'', cases a'' with hd a''',
  existsi d, existsi hd, intros x hx, exact a''',
end

lemma tendsto_punctured_iff_tendsto (f : ℝ → ℝ) (L : ℝ)
: tendsto_punctured (λ h, (f h) / h) L ↔ tendsto (λ h, (f h - L * h) / h) (nhds 0) (nhds 0) :=
begin
  split,
  { simp only [tendsto_nhds_of_metric, dist, sub_zero],
    intros Htp ε Hε, have Htp1 := Htp ε Hε,
    cases Htp1 with δ Htp2, cases Htp2 with Hδ Htp3,
    existsi δ, existsi Hδ, intros h Hhd, have Htp4 := Htp3 h,
    cases classical.em (h = 0) with Hh0 Hh0, { simpa [Hh0] },
    rw [sub_div, mul_div_cancel _ Hh0], apply Htp4 Hh0 Hhd },
  { intros Ht ε Hε,
    simp only [tendsto_nhds_of_metric, dist, sub_zero] at Ht ⊢, have Ht1 := Ht ε Hε,
    cases Ht1 with δ Ht1, cases Ht1 with Hδ Ht2, existsi δ, existsi Hδ, 
    intros h Hh0 Hhd, have Ht3 := Ht2 Hhd,
    rwa [sub_div, mul_div_cancel _ Hh0] at Ht3 }
end

lemma tendsto_of_tendsto_punctured (f g : ℝ → ℝ) (L : ℝ) (Hg : g 0 = 0)
: tendsto_punctured (λ h, (f h) / (g h)) L → tendsto (λ h, (f h - L * (g h)) / (g h)) (nhds 0) (nhds 0) :=
begin
  simp only [tendsto_nhds_of_metric, dist, sub_zero],
  intros Htp ε Hε, have Htp1 := Htp ε Hε,
  cases Htp1 with δ Htp2, cases Htp2 with Hδ Htp3,
  existsi δ, existsi Hδ, intros h Hhd, have Htp4 := Htp3 h,
  cases classical.em (g h = 0) with Hg0 Hg0, { simpa [Hg0] },
  rw [sub_div, mul_div_cancel _ Hg0], apply Htp4 _ Hhd,
  intro Hh0, apply Hg0, rwa Hh0
end

lemma tendsto_punctured_comp {f g : ℝ → ℝ} {x : ℝ} 
: tendsto_punctured g 0 → tendsto_punctured f x → tendsto_punctured (f ∘ g) x := 
begin
  /-intros Hg Hf ε Hε,
  rcases (Hf ε Hε) with ⟨δ₁, ⟨Hδ₁, Hf3⟩⟩,
  rcases (Hg ε Hε) with ⟨δ₂, ⟨Hδ₂, Hg3⟩⟩,-/
  intros Hg Hf ε Hε,
  have Hf1 := Hf ε Hε, cases Hf1 with δ₁ Hf2, cases Hf2 with Hδ₁ Hf3,
  have Hg1 := Hg δ₁ Hδ₁, cases Hg1 with δ₂ Hg2, cases Hg2 with Hδ₂ Hg3,
  existsi (min δ₁ δ₂), existsi (lt_min Hδ₁ Hδ₂), intros h Hh0 Hhd, 
  have Hg4 := Hg3 h Hh0 (lt_min_iff.mp Hhd).2, have Hf4 := Hf3 (g h),
  simp at Hg4,
  cases classical.em (g h = 0) with p p,
  { rw [function.comp_app, p], sorry },
  { exact Hf4 p Hg4 }  
end

lemma tendsto_punctured_neg {f : ℝ → ℝ} {L : ℝ} : tendsto_punctured f L → tendsto_punctured (-f) (-L) :=
begin
  intros Hf ε Hε, have Hf1 := Hf ε Hε, cases Hf1 with δ Hf2, cases Hf2 with Hδ Hf3, existsi δ, existsi Hδ,
  intros x hole Hx, have Hf4 := Hf3 x hole Hx,
  rwa [pi.neg_apply, ←neg_neg (-f x - -L), neg_neg_sub_neg, abs_neg],
end

lemma tendsto_punctured_neg_iff (f : ℝ → ℝ) (L : ℝ) : tendsto_punctured f L ↔ tendsto_punctured (-f) (-L) :=
begin
  split, {apply tendsto_punctured_neg },
  intro temp, rw [←neg_neg f, ←neg_neg L],
  apply tendsto_punctured_neg temp,
end

private lemma tendsto_punctured_mul_of_pos_nonneg (f : ℝ → ℝ) (g : ℝ → ℝ) {Lf : ℝ} {Lg : ℝ} (hLf : Lf > 0) (hLg : Lg ≥ 0)
: tendsto_punctured f Lf → tendsto_punctured g Lg → tendsto_punctured (f * g) (Lf * Lg) :=
begin
  intros Hf Hg ε Hε, 
  have hLgf : Lg + Lf > 0 := add_pos_of_nonneg_of_pos hLg hLf,
  have h : Lg + Lf ≠ 0 := ne_of_gt hLgf,
  have Hf1 := Hf (min  (min ((ε / 4)/(abs (Lg + Lf))) ((sqrt ε) / 4)) (2 / 3))
    (lt_min (lt_min (div_pos (div_pos Hε (by norm_num))
    (abs_pos_of_ne_zero h)) (div_pos (sqrt_pos.mpr Hε) (by norm_num))) (by norm_num)),
  have Hg1 := Hg (min (min ((ε / 4)/(abs (Lg + Lf))) ((sqrt ε) / 4)) (2 / 3))
    (lt_min (lt_min (div_pos (div_pos Hε (by norm_num))
    (abs_pos_of_ne_zero h)) (div_pos (sqrt_pos.mpr Hε) (by norm_num))) (by norm_num)),
  cases Hf1 with δ₁ Hf2, cases Hf2 with Hδ₁ Hf3,
  cases Hg1 with δ₂ Hg2, cases Hg2 with Hδ₂ Hg3,
  existsi (min δ₁ δ₂), existsi lt_min Hδ₁ Hδ₂,
  intros x hole Hx, rw pi.mul_apply,
  have Hf4 := lt_min_iff.mp (Hf3 x hole (lt_min_iff.mp Hx).1), rw lt_min_iff at Hf4,
  have Hg4 := lt_min_iff.mp (Hg3 x hole (lt_min_iff.mp Hx).2), rw lt_min_iff at Hg4,
  have convertor : f x * g x - Lf * Lg = (f x - Lf) * Lg + (g x - Lg) * Lf + (f x - Lf) * (g x - Lg) := by ring,
  rw convertor,
  apply lt_of_le_of_lt (abs_add_three _ _ _ : 
                      _ ≤  abs ((f x - Lf) * Lg) + abs ((g x - Lg) * Lf) + abs((f x - Lf) * (g x - Lg))),
  rw [abs_mul, abs_mul, abs_mul],
  apply lt_of_le_of_lt ( _ : _ ≤ (ε / 4 / abs (Lg + Lf)) * abs Lg + abs (g x - Lg) * abs Lf + abs (f x - Lf) * abs (g x - Lg)),
  swap,
    rw [add_le_add_iff_right, add_le_add_iff_right],
    apply mul_le_mul_of_nonneg_right (le_of_lt Hf4.1.1) (abs_nonneg _),
  apply lt_of_le_of_lt ( _ : _ ≤ (ε / 4 / abs (Lg + Lf)) * abs Lg + (ε / 4 / abs (Lg + Lf)) * abs Lf + abs (f x - Lf) * abs (g x - Lg)),
  swap,
    rw [add_le_add_iff_right, add_le_add_iff_left],
    apply mul_le_mul_of_nonneg_right (le_of_lt Hg4.1.1) (abs_nonneg _),
  apply lt_of_le_of_lt (_ : _ ≤ ε / 4 / abs (Lg + Lf) * abs Lg + ε / 4 / abs (Lg + Lf) * abs Lf + ((sqrt ε) / 4) * ((sqrt ε) / 4)),
  swap,
    rw add_le_add_iff_left,
    apply mul_le_mul (le_of_lt Hf4.1.2) (le_of_lt Hg4.1.2) (abs_nonneg _) (le_of_lt (div_pos (sqrt_pos.mpr Hε) (by norm_num))),
  rw [←mul_add, ←pow_two, div_pow _ (by norm_num : (4 : ℝ) ≠ 0) _, sqr_sqrt (le_of_lt Hε), 
      abs_of_pos hLf, abs_of_nonneg hLg, abs_of_pos hLgf, div_mul_cancel _ h, 
      div_eq_mul_one_div, div_eq_mul_one_div ε _, ←mul_add, mul_lt_iff_lt_one_right Hε],
  norm_num
end

private lemma tendsto_punctured_mul_of_nonneg_nonneg (f : ℝ → ℝ) (g : ℝ → ℝ) {Lf : ℝ} {Lg : ℝ} (hLf : Lf ≥ 0) (hLg : Lg ≥ 0)
: tendsto_punctured f Lf → tendsto_punctured g Lg → tendsto_punctured (f * g) (Lf * Lg) :=
begin
  cases lt_or_eq_of_le hLf with hLf' hLf',
  { apply tendsto_punctured_mul_of_pos_nonneg _ _ hLf' hLg },
  cases lt_or_eq_of_le hLg with hLg' hLg',
  { intros hf hg, revert hg hf, rw [mul_comm, mul_comm Lf],
    apply tendsto_punctured_mul_of_pos_nonneg _ _ hLg' hLf },
  rw [←hLf', ←hLg', zero_mul],
  intros hf hg ε Hε,
  have hf1 := hf (sqrt ε) (sqrt_pos.mpr Hε), cases hf1 with δ₁ hf2, cases hf2 with Hδ₁ hf3,
  have hg1 := hg (sqrt ε) (sqrt_pos.mpr Hε), cases hg1 with δ₂ hg2, cases hg2 with Hδ₂ hg3,
  existsi (min δ₁ δ₂), existsi lt_min Hδ₁ Hδ₂, intros x hole hx,
  have hf4 := hf3 x hole (lt_min_iff.mp hx).1,
  have hg4 := hg3 x hole (lt_min_iff.mp hx).2,
  rw sub_zero at hf4 hg4 ⊢,
  rw [pi.mul_apply, abs_mul, ←sqrt_mul_self (le_of_lt Hε), sqrt_mul (le_of_lt Hε)],
  apply mul_lt_mul' (le_of_lt hf4) hg4 (abs_nonneg _) (sqrt_pos.mpr Hε)
end

lemma tendsto_punctured_mul (f : ℝ → ℝ) (g : ℝ → ℝ) (Lf : ℝ) (Lg : ℝ)
: tendsto_punctured f Lf → tendsto_punctured g Lg → tendsto_punctured (f * g) (Lf * Lg) :=
begin
  cases lt_or_ge Lf 0 with hLf hLf,
  { cases lt_or_ge Lg 0 with hLg hLg,
    { have hLf' := neg_nonneg_of_nonpos (le_of_lt hLf),
      have hLg' := neg_nonneg_of_nonpos (le_of_lt hLg),
      rw [tendsto_punctured_neg_iff f, tendsto_punctured_neg_iff g, ←neg_mul_neg, ←neg_mul_neg Lf],
      apply tendsto_punctured_mul_of_nonneg_nonneg _ _ hLf' hLg' },
    { have hLf' := neg_nonneg_of_nonpos (le_of_lt hLf),
      rw [tendsto_punctured_neg_iff f, tendsto_punctured_neg_iff (f * g), neg_mul_eq_neg_mul, neg_mul_eq_neg_mul],
      apply tendsto_punctured_mul_of_nonneg_nonneg _ _ hLf' hLg } },
  { cases lt_or_ge Lg 0 with hLg hLg,
    { have hLg' := neg_nonneg_of_nonpos (le_of_lt hLg),
      rw [tendsto_punctured_neg_iff g, tendsto_punctured_neg_iff (f * g), neg_mul_eq_mul_neg, neg_mul_eq_mul_neg],
      apply tendsto_punctured_mul_of_nonneg_nonneg _ _ hLf hLg' },
    { exact tendsto_punctured_mul_of_nonneg_nonneg _ _ hLf hLg } }
end
