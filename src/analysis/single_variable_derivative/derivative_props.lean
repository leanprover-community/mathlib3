import .tendsto_punctured
import .derivative

open filter

theorem limit_h_order : ∀ n : ℕ, n ≠ 0 → (tendsto (λ h : ℝ, h^n) (nhds 0) (nhds 0)) :=
begin
  intros n Hn, simp [tendsto_nhds_of_metric, dist],
  intros ε He, existsi (min (1/2 : ℝ) ( (nth_root ε n)/2)), 
  split, 
  { apply lt_min, norm_num, apply half_pos (nth_root_pos (ne_of_gt He)) },
  { intros x Hx, rw abs_pow,
    have Hx1 : abs x < 1, apply @lt_trans ℝ _ _ (1/2) _ (lt_min_iff.mp Hx).1, norm_num,
    have Hx2 : abs x < nth_root ε n := @lt_trans ℝ _ _ ((nth_root ε n)/2) _ (lt_min_iff.mp Hx).2 (half_lt_self (nth_root_pos (ne_of_gt He))),
    cases classical.em (x = 0), { rwa [h, abs_zero, zero_pow (nat.pos_of_ne_zero Hn) ] },
    { rw [←@nth_root_power _ n He (nat.pos_iff_ne_zero.mpr Hn)], 
      apply pow_lt Hx2 (abs_pos_iff.mpr h) (nat.pos_of_ne_zero Hn) } }
end

theorem continuity_of_differentiability_everywhere (f : ℝ → ℝ)
: differentiable_everywhere f → ∀ x : ℝ, tendsto (λ (h : ℝ), f (x + h) - f x) (nhds 0) (nhds 0) :=
begin
  intros hfd x, cases hfd with f' hfd,
  have lifesavingrewrite : (λ (h : ℝ), f (x + h) - f x) = (λ (h : ℝ), (h * ((f (x + h) - f x) / h))),
    funext, 
    cases classical.em (h = 0) with p p,
    { simp [p] },
    { rwa mul_div_cancel' },
  rw lifesavingrewrite,
  apply tendsto_mul_zero_of_zero,
  { apply tendsto_id },
  { rw [tendsto_punctured, ←has_derivative_at_iff_eps_del'], exact hfd x },
  { refl },
  { apply div_zero }
end

theorem derivative_constant_zero (c : ℝ) : has_derivative_everywhere (function.const _ c) 0 :=
begin
  rw function.const, intro x, rw has_derivative_at_iff_eps_del',
  intros ε He, existsi (1 : ℝ), split, norm_num,
  intros, simpa,
end

theorem derivative_add (f : ℝ → ℝ) (f' : ℝ → ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ) (diffdom : set ℝ)
: has_derivative f diffdom f' → has_derivative g diffdom g' → has_derivative (f + g) diffdom (f' + g') :=
begin 
  intros Hf Hg x indom, rw has_derivative_at,
  simp only [pi.add_apply, add_mul, sub_add_eq_sub_sub],
  have convertor : (λ (h : ℝ), (f (x + h) + g (x + h) - f x - g x - f' x * h - g' x * h) / h) 
                 = (λ (h : ℝ), ((f (x + h) - f x - f' x * h) / h + (g (x + h) - g x - g' x * h) / h)),
  { funext, ring },
  rw [←zero_add (0 : ℝ)] {occs := occurrences.pos [2]},
  rw convertor, apply tendsto_add (Hf _ indom) (Hg _ indom),
end

theorem derivative_everywhere_add (f : ℝ → ℝ) (f' : ℝ → ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ) 
: has_derivative_everywhere f f' → has_derivative_everywhere g g' → has_derivative_everywhere (f + g) (f' + g') :=
begin 
  rw [derivative_everywhere_iff_univ, derivative_everywhere_iff_univ, derivative_everywhere_iff_univ], 
  apply derivative_add,
end

theorem derivative_everywhere_sum (s : finset ℕ) (f : ℕ → ℝ → ℝ) (f' : ℕ → ℝ → ℝ)
: (∀ a : ℕ, has_derivative_everywhere (f a) (f' a))
  → has_derivative_everywhere (λ x, finset.sum s (λ a, f a x)) (λ x, finset.sum s (λ a, f' a x)) := 
begin
  intro Df,
  apply finset.induction_on s,
  { simp, apply derivative_constant_zero },
  { intros b t bt Dfs,
    simp [finset.sum_insert bt] at Dfs ⊢,
    apply derivative_everywhere_add _ _ _ _ (Df b) Dfs }
end

theorem derivative_everywhere_mul (f : ℝ → ℝ) (f' : ℝ → ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ)
: has_derivative_everywhere f f' → has_derivative_everywhere g g' → has_derivative_everywhere (f * g) (f' * g + f * g') :=
begin
  intros Hf Hg x, rw has_derivative_at,
  simp only [pi.add_apply, pi.mul_apply, add_mul, sub_add_eq_sub_sub],
  have convertor : (λ (h : ℝ), (f (x + h) * g (x + h) - f x * g x - f' x * g x * h - f x * g' x * h) / h) = 
                   (λ (h : ℝ), g (x) * ((f (x + h) - f (x) - f' x * h) / h) + f (x) * ((g (x + h) - g (x) - g' x * h) / h) + ((f (x + h) - f (x)) * ((g (x + h) - g (x)) / h) )),
  { funext, ring },
  rw convertor, clear convertor,
  rw [←zero_add (0 : ℝ)] {occs := occurrences.pos [2]},
  apply tendsto_add,
  { rw [←zero_add (0 : ℝ)] {occs := occurrences.pos [2]},
    apply tendsto_add,
    { rw [←mul_zero ((g x) : ℝ)] {occs := occurrences.pos [2]},
      apply tendsto_mul, apply tendsto_const_nhds, apply Hf },
    { rw [←mul_zero ((f x) : ℝ)] {occs := occurrences.pos [2]},
      apply tendsto_mul, apply tendsto_const_nhds, apply Hg } },
  { apply tendsto_mul_zero_of_zero,
    { apply continuity_of_differentiability_everywhere,
      existsi f', exact Hf },
    { rw [tendsto_punctured, ←has_derivative_at_iff_eps_del'],
      exact Hg x },
    simp, simp }
end 

theorem derivative_everywhere_const_mul (c : ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) 
: has_derivative_everywhere f f' → has_derivative_everywhere ((function.const _ c) * f) ((function.const _ c) * f') :=
begin
  intro hf,
  have g : has_derivative_everywhere (function.const ℝ c * f) ((function.const ℝ 0) * f + (function.const ℝ c * f'))
    := derivative_everywhere_mul _ _ _ _ (derivative_constant_zero _) hf,
  rwa [(by {funext, simp} : (function.const _ 0) * f = 0), zero_add] at g,
end

theorem derivative_everywhere_const_mul' (c : ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ)
: has_derivative_everywhere f f' → has_derivative_everywhere (λ x, c * f x) (λ x, c * f' x) 
:= derivative_everywhere_const_mul _ _ _

lemma derivative_h_substitution (f f' g : ℝ → ℝ) (Hg : differentiable_everywhere g)
: has_derivative_everywhere f f' 
→ ∀ x : ℝ, tendsto_punctured (λ h, (f (g (x + h)) - f (g x)) / (g (x + h) - g x)) (f' (g x)) := 
begin
  intros Hf x,
  conv { congr, funext, rw [←add_sub_cancel'_right (g x) (g (x + h))] 
       { occs := occurrences.pos [1] } },
  change tendsto_punctured (((λ (H : ℝ), (f (g x + H) - f (g x)) / H)) ∘ (λ h, g (x + h) - g x)) (f' (g x)),
  apply tendsto_punctured_comp,
  { apply tendsto_punctured_of_tendsto _ _ (continuity_of_differentiability_everywhere _ Hg _) },
  { rw [tendsto_punctured, ←has_derivative_at_iff_eps_del'], apply Hf }
end

theorem chain_rule' (f : ℝ → ℝ) (g : ℝ → ℝ) (f' : ℝ → ℝ) (g' : ℝ → ℝ)
: has_derivative_everywhere f f' → has_derivative_everywhere g g' 
→ has_derivative_everywhere (λ x, f (g x)) (λ x, f' (g x) * g' x) :=
begin
  intros Hf Hg x,
  have convertor : (λ h, (f (g (x + h)) - f (g x)) / h) 
                  = λ h, (((f (g (x + h)) - f (g x)) / (g (x + h) - g x)) * ((g (x + h) - g x) / h)),
    funext, cases classical.em (g (x + h) - g x = 0) with Hh Hh,
    { rw [Hh, zero_div, mul_zero, eq_of_sub_eq_zero Hh, sub_self, zero_div] },
    { rw [div_mul_div_cancel], intro H0, apply Hh, rw [H0, add_zero, sub_self], exact Hh },
  rw [has_derivative_at_iff_eps_del', ←tendsto_punctured, convertor],
  apply tendsto_punctured_mul,
  { apply derivative_h_substitution,
    existsi g', exact Hg, exact Hf },
  { rw [tendsto_punctured, ←has_derivative_at_iff_eps_del'], 
    apply has_derivative_at_of_has_derivative_everywhere _ _ _ Hg }                
end

--L' Hospital