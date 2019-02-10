import data.real.basic
import analysis.normed_space

open filter

def has_derivative_at (f : ℝ → ℝ) (x0 : ℝ) (f'x0 : ℝ) : Prop 
:= (tendsto (λ h, (f (x0 + h) - f (x0) - f'x0 * h)/h) (nhds 0) (nhds 0))

lemma has_derivative_at_iff_eps_del (f : ℝ → ℝ) (x0 : ℝ) (f'x0 : ℝ)
: has_derivative_at f x0 f'x0 ↔
  ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, abs h < δ → abs ((f(x0 + h) - f(x0) - f'x0 * h) / h) < ε 
  := by simp [has_derivative_at, tendsto_nhds_of_metric, dist]

lemma has_derivative_at_iff_eps_del' (f : ℝ → ℝ) (x0 : ℝ) (f'x0 : ℝ)
: has_derivative_at f x0 f'x0 ↔
  ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, h ≠ 0 → abs h < δ → abs ((f(x0 + h) - f(x0))/h - f'x0) < ε :=
  begin
  rw has_derivative_at_iff_eps_del, split,
  { intros a ε Hε, have a1 := a ε Hε, cases a1 with δ a2, cases a2 with Hd a3,
    existsi δ, existsi Hd, intros h Hh, have a4 := a3 h, 
    rwa [sub_div, mul_div_cancel _ Hh ] at a4 },
  { intros a ε He, have a1 := a ε He, cases a1 with δ a2, cases a2 with Hd a3,
    existsi δ, existsi Hd, intro h, have a4 := a3 h, intro Hhd,
    cases classical.em (h ≠ 0) with N Y,
    { have a5 := a4 N Hhd, rwa [sub_div, mul_div_cancel _ N ] },
    { rw auto.not_not_eq at Y, simpa [Y] } }
  end

def has_derivative (f : ℝ → ℝ) (diffdom : set ℝ) (f' : ℝ → ℝ) 
:= ∀ x ∈ diffdom, has_derivative_at f x (f' x)

def has_derivative_everywhere (f : ℝ → ℝ) (f' : ℝ → ℝ) := ∀ x : ℝ, has_derivative_at f x (f' x)

lemma has_derivative_of_has_derivative_everywhere {f : ℝ → ℝ} {f' : ℝ → ℝ} {diffdom : set ℝ}
: has_derivative_everywhere f f' → has_derivative f diffdom f' := λ R x D, R x

lemma has_derivative_at_of_has_derivative (f : ℝ → ℝ) (x : ℝ) (diffdom : set ℝ) (f' : ℝ → ℝ) (Hx : x ∈ diffdom)
: has_derivative f diffdom f' → has_derivative_at f x (f' x) := λ a, a x Hx

lemma has_derivative_at_of_has_derivative_everywhere (f : ℝ → ℝ) (x : ℝ) (f' : ℝ → ℝ) 
: has_derivative_everywhere f f' → has_derivative_at f x (f' x) := λ a, a x

lemma derivative_everywhere_iff_univ (f : ℝ → ℝ) (f' : ℝ → ℝ) 
: has_derivative_everywhere f f' ↔ has_derivative f (set.univ) f' :=
⟨λ t x hx, has_derivative_at_of_has_derivative_everywhere f x f' t, λ s x, s x true.intro⟩

def differentiable_at (f : ℝ → ℝ) (x : ℝ) := ∃ f'x, has_derivative_at f x f'x

def differentiable_at' (f : ℝ → ℝ) (x : ℝ) := ∃ f' : ℝ → ℝ, has_derivative_at f x (f' x)

def differentiable (f : ℝ → ℝ) (diffdom : set ℝ) := ∃ f', has_derivative f diffdom f'

def differentiable_everywhere (f : ℝ → ℝ) := ∃ f', has_derivative_everywhere f f'

lemma derivative_at_unique (f : ℝ → ℝ) (x : ℝ)
: ∀ (y₁ y₂ : ℝ), has_derivative_at f x y₁ → has_derivative_at f x y₂ → y₁ = y₂ :=
begin
  intros L1 L2 H1 H2, rw has_derivative_at_iff_eps_del' at H1 H2, by_contradiction,
  have H11 := H1 (abs((L1 - L2))/2) (half_pos(abs_pos_of_ne_zero (sub_ne_zero_of_ne a))),
  have H21 := H2 (abs((L1 - L2))/2) (half_pos(abs_pos_of_ne_zero (sub_ne_zero_of_ne a))),
  cases H11 with δ₁ H12, cases H12 with Hd1 H13, cases H21 with δ₂ H22, cases H22 with Hd2 H23,
  have D1 : abs (min δ₁ δ₂ / 2) < δ₁, 
    rw abs_of_pos (half_pos (lt_min Hd1 Hd2)), 
    apply lt_of_lt_of_le (half_lt_self(lt_min Hd1 Hd2)) (min_le_left δ₁ δ₂),
  have D2 : abs (min δ₁ δ₂ / 2) < δ₂, 
    rw abs_of_pos (half_pos (lt_min Hd1 Hd2)), 
    apply lt_of_lt_of_le (half_lt_self(lt_min Hd1 Hd2)) (min_le_right δ₁ δ₂),
  have H14 := H13 ((min δ₁ δ₂)/2) (ne_of_gt (half_pos (lt_min Hd1 Hd2))) D1,
  have H24 := H23 ((min δ₁ δ₂)/2) (ne_of_gt (half_pos (lt_min Hd1 Hd2))) D2,
  have H15 := abs_lt.mp H14, have H25 := abs_lt.mp H24,
  cases lt_or_gt_of_ne a with a1 a2,
  { rw ←sub_lt_zero at a1,
    have H16 := H15.2, have H26 := H25.1, clear H15 H25 H14 H24 H13 H23 H1 H2 a,
    rw [abs_of_neg a1, sub_lt_iff_lt_add', neg_div, sub_div L1, ←sub_eq_add_neg, ←sub_add, sub_half] at H16,
    rw [abs_of_neg a1, lt_sub_iff_add_lt, neg_div, neg_neg, sub_div L1, sub_add, half_sub, sub_neg_eq_add] at H26,
    revert H26, apply not_lt_of_gt H16 },
  { change L2 < L1 at a2, rw ←sub_pos at a2,
    have H16 := H15.1, have H26 := H25.2, clear H15 H25 H14 H24 H13 H23 H1 H2 a,
    rw [abs_of_pos a2, lt_sub_iff_add_lt, sub_div, ←sub_eq_neg_add, ←sub_add, sub_half] at H16,
    rw [abs_of_pos a2, sub_lt_iff_lt_add, sub_div L1, sub_add, half_sub, sub_neg_eq_add] at H26,
    revert H26, apply not_lt_of_gt H16 }
end

lemma derivative_at_exists_unique (f : ℝ → ℝ) (x : ℝ) (Hdiff : differentiable_at f x)
: (∃! f'x, has_derivative_at f x f'x) 
:= exists_unique_of_exists_of_unique Hdiff (derivative_at_unique f x)

lemma derivative_unique (f : ℝ → ℝ) (diffdom : set ℝ) 
: ∀ (f₁ f₂ : ℝ → ℝ), has_derivative f diffdom f₁ → has_derivative f diffdom f₂ → ∀ x ∈ diffdom, f₁ x = f₂ x 
:= λ f₁ f₂ H1 H2 x Hx, derivative_at_unique _ _ _ _ (H1 x Hx) (H2 x Hx)

lemma derivative_everywhere_unique (f : ℝ → ℝ)
: ∀ (f₁ f₂ : ℝ → ℝ), has_derivative_everywhere f f₁ → has_derivative_everywhere f f₂ → f₁ = f₂ 
:= λ f₁ f₂ H1 H2, funext (λ x, derivative_at_unique _ _ _ _ (H1 _) (H2 _))

lemma derivative_everywhere_exists_unique (f : ℝ → ℝ) (Hdiff : ∃ f', has_derivative_everywhere f f')
: ∃! f', has_derivative_everywhere f f' 
:= exists_unique_of_exists_of_unique Hdiff (derivative_everywhere_unique f)
