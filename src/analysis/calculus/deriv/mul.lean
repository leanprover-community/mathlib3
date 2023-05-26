import analysis.calculus.deriv.basic
import analysis.calculus.fderiv.mul
import analysis.calculus.fderiv.add

universes u v w
noncomputable theory
open_locale classical topology big_operators filter ennreal
open filter asymptotics set
open continuous_linear_map (smul_right smul_right_one_eq_iff)


variables {𝕜 : Type u} [nontrivially_normed_field 𝕜]
variables {F : Type v} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {E : Type w} [normed_add_comm_group E] [normed_space 𝕜 E]

variables {f f₀ f₁ g : 𝕜 → F}
variables {f' f₀' f₁' g' : F}
variables {x : 𝕜}
variables {s t : set 𝕜}
variables {L L₁ L₂ : filter 𝕜}

section smul

/-! ### Derivative of the multiplication of a scalar function and a vector function -/

variables {𝕜' : Type*} [nontrivially_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
  [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {c : 𝕜 → 𝕜'} {c' : 𝕜'}

theorem has_deriv_within_at.smul
  (hc : has_deriv_within_at c c' s x) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ y, c y • f y) (c x • f' + c' • f x) s x :=
by simpa using (has_fderiv_within_at.smul hc hf).has_deriv_within_at

theorem has_deriv_at.smul
  (hc : has_deriv_at c c' x) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ y, c y • f y) (c x • f' + c' • f x) x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.smul hf
end

theorem has_strict_deriv_at.smul
  (hc : has_strict_deriv_at c c' x) (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ y, c y • f y) (c x • f' + c' • f x) x :=
by simpa using (hc.smul hf).has_strict_deriv_at

lemma deriv_within_smul (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) :
  deriv_within (λ y, c y • f y) s x = c x • deriv_within f s x + (deriv_within c s x) • f x :=
(hc.has_deriv_within_at.smul hf.has_deriv_within_at).deriv_within hxs

lemma deriv_smul (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
  deriv (λ y, c y • f y) x = c x • deriv f x + (deriv c x) • f x :=
(hc.has_deriv_at.smul hf.has_deriv_at).deriv

theorem has_strict_deriv_at.smul_const
  (hc : has_strict_deriv_at c c' x) (f : F) :
  has_strict_deriv_at (λ y, c y • f) (c' • f) x :=
begin
  have := hc.smul (has_strict_deriv_at_const x f),
  rwa [smul_zero, zero_add] at this,
end

theorem has_deriv_within_at.smul_const
  (hc : has_deriv_within_at c c' s x) (f : F) :
  has_deriv_within_at (λ y, c y • f) (c' • f) s x :=
begin
  have := hc.smul (has_deriv_within_at_const x s f),
  rwa [smul_zero, zero_add] at this
end

theorem has_deriv_at.smul_const
  (hc : has_deriv_at c c' x) (f : F) :
  has_deriv_at (λ y, c y • f) (c' • f) x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.smul_const f
end

lemma deriv_within_smul_const (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (f : F) :
  deriv_within (λ y, c y • f) s x = (deriv_within c s x) • f :=
(hc.has_deriv_within_at.smul_const f).deriv_within hxs

lemma deriv_smul_const (hc : differentiable_at 𝕜 c x) (f : F) :
  deriv (λ y, c y • f) x = (deriv c x) • f :=
(hc.has_deriv_at.smul_const f).deriv

end smul

section const_smul

variables {R : Type*} [semiring R] [module R F] [smul_comm_class 𝕜 R F]
  [has_continuous_const_smul R F]

theorem has_strict_deriv_at.const_smul
  (c : R) (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ y, c • f y) (c • f') x :=
by simpa using (hf.const_smul c).has_strict_deriv_at

theorem has_deriv_at_filter.const_smul
  (c : R) (hf : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ y, c • f y) (c • f') x L :=
by simpa using (hf.const_smul c).has_deriv_at_filter

theorem has_deriv_within_at.const_smul
  (c : R) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ y, c • f y) (c • f') s x :=
hf.const_smul c

theorem has_deriv_at.const_smul (c : R) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ y, c • f y) (c • f') x :=
hf.const_smul c

lemma deriv_within_const_smul (hxs : unique_diff_within_at 𝕜 s x)
  (c : R) (hf : differentiable_within_at 𝕜 f s x) :
  deriv_within (λ y, c • f y) s x = c • deriv_within f s x :=
(hf.has_deriv_within_at.const_smul c).deriv_within hxs

lemma deriv_const_smul (c : R) (hf : differentiable_at 𝕜 f x) :
  deriv (λ y, c • f y) x = c • deriv f x :=
(hf.has_deriv_at.const_smul c).deriv

end const_smul

section mul
/-! ### Derivative of the multiplication of two functions -/
variables {𝕜' 𝔸 : Type*} [normed_field 𝕜'] [normed_ring 𝔸] [normed_algebra 𝕜 𝕜']
  [normed_algebra 𝕜 𝔸] {c d : 𝕜 → 𝔸} {c' d' : 𝔸} {u v : 𝕜 → 𝕜'}

theorem has_deriv_within_at.mul
  (hc : has_deriv_within_at c c' s x) (hd : has_deriv_within_at d d' s x) :
  has_deriv_within_at (λ y, c y * d y) (c' * d x + c x * d') s x :=
begin
  have := (has_fderiv_within_at.mul' hc hd).has_deriv_within_at,
  rwa [continuous_linear_map.add_apply, continuous_linear_map.smul_apply,
      continuous_linear_map.smul_right_apply, continuous_linear_map.smul_right_apply,
      continuous_linear_map.smul_right_apply, continuous_linear_map.one_apply,
      one_smul, one_smul, add_comm] at this,
end

theorem has_deriv_at.mul (hc : has_deriv_at c c' x) (hd : has_deriv_at d d' x) :
  has_deriv_at (λ y, c y * d y) (c' * d x + c x * d') x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.mul hd
end

theorem has_strict_deriv_at.mul
  (hc : has_strict_deriv_at c c' x) (hd : has_strict_deriv_at d d' x) :
  has_strict_deriv_at (λ y, c y * d y) (c' * d x + c x * d') x :=
begin
  have := (has_strict_fderiv_at.mul' hc hd).has_strict_deriv_at,
  rwa [continuous_linear_map.add_apply, continuous_linear_map.smul_apply,
      continuous_linear_map.smul_right_apply, continuous_linear_map.smul_right_apply,
      continuous_linear_map.smul_right_apply, continuous_linear_map.one_apply,
      one_smul, one_smul, add_comm] at this,
end

lemma deriv_within_mul (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
  deriv_within (λ y, c y * d y) s x = deriv_within c s x * d x + c x * deriv_within d s x :=
(hc.has_deriv_within_at.mul hd.has_deriv_within_at).deriv_within hxs

@[simp] lemma deriv_mul (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
  deriv (λ y, c y * d y) x = deriv c x * d x + c x * deriv d x :=
(hc.has_deriv_at.mul hd.has_deriv_at).deriv

theorem has_deriv_within_at.mul_const (hc : has_deriv_within_at c c' s x) (d : 𝔸) :
  has_deriv_within_at (λ y, c y * d) (c' * d) s x :=
begin
  convert hc.mul (has_deriv_within_at_const x s d),
  rw [mul_zero, add_zero]
end

theorem has_deriv_at.mul_const (hc : has_deriv_at c c' x) (d : 𝔸) :
  has_deriv_at (λ y, c y * d) (c' * d) x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.mul_const d
end

theorem has_deriv_at_mul_const (c : 𝕜) : has_deriv_at (λ x, x * c) c x :=
by simpa only [one_mul] using (has_deriv_at_id' x).mul_const c

theorem has_strict_deriv_at.mul_const (hc : has_strict_deriv_at c c' x) (d : 𝔸) :
  has_strict_deriv_at (λ y, c y * d) (c' * d) x :=
begin
  convert hc.mul (has_strict_deriv_at_const x d),
  rw [mul_zero, add_zero]
end

lemma deriv_within_mul_const (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (d : 𝔸) :
  deriv_within (λ y, c y * d) s x = deriv_within c s x * d :=
(hc.has_deriv_within_at.mul_const d).deriv_within hxs

lemma deriv_mul_const (hc : differentiable_at 𝕜 c x) (d : 𝔸) :
  deriv (λ y, c y * d) x = deriv c x * d :=
(hc.has_deriv_at.mul_const d).deriv

lemma deriv_mul_const_field (v : 𝕜') :
  deriv (λ y, u y * v) x = deriv u x * v :=
begin
  by_cases hu : differentiable_at 𝕜 u x,
  { exact deriv_mul_const hu v },
  { rw [deriv_zero_of_not_differentiable_at hu, zero_mul],
    rcases eq_or_ne v 0 with rfl|hd,
    { simp only [mul_zero, deriv_const] },
    { refine deriv_zero_of_not_differentiable_at (mt (λ H, _) hu),
      simpa only [mul_inv_cancel_right₀ hd] using H.mul_const v⁻¹ } }
end

@[simp] lemma deriv_mul_const_field' (v : 𝕜') : deriv (λ x, u x * v) = λ x, deriv u x * v :=
funext $ λ _, deriv_mul_const_field v

theorem has_deriv_within_at.const_mul (c : 𝔸) (hd : has_deriv_within_at d d' s x) :
  has_deriv_within_at (λ y, c * d y) (c * d') s x :=
begin
  convert (has_deriv_within_at_const x s c).mul hd,
  rw [zero_mul, zero_add]
end

theorem has_deriv_at.const_mul (c : 𝔸) (hd : has_deriv_at d d' x) :
  has_deriv_at (λ y, c * d y) (c * d') x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hd.const_mul c
end

theorem has_strict_deriv_at.const_mul (c : 𝔸) (hd : has_strict_deriv_at d d' x) :
  has_strict_deriv_at (λ y, c * d y) (c * d') x :=
begin
  convert (has_strict_deriv_at_const _ _).mul hd,
  rw [zero_mul, zero_add]
end

lemma deriv_within_const_mul (hxs : unique_diff_within_at 𝕜 s x)
  (c : 𝔸) (hd : differentiable_within_at 𝕜 d s x) :
  deriv_within (λ y, c * d y) s x = c * deriv_within d s x :=
(hd.has_deriv_within_at.const_mul c).deriv_within hxs

lemma deriv_const_mul (c : 𝔸) (hd : differentiable_at 𝕜 d x) :
  deriv (λ y, c * d y) x = c * deriv d x :=
(hd.has_deriv_at.const_mul c).deriv

lemma deriv_const_mul_field (u : 𝕜') : deriv (λ y, u * v y) x = u * deriv v x :=
by simp only [mul_comm u, deriv_mul_const_field]

@[simp] lemma deriv_const_mul_field' (u : 𝕜') : deriv (λ x, u * v x) = λ x, u * deriv v x :=
funext (λ x, deriv_const_mul_field u)

end mul

section clm_comp_apply
/-! ### Derivative of the pointwise composition/application of continuous linear maps -/

open continuous_linear_map

variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G] {c : 𝕜 → F →L[𝕜] G}
  {c' : F →L[𝕜] G} {d : 𝕜 → E →L[𝕜] F} {d' : E →L[𝕜] F} {u : 𝕜 → F} {u' : F}

lemma has_strict_deriv_at.clm_comp (hc : has_strict_deriv_at c c' x)
  (hd : has_strict_deriv_at d d' x) :
  has_strict_deriv_at (λ y, (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x :=
begin
  have := (hc.has_strict_fderiv_at.clm_comp hd.has_strict_fderiv_at).has_strict_deriv_at,
  rwa [add_apply, comp_apply, comp_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
      one_smul, add_comm] at this,
end

lemma has_deriv_within_at.clm_comp (hc : has_deriv_within_at c c' s x)
  (hd : has_deriv_within_at d d' s x) :
  has_deriv_within_at (λ y, (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') s x :=
begin
  have := (hc.has_fderiv_within_at.clm_comp hd.has_fderiv_within_at).has_deriv_within_at,
  rwa [add_apply, comp_apply, comp_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
      one_smul, add_comm] at this,
end

lemma has_deriv_at.clm_comp (hc : has_deriv_at c c' x) (hd : has_deriv_at d d' x) :
  has_deriv_at (λ y, (c y).comp (d y))
  (c'.comp (d x) + (c x).comp d') x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.clm_comp hd
end

lemma deriv_within_clm_comp (hc : differentiable_within_at 𝕜 c s x)
  (hd : differentiable_within_at 𝕜 d s x) (hxs : unique_diff_within_at 𝕜 s x):
  deriv_within (λ y, (c y).comp (d y)) s x =
    ((deriv_within c s x).comp (d x) + (c x).comp (deriv_within d s x)) :=
(hc.has_deriv_within_at.clm_comp hd.has_deriv_within_at).deriv_within hxs

lemma deriv_clm_comp (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
  deriv (λ y, (c y).comp (d y)) x =
    ((deriv c x).comp (d x) + (c x).comp (deriv d x)) :=
(hc.has_deriv_at.clm_comp hd.has_deriv_at).deriv

lemma has_strict_deriv_at.clm_apply (hc : has_strict_deriv_at c c' x)
  (hu : has_strict_deriv_at u u' x) :
  has_strict_deriv_at (λ y, (c y) (u y)) (c' (u x) + c x u') x :=
begin
  have := (hc.has_strict_fderiv_at.clm_apply hu.has_strict_fderiv_at).has_strict_deriv_at,
  rwa [add_apply, comp_apply, flip_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
      one_smul, add_comm] at this,
end

lemma has_deriv_within_at.clm_apply (hc : has_deriv_within_at c c' s x)
  (hu : has_deriv_within_at u u' s x) :
  has_deriv_within_at (λ y, (c y) (u y)) (c' (u x) + c x u') s x :=
begin
  have := (hc.has_fderiv_within_at.clm_apply hu.has_fderiv_within_at).has_deriv_within_at,
  rwa [add_apply, comp_apply, flip_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
      one_smul, add_comm] at this,
end

lemma has_deriv_at.clm_apply (hc : has_deriv_at c c' x) (hu : has_deriv_at u u' x) :
  has_deriv_at (λ y, (c y) (u y)) (c' (u x) + c x u') x :=
begin
  have := (hc.has_fderiv_at.clm_apply hu.has_fderiv_at).has_deriv_at,
  rwa [add_apply, comp_apply, flip_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
      one_smul, add_comm] at this,
end

lemma deriv_within_clm_apply (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hu : differentiable_within_at 𝕜 u s x) :
  deriv_within (λ y, (c y) (u y)) s x = (deriv_within c s x (u x) + c x (deriv_within u s x)) :=
(hc.has_deriv_within_at.clm_apply hu.has_deriv_within_at).deriv_within hxs

lemma deriv_clm_apply (hc : differentiable_at 𝕜 c x) (hu : differentiable_at 𝕜 u x) :
  deriv (λ y, (c y) (u y)) x = (deriv c x (u x) + c x (deriv u x)) :=
(hc.has_deriv_at.clm_apply hu.has_deriv_at).deriv

end clm_comp_apply

