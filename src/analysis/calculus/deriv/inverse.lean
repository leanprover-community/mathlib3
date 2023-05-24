section inverse
/-! ### Derivative of `x ↦ x⁻¹` -/

theorem has_strict_deriv_at_inv (hx : x ≠ 0) : has_strict_deriv_at has_inv.inv (-(x^2)⁻¹) x :=
begin
  suffices : (λ p : 𝕜 × 𝕜, (p.1 - p.2) * ((x * x)⁻¹ - (p.1 * p.2)⁻¹)) =o[𝓝 (x, x)]
    (λ p, (p.1 - p.2) * 1),
  { refine this.congr' _ (eventually_of_forall $ λ _, mul_one _),
    refine eventually.mono (is_open.mem_nhds (is_open_ne.prod is_open_ne) ⟨hx, hx⟩) _,
    rintro ⟨y, z⟩ ⟨hy, hz⟩,
    simp only [mem_set_of_eq] at hy hz, -- hy : y ≠ 0, hz : z ≠ 0
    field_simp [hx, hy, hz], ring, },
  refine (is_O_refl (λ p : 𝕜 × 𝕜, p.1 - p.2) _).mul_is_o ((is_o_one_iff _).2 _),
  rw [← sub_self (x * x)⁻¹],
  exact tendsto_const_nhds.sub ((continuous_mul.tendsto (x, x)).inv₀ $ mul_ne_zero hx hx)
end

theorem has_deriv_at_inv (x_ne_zero : x ≠ 0) :
  has_deriv_at (λy, y⁻¹) (-(x^2)⁻¹) x :=
(has_strict_deriv_at_inv x_ne_zero).has_deriv_at

theorem has_deriv_within_at_inv (x_ne_zero : x ≠ 0) (s : set 𝕜) :
  has_deriv_within_at (λx, x⁻¹) (-(x^2)⁻¹) s x :=
(has_deriv_at_inv x_ne_zero).has_deriv_within_at

lemma differentiable_at_inv :
  differentiable_at 𝕜 (λx, x⁻¹) x ↔ x ≠ 0:=
⟨λ H, normed_field.continuous_at_inv.1 H.continuous_at,
  λ H, (has_deriv_at_inv H).differentiable_at⟩

lemma differentiable_within_at_inv (x_ne_zero : x ≠ 0) :
  differentiable_within_at 𝕜 (λx, x⁻¹) s x :=
(differentiable_at_inv.2 x_ne_zero).differentiable_within_at

lemma differentiable_on_inv : differentiable_on 𝕜 (λx:𝕜, x⁻¹) {x | x ≠ 0} :=
λx hx, differentiable_within_at_inv hx

lemma deriv_inv : deriv (λx, x⁻¹) x = -(x^2)⁻¹ :=
begin
  rcases eq_or_ne x 0 with rfl|hne,
  { simp [deriv_zero_of_not_differentiable_at (mt differentiable_at_inv.1 (not_not.2 rfl))] },
  { exact (has_deriv_at_inv hne).deriv  }
end

@[simp] lemma deriv_inv' : deriv (λ x : 𝕜, x⁻¹) = λ x, -(x ^ 2)⁻¹ := funext (λ x, deriv_inv)

lemma deriv_within_inv (x_ne_zero : x ≠ 0) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, x⁻¹) s x = -(x^2)⁻¹ :=
begin
  rw differentiable_at.deriv_within (differentiable_at_inv.2 x_ne_zero) hxs,
  exact deriv_inv
end

lemma has_fderiv_at_inv (x_ne_zero : x ≠ 0) :
  has_fderiv_at (λx, x⁻¹) (smul_right (1 : 𝕜 →L[𝕜] 𝕜) (-(x^2)⁻¹) : 𝕜 →L[𝕜] 𝕜) x :=
has_deriv_at_inv x_ne_zero

lemma has_fderiv_within_at_inv (x_ne_zero : x ≠ 0) :
  has_fderiv_within_at (λx, x⁻¹) (smul_right (1 : 𝕜 →L[𝕜] 𝕜) (-(x^2)⁻¹) : 𝕜 →L[𝕜] 𝕜) s x :=
(has_fderiv_at_inv x_ne_zero).has_fderiv_within_at

lemma fderiv_inv :
  fderiv 𝕜 (λx, x⁻¹) x = smul_right (1 : 𝕜 →L[𝕜] 𝕜) (-(x^2)⁻¹) :=
by rw [← deriv_fderiv, deriv_inv]

lemma fderiv_within_inv (x_ne_zero : x ≠ 0) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λx, x⁻¹) s x = smul_right (1 : 𝕜 →L[𝕜] 𝕜) (-(x^2)⁻¹) :=
begin
  rw differentiable_at.fderiv_within (differentiable_at_inv.2 x_ne_zero) hxs,
  exact fderiv_inv
end

variables {c : 𝕜 → 𝕜} {h : E → 𝕜} {c' : 𝕜} {z : E} {S : set E}

lemma has_deriv_within_at.inv
  (hc : has_deriv_within_at c c' s x) (hx : c x ≠ 0) :
  has_deriv_within_at (λ y, (c y)⁻¹) (- c' / (c x)^2) s x :=
begin
  convert (has_deriv_at_inv hx).comp_has_deriv_within_at x hc,
  field_simp
end

lemma has_deriv_at.inv (hc : has_deriv_at c c' x) (hx : c x ≠ 0) :
  has_deriv_at (λ y, (c y)⁻¹) (- c' / (c x)^2) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hc.inv hx
end

lemma differentiable_within_at.inv (hf : differentiable_within_at 𝕜 h S z) (hz : h z ≠ 0) :
  differentiable_within_at 𝕜 (λx, (h x)⁻¹) S z :=
(differentiable_at_inv.mpr hz).comp_differentiable_within_at z hf

@[simp] lemma differentiable_at.inv (hf : differentiable_at 𝕜 h z) (hz : h z ≠ 0) :
  differentiable_at 𝕜 (λx, (h x)⁻¹) z :=
(differentiable_at_inv.mpr hz).comp z hf

lemma differentiable_on.inv (hf : differentiable_on 𝕜 h S) (hz : ∀ x ∈ S, h x ≠ 0) :
  differentiable_on 𝕜 (λx, (h x)⁻¹) S :=
λx h, (hf x h).inv (hz x h)

@[simp] lemma differentiable.inv (hf : differentiable 𝕜 h) (hz : ∀ x, h x ≠ 0) :
  differentiable 𝕜 (λx, (h x)⁻¹) :=
λx, (hf x).inv (hz x)

lemma deriv_within_inv' (hc : differentiable_within_at 𝕜 c s x) (hx : c x ≠ 0)
  (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, (c x)⁻¹) s x = - (deriv_within c s x) / (c x)^2 :=
(hc.has_deriv_within_at.inv hx).deriv_within hxs

@[simp] lemma deriv_inv'' (hc : differentiable_at 𝕜 c x) (hx : c x ≠ 0) :
  deriv (λx, (c x)⁻¹) x = - (deriv c x) / (c x)^2 :=
(hc.has_deriv_at.inv hx).deriv

end inverse

section division
/-! ### Derivative of `x ↦ c x / d x` -/

variables {𝕜' : Type*} [nontrivially_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
  {c d : 𝕜 → 𝕜'} {c' d' : 𝕜'}

lemma has_deriv_within_at.div
  (hc : has_deriv_within_at c c' s x) (hd : has_deriv_within_at d d' s x) (hx : d x ≠ 0) :
  has_deriv_within_at (λ y, c y / d y) ((c' * d x - c x * d') / (d x)^2) s x :=
begin
  convert hc.mul ((has_deriv_at_inv hx).comp_has_deriv_within_at x hd),
  { simp only [div_eq_mul_inv] },
  { field_simp, ring }
end

lemma has_strict_deriv_at.div (hc : has_strict_deriv_at c c' x) (hd : has_strict_deriv_at d d' x)
  (hx : d x ≠ 0) :
  has_strict_deriv_at (λ y, c y / d y) ((c' * d x - c x * d') / (d x)^2) x :=
begin
  convert hc.mul ((has_strict_deriv_at_inv hx).comp x hd),
  { simp only [div_eq_mul_inv] },
  { field_simp, ring }
end

lemma has_deriv_at.div (hc : has_deriv_at c c' x) (hd : has_deriv_at d d' x) (hx : d x ≠ 0) :
  has_deriv_at (λ y, c y / d y) ((c' * d x - c x * d') / (d x)^2) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hc.div hd hx
end

lemma differentiable_within_at.div
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) (hx : d x ≠ 0) :
  differentiable_within_at 𝕜 (λx, c x / d x) s x :=
((hc.has_deriv_within_at).div (hd.has_deriv_within_at) hx).differentiable_within_at

@[simp] lemma differentiable_at.div
  (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) (hx : d x ≠ 0) :
  differentiable_at 𝕜 (λx, c x / d x) x :=
((hc.has_deriv_at).div (hd.has_deriv_at) hx).differentiable_at

lemma differentiable_on.div
  (hc : differentiable_on 𝕜 c s) (hd : differentiable_on 𝕜 d s) (hx : ∀ x ∈ s, d x ≠ 0) :
  differentiable_on 𝕜 (λx, c x / d x) s :=
λx h, (hc x h).div (hd x h) (hx x h)

@[simp] lemma differentiable.div
  (hc : differentiable 𝕜 c) (hd : differentiable 𝕜 d) (hx : ∀ x, d x ≠ 0) :
differentiable 𝕜 (λx, c x / d x) :=
λx, (hc x).div (hd x) (hx x)

lemma deriv_within_div
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) (hx : d x ≠ 0)
  (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, c x / d x) s x
    = ((deriv_within c s x) * d x - c x * (deriv_within d s x)) / (d x)^2 :=
((hc.has_deriv_within_at).div (hd.has_deriv_within_at) hx).deriv_within hxs

@[simp] lemma deriv_div
  (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) (hx : d x ≠ 0) :
  deriv (λx, c x / d x) x = ((deriv c x) * d x - c x * (deriv d x)) / (d x)^2 :=
((hc.has_deriv_at).div (hd.has_deriv_at) hx).deriv

lemma has_deriv_at.div_const (hc : has_deriv_at c c' x) (d : 𝕜') :
  has_deriv_at (λ x, c x / d) (c' / d) x :=
by simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

lemma has_deriv_within_at.div_const (hc : has_deriv_within_at c c' s x) (d : 𝕜') :
  has_deriv_within_at (λ x, c x / d) (c' / d) s x :=
by simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

lemma has_strict_deriv_at.div_const (hc : has_strict_deriv_at c c' x) (d : 𝕜') :
  has_strict_deriv_at (λ x, c x / d) (c' / d) x :=
by simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

lemma differentiable_within_at.div_const (hc : differentiable_within_at 𝕜 c s x) (d : 𝕜') :
  differentiable_within_at 𝕜 (λx, c x / d) s x :=
(hc.has_deriv_within_at.div_const _).differentiable_within_at

@[simp] lemma differentiable_at.div_const (hc : differentiable_at 𝕜 c x) (d : 𝕜') :
  differentiable_at 𝕜 (λ x, c x / d) x :=
(hc.has_deriv_at.div_const _).differentiable_at

lemma differentiable_on.div_const (hc : differentiable_on 𝕜 c s) (d : 𝕜') :
  differentiable_on 𝕜 (λx, c x / d) s :=
λ x hx, (hc x hx).div_const d

@[simp] lemma differentiable.div_const (hc : differentiable 𝕜 c) (d : 𝕜') :
  differentiable 𝕜 (λx, c x / d) :=
λ x, (hc x).div_const d

lemma deriv_within_div_const (hc : differentiable_within_at 𝕜 c s x) (d : 𝕜')
  (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, c x / d) s x = (deriv_within c s x) / d :=
by simp [div_eq_inv_mul, deriv_within_const_mul, hc, hxs]

@[simp] lemma deriv_div_const (d : 𝕜') :
  deriv (λx, c x / d) x = (deriv c x) / d :=
by simp only [div_eq_mul_inv, deriv_mul_const_field]

end division
