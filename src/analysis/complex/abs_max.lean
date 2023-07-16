/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.complex.cauchy_integral
import analysis.normed_space.completion
import analysis.normed_space.extr
import topology.algebra.order.extr_closure

/-!
# Maximum modulus principle

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove several versions of the maximum modulus principle. There are several
statements that can be called "the maximum modulus principle" for maps between normed complex
spaces. They differ by assumptions on the domain (any space, a nontrivial space, a finite
dimensional space), assumptions on the codomain (any space, a strictly convex space), and by
conclusion (either equality of norms or of the values of the function).

## Main results

### Theorems for any codomain

Consider a function `f : E → F` that is complex differentiable on a set `s`, is continuous on its
closure, and `‖f x‖` has a maximum on `s` at `c`. We prove the following theorems.

- `complex.norm_eq_on_closed_ball_of_is_max_on`: if `s = metric.ball c r`, then `‖f x‖ = ‖f c‖` for
  any `x` from the corresponding closed ball;

- `complex.norm_eq_norm_of_is_max_on_of_ball_subset`: if `metric.ball c (dist w c) ⊆ s`, then
  `‖f w‖ = ‖f c‖`;

- `complex.norm_eq_on_of_is_preconnected_of_is_max_on`: if `U` is an open (pre)connected set, `f` is
  complex differentiable on `U`, and `‖f x‖` has a maximum on `U` at `c ∈ U`, then `‖f x‖ = ‖f c‖`
  for all `x ∈ U`;

- `complex.norm_eq_on_closure_of_is_preconnected_of_is_max_on`: if `s` is open and (pre)connected
  and `c ∈ s`, then `‖f x‖ = ‖f c‖` for all `x ∈ closure s`;

- `complex.norm_eventually_eq_of_is_local_max`: if `f` is complex differentiable in a neighborhood
  of `c` and `‖f x‖` has a local maximum at `c`, then `‖f x‖` is locally a constant in a
  neighborhood of `c`.

### Theorems for a strictly convex codomain

If the codomain `F` is a strictly convex space, then in the lemmas from the previous section we can
prove `f w = f c` instead of `‖f w‖ = ‖f c‖`, see
`complex.eq_on_of_is_preconnected_of_is_max_on_norm`,
`complex.eq_on_closure_of_is_preconnected_of_is_max_on_norm`,
`complex.eq_of_is_max_on_of_ball_subset`, `complex.eq_on_closed_ball_of_is_max_on_norm`, and
`complex.eventually_eq_of_is_local_max_norm`.

### Values on the frontier

Finally, we prove some corollaries that relate the (norm of the) values of a function on a set to
its values on the frontier of the set. All these lemmas assume that `E` is a nontrivial space.  In
this section `f g : E → F` are functions that are complex differentiable on a bounded set `s` and
are continuous on its closure. We prove the following theorems.

- `complex.exists_mem_frontier_is_max_on_norm`: If `E` is a finite dimensional space and `s` is a
  nonempty bounded set, then there exists a point `z ∈ frontier s` such that `λ z, ‖f z‖` takes it
  maximum value on `closure s` at `z`.

- `complex.norm_le_of_forall_mem_frontier_norm_le`: if `‖f z‖ ≤ C` for all `z ∈ frontier s`, then
  `‖f z‖ ≤ C` for all `z ∈ s`; note that this theorem does not require `E` to be a finite
  dimensional space.

- `complex.eq_on_closure_of_eq_on_frontier`: if `f x = g x` on the frontier of `s`, then `f x = g x`
  on `closure s`;

- `complex.eq_on_of_eq_on_frontier`: if `f x = g x` on the frontier of `s`, then `f x = g x`
  on `s`.

## Tags

maximum modulus principle, complex analysis
-/

open topological_space metric set filter asymptotics function measure_theory affine_map
open_locale topology filter nnreal real

universes u v w
variables {E : Type u} [normed_add_comm_group E] [normed_space ℂ E]
  {F : Type v} [normed_add_comm_group F] [normed_space ℂ F]

local postfix `̂`:100 := uniform_space.completion

namespace complex

/-!
### Auxiliary lemmas

We split the proof into a series of lemmas. First we prove the principle for a function `f : ℂ → F`
with an additional assumption that `F` is a complete space, then drop unneeded assumptions one by
one.

The lemmas with names `*_auxₙ` are considered to be private and should not be used outside of this
file.
-/

lemma norm_max_aux₁ [complete_space F] {f : ℂ → F} {z w : ℂ}
  (hd : diff_cont_on_cl ℂ f (ball z (dist w z)))
  (hz : is_max_on (norm ∘ f) (closed_ball z (dist w z)) z) :
  ‖f w‖ = ‖f z‖ :=
begin
  /- Consider a circle of radius `r = dist w z`. -/
  set r : ℝ := dist w z,
  have hw : w ∈ closed_ball z r, from mem_closed_ball.2 le_rfl,
  /- Assume the converse. Since `‖f w‖ ≤ ‖f z‖`, we have `‖f w‖ < ‖f z‖`. -/
  refine (is_max_on_iff.1 hz _ hw).antisymm (not_lt.1 _),
  rintro hw_lt : ‖f w‖ < ‖f z‖,
  have hr : 0 < r, from dist_pos.2 (ne_of_apply_ne (norm ∘ f) hw_lt.ne),
  /- Due to Cauchy integral formula, it suffices to prove the following inequality. -/
  suffices : ‖∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ‖ < 2 * π * ‖f z‖,
  { refine this.ne _,
    have A : ∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ = (2 * π * I : ℂ) • f z :=
      hd.circle_integral_sub_inv_smul (mem_ball_self hr),
    simp [A, norm_smul, real.pi_pos.le] },
  suffices : ‖∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ‖ < 2 * π * r * (‖f z‖ / r),
    by rwa [mul_assoc, mul_div_cancel' _ hr.ne'] at this,
  /- This inequality is true because `‖(ζ - z)⁻¹ • f ζ‖ ≤ ‖f z‖ / r` for all `ζ` on the circle and
  this inequality is strict at `ζ = w`. -/
  have hsub : sphere z r ⊆ closed_ball z r, from sphere_subset_closed_ball,
  refine circle_integral.norm_integral_lt_of_norm_le_const_of_lt hr _ _ ⟨w, rfl, _⟩,
  show continuous_on (λ (ζ : ℂ), (ζ - z)⁻¹ • f ζ) (sphere z r),
  { refine ((continuous_on_id.sub continuous_on_const).inv₀ _).smul
      (hd.continuous_on_ball.mono hsub),
    exact λ ζ hζ, sub_ne_zero.2 (ne_of_mem_sphere hζ hr.ne') },
  show ∀ ζ ∈ sphere z r, ‖(ζ - z)⁻¹ • f ζ‖ ≤ ‖f z‖ / r,
  { rintros ζ (hζ : abs (ζ - z) = r),
    rw [le_div_iff hr, norm_smul, norm_inv, norm_eq_abs, hζ, mul_comm, mul_inv_cancel_left₀ hr.ne'],
    exact hz (hsub hζ) },
  show ‖(w - z)⁻¹ • f w‖ < ‖f z‖ / r,
  { rw [norm_smul, norm_inv, norm_eq_abs, ← div_eq_inv_mul],
    exact (div_lt_div_right hr).2 hw_lt }
end

/-!
Now we drop the assumption `complete_space F` by embedding `F` into its completion.
-/

lemma norm_max_aux₂ {f : ℂ → F} {z w : ℂ} (hd : diff_cont_on_cl ℂ f (ball z (dist w z)))
  (hz : is_max_on (norm ∘ f) (closed_ball z (dist w z)) z) :
  ‖f w‖ = ‖f z‖ :=
begin
  set e : F →L[ℂ] F̂ := uniform_space.completion.to_complL,
  have he : ∀ x, ‖e x‖ = ‖x‖, from uniform_space.completion.norm_coe,
  replace hz : is_max_on (norm ∘ (e ∘ f)) (closed_ball z (dist w z)) z,
    by simpa only [is_max_on, (∘), he] using hz,
  simpa only [he] using norm_max_aux₁ (e.differentiable.comp_diff_cont_on_cl hd) hz
end

/-!
Then we replace the assumption `is_max_on (norm ∘ f) (closed_ball z r) z` with a seemingly weaker
assumption `is_max_on (norm ∘ f) (ball z r) z`.
-/

lemma norm_max_aux₃ {f : ℂ → F} {z w : ℂ} {r : ℝ} (hr : dist w z = r)
  (hd : diff_cont_on_cl ℂ f (ball z r)) (hz : is_max_on (norm ∘ f) (ball z r) z) :
  ‖f w‖ = ‖f z‖ :=
begin
  subst r,
  rcases eq_or_ne w z with rfl|hne, { refl },
  rw ← dist_ne_zero at hne,
  exact norm_max_aux₂ hd (closure_ball z hne ▸ hz.closure hd.continuous_on.norm)
end

/-!
### Maximum modulus principle for any codomain

If we do not assume that the codomain is a strictly convex space, then we can only claim that the
**norm** `‖f x‖` is locally constant.
-/

/-!
Finally, we generalize the theorem from a disk in `ℂ` to a closed ball in any normed space.
-/

/-- **Maximum modulus principle** on a closed ball: if `f : E → F` is continuous on a closed ball,
is complex differentiable on the corresponding open ball, and the norm `‖f w‖` takes its maximum
value on the open ball at its center, then the norm `‖f w‖` is constant on the closed ball.  -/
lemma norm_eq_on_closed_ball_of_is_max_on {f : E → F} {z : E} {r : ℝ}
  (hd : diff_cont_on_cl ℂ f (ball z r)) (hz : is_max_on (norm ∘ f) (ball z r) z) :
  eq_on (norm ∘ f) (const E ‖f z‖) (closed_ball z r) :=
begin
  intros w hw,
  rw [mem_closed_ball, dist_comm] at hw,
  rcases eq_or_ne z w with rfl|hne, { refl },
  set e : ℂ → E := line_map z w,
  have hde : differentiable ℂ e := (differentiable_id.smul_const (w - z)).add_const z,
  suffices : ‖(f ∘ e) (1 : ℂ)‖ = ‖(f ∘ e) (0 : ℂ)‖, by simpa [e],
  have hr : dist (1 : ℂ) 0 = 1, by simp,
  have hball : maps_to e (ball 0 1) (ball z r),
  { refine ((lipschitz_with_line_map z w).maps_to_ball
      (mt nndist_eq_zero.1 hne) 0 1).mono subset.rfl _,
    simpa only [line_map_apply_zero, mul_one, coe_nndist] using ball_subset_ball hw },
  exact norm_max_aux₃ hr (hd.comp hde.diff_cont_on_cl hball)
    (hz.comp_maps_to hball (line_map_apply_zero z w))
end

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a set `s`, the norm
of `f` takes it maximum on `s` at `z`, and `w` is a point such that the closed ball with center `z`
and radius `dist w z` is included in `s`, then `‖f w‖ = ‖f z‖`. -/
lemma norm_eq_norm_of_is_max_on_of_ball_subset {f : E → F} {s : set E} {z w : E}
  (hd : diff_cont_on_cl ℂ f s) (hz : is_max_on (norm ∘ f) s z) (hsub : ball z (dist w z) ⊆ s) :
  ‖f w‖ = ‖f z‖ :=
norm_eq_on_closed_ball_of_is_max_on (hd.mono hsub) (hz.on_subset hsub) (mem_closed_ball.2 le_rfl)

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable in a neighborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `‖f z‖` is locally constant in a neighborhood
of `c`. -/
lemma norm_eventually_eq_of_is_local_max {f : E → F} {c : E}
  (hd : ∀ᶠ z in 𝓝 c, differentiable_at ℂ f z) (hc : is_local_max (norm ∘ f) c) :
  ∀ᶠ y in 𝓝 c, ‖f y‖ = ‖f c‖ :=
begin
  rcases nhds_basis_closed_ball.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩,
  exact nhds_basis_closed_ball.eventually_iff.2 ⟨r, hr₀, norm_eq_on_closed_ball_of_is_max_on
    (differentiable_on.diff_cont_on_cl $
      λ x hx, (hr $ closure_ball_subset_closed_ball hx).1.differentiable_within_at)
    (λ x hx, (hr $ ball_subset_closed_ball hx).2)⟩
end

lemma is_open_set_of_mem_nhds_and_is_max_on_norm {f : E → F} {s : set E}
  (hd : differentiable_on ℂ f s) :
  is_open {z | s ∈ 𝓝 z ∧ is_max_on (norm ∘ f) s z} :=
begin
  refine is_open_iff_mem_nhds.2 (λ z hz, (eventually_eventually_nhds.2 hz.1).and _),
  replace hd : ∀ᶠ w in 𝓝 z, differentiable_at ℂ f w, from hd.eventually_differentiable_at hz.1,
  exact (norm_eventually_eq_of_is_local_max hd $ (hz.2.is_local_max hz.1)).mono
    (λ x hx y hy, le_trans (hz.2 hy) hx.ge)
end

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space. Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `‖f x‖ = ‖f c‖` for all `x ∈ U`. -/
lemma norm_eq_on_of_is_preconnected_of_is_max_on {f : E → F} {U : set E} {c : E}
  (hc : is_preconnected U) (ho : is_open U) (hd : differentiable_on ℂ f U) (hcU : c ∈ U)
  (hm : is_max_on (norm ∘ f) U c) :
  eq_on (norm ∘ f) (const E ‖f c‖) U :=
begin
  set V := U ∩ {z | is_max_on (norm ∘ f) U z},
  have hV : ∀ x ∈ V, ‖f x‖ = ‖f c‖, from λ x hx, le_antisymm (hm hx.1) (hx.2 hcU),
  suffices : U ⊆ V, from λ x hx, hV x (this hx),
  have hVo : is_open V,
  { simpa only [ho.mem_nhds_iff, set_of_and, set_of_mem_eq]
      using is_open_set_of_mem_nhds_and_is_max_on_norm hd },
  have hVne : (U ∩ V).nonempty := ⟨c, hcU, hcU, hm⟩,
  set W := U ∩ {z | ‖f z‖ ≠ ‖f c‖},
  have hWo : is_open W, from hd.continuous_on.norm.preimage_open_of_open ho is_open_ne,
  have hdVW : disjoint V W, from disjoint_left.mpr (λ x hxV hxW, hxW.2 (hV x hxV)),
  have hUVW : U ⊆ V ∪ W,
    from λ x hx, (eq_or_ne (‖f x‖) (‖f c‖)).imp (λ h, ⟨hx, λ y hy, (hm hy).out.trans_eq h.symm⟩)
      (and.intro hx),
  exact hc.subset_left_of_subset_union hVo hWo hdVW hUVW hVne,
end

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U` and is
continuous on its closure. Suppose that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then
`‖f x‖ = ‖f c‖` for all `x ∈ closure U`. -/
lemma norm_eq_on_closure_of_is_preconnected_of_is_max_on {f : E → F} {U : set E} {c : E}
  (hc : is_preconnected U) (ho : is_open U) (hd : diff_cont_on_cl ℂ f U) (hcU : c ∈ U)
  (hm : is_max_on (norm ∘ f) U c) :
  eq_on (norm ∘ f) (const E ‖f c‖) (closure U) :=
(norm_eq_on_of_is_preconnected_of_is_max_on hc ho hd.differentiable_on hcU hm).of_subset_closure
  hd.continuous_on.norm continuous_on_const subset_closure subset.rfl

section strict_convex

/-!
### The case of a strictly convex codomain

If the codomain `F` is a strictly convex space, then we can claim equalities like `f w = f z`
instead of `‖f w‖ = ‖f z‖`.

Instead of repeating the proof starting with lemmas about integrals, we apply a corresponding lemma
above twice: for `f` and for `λ x, f x + f c`.  Then we have `‖f w‖ = ‖f z‖` and
`‖f w + f z‖ = ‖f z + f z‖`, thus `‖f w + f z‖ = ‖f w‖ + ‖f z‖`. This is only possible if
`f w = f z`, see `eq_of_norm_eq_of_norm_add_eq`.
-/

variables [strict_convex_space ℝ F]

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `f x = f c` for all `x ∈ U`.

TODO: change assumption from `is_max_on` to `is_local_max`. -/
lemma eq_on_of_is_preconnected_of_is_max_on_norm {f : E → F} {U : set E} {c : E}
  (hc : is_preconnected U) (ho : is_open U) (hd : differentiable_on ℂ f U) (hcU : c ∈ U)
  (hm : is_max_on (norm ∘ f) U c) :
  eq_on f (const E (f c)) U :=
λ x hx,
have H₁ : ‖f x‖ = ‖f c‖, from norm_eq_on_of_is_preconnected_of_is_max_on hc ho hd hcU hm hx,
have H₂ : ‖f x + f c‖ = ‖f c + f c‖,
  from norm_eq_on_of_is_preconnected_of_is_max_on hc ho (hd.add_const _) hcU hm.norm_add_self hx,
eq_of_norm_eq_of_norm_add_eq H₁ $ by simp only [H₂, same_ray.rfl.norm_add, H₁]

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U` and is
continuous on its closure. Suppose that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then
`f x = f c` for all `x ∈ closure U`. -/
lemma eq_on_closure_of_is_preconnected_of_is_max_on_norm {f : E → F} {U : set E} {c : E}
  (hc : is_preconnected U) (ho : is_open U) (hd : diff_cont_on_cl ℂ f U) (hcU : c ∈ U)
  (hm : is_max_on (norm ∘ f) U c) :
  eq_on f (const E (f c)) (closure U) :=
(eq_on_of_is_preconnected_of_is_max_on_norm hc ho hd.differentiable_on hcU hm).of_subset_closure
  hd.continuous_on continuous_on_const subset_closure subset.rfl

/-- **Maximum modulus principle**. Let `f : E → F` be a function between complex normed spaces.
Suppose that the codomain `F` is a strictly convex space, `f` is complex differentiable on a set
`s`, `f` is continuous on the closure of `s`, the norm of `f` takes it maximum on `s` at `z`, and
`w` is a point such that the closed ball with center `z` and radius `dist w z` is included in `s`,
then `f w = f z`. -/
lemma eq_of_is_max_on_of_ball_subset {f : E → F} {s : set E} {z w : E} (hd : diff_cont_on_cl ℂ f s)
  (hz : is_max_on (norm ∘ f) s z) (hsub : ball z (dist w z) ⊆ s) :
  f w = f z :=
have H₁ : ‖f w‖ = ‖f z‖, from norm_eq_norm_of_is_max_on_of_ball_subset hd hz hsub,
have H₂ : ‖f w + f z‖ = ‖f z + f z‖,
  from norm_eq_norm_of_is_max_on_of_ball_subset (hd.add_const _) hz.norm_add_self hsub,
eq_of_norm_eq_of_norm_add_eq H₁ $ by simp only [H₂, same_ray.rfl.norm_add, H₁]

/-- **Maximum modulus principle** on a closed ball. Suppose that a function `f : E → F` from a
normed complex space to a strictly convex normed complex space has the following properties:

- it is continuous on a closed ball `metric.closed_ball z r`,
- it is complex differentiable on the corresponding open ball;
- the norm `‖f w‖` takes its maximum value on the open ball at its center.

Then `f` is a constant on the closed ball.  -/
lemma eq_on_closed_ball_of_is_max_on_norm {f : E → F} {z : E} {r : ℝ}
  (hd : diff_cont_on_cl ℂ f (ball z r)) (hz : is_max_on (norm ∘ f) (ball z r) z) :
  eq_on f (const E (f z)) (closed_ball z r) :=
λ x hx, eq_of_is_max_on_of_ball_subset hd hz $ ball_subset_ball hx

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable in a neighborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `f` is locally constant in a neighborhood
of `c`. -/
lemma eventually_eq_of_is_local_max_norm {f : E → F} {c : E}
  (hd : ∀ᶠ z in 𝓝 c, differentiable_at ℂ f z) (hc : is_local_max (norm ∘ f) c) :
  ∀ᶠ y in 𝓝 c, f y = f c :=
begin
  rcases nhds_basis_closed_ball.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩,
  exact nhds_basis_closed_ball.eventually_iff.2 ⟨r, hr₀, eq_on_closed_ball_of_is_max_on_norm
    (differentiable_on.diff_cont_on_cl $
      λ x hx, (hr $ closure_ball_subset_closed_ball hx).1.differentiable_within_at)
    (λ x hx, (hr $ ball_subset_closed_ball hx).2)⟩
end

lemma eventually_eq_or_eq_zero_of_is_local_min_norm {f : E → ℂ} {c : E}
  (hf : ∀ᶠ z in 𝓝 c, differentiable_at ℂ f z) (hc : is_local_min (norm ∘ f) c) :
  (∀ᶠ z in 𝓝 c, f z = f c) ∨ (f c = 0) :=
begin
  refine or_iff_not_imp_right.mpr (λ h, _),
  have h1 : ∀ᶠ z in 𝓝 c, f z ≠ 0 := hf.self_of_nhds.continuous_at.eventually_ne h,
  have h2 : is_local_max (norm ∘ f)⁻¹ c := hc.inv (h1.mono (λ z, norm_pos_iff.mpr)),
  have h3 : is_local_max (norm ∘ f⁻¹) c := by { refine h2.congr (eventually_of_forall _); simp },
  have h4 : ∀ᶠ z in 𝓝 c, differentiable_at ℂ f⁻¹ z, by filter_upwards [hf, h1] with z h using h.inv,
  filter_upwards [eventually_eq_of_is_local_max_norm h4 h3] with z using inv_inj.mp
end

end strict_convex

/-!
### Maximum on a set vs maximum on its frontier

In this section we prove corollaries of the maximum modulus principle that relate the values of a
function on a set to its values on the frontier of this set.
-/

variable [nontrivial E]

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a nonempty bounded
set `U` and is continuous on its closure, then there exists a point `z ∈ frontier U` such that
`λ z, ‖f z‖` takes it maximum value on `closure U` at `z`. -/
lemma exists_mem_frontier_is_max_on_norm [finite_dimensional ℂ E] {f : E → F} {U : set E}
  (hb : bounded U) (hne : U.nonempty) (hd : diff_cont_on_cl ℂ f U) :
  ∃ z ∈ frontier U, is_max_on (norm ∘ f) (closure U) z :=
begin
  have hc : is_compact (closure U), from hb.is_compact_closure,
  obtain ⟨w, hwU, hle⟩ : ∃ w ∈ closure U, is_max_on (norm ∘ f) (closure U) w,
    from hc.exists_forall_ge hne.closure hd.continuous_on.norm,
  rw [closure_eq_interior_union_frontier, mem_union] at hwU,
  cases hwU, rotate, { exact ⟨w, hwU, hle⟩ },
  have : interior U ≠ univ, from ne_top_of_le_ne_top hc.ne_univ interior_subset_closure,
  rcases exists_mem_frontier_inf_dist_compl_eq_dist hwU this with ⟨z, hzU, hzw⟩,
  refine ⟨z, frontier_interior_subset hzU, λ x hx, (mem_set_of_eq.mp $ hle hx).trans_eq _⟩,
  refine (norm_eq_norm_of_is_max_on_of_ball_subset hd (hle.on_subset subset_closure) _).symm,
  rw [dist_comm, ← hzw],
  exact ball_inf_dist_compl_subset.trans interior_subset
end

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a bounded set `U` and
`‖f z‖ ≤ C` for any `z ∈ frontier U`, then the same is true for any `z ∈ closure U`. -/
lemma norm_le_of_forall_mem_frontier_norm_le {f : E → F} {U : set E} (hU : bounded U)
  (hd : diff_cont_on_cl ℂ f U) {C : ℝ} (hC : ∀ z ∈ frontier U, ‖f z‖ ≤ C)
  {z : E} (hz : z ∈ closure U) :
  ‖f z‖ ≤ C :=
begin
  rw [closure_eq_self_union_frontier, union_comm, mem_union] at hz,
  cases hz, { exact hC z hz },
  /- In case of a finite dimensional domain, one can just apply
  `complex.exists_mem_frontier_is_max_on_norm`. To make it work in any Banach space, we restrict
  the function to a line first. -/
  rcases exists_ne z with ⟨w, hne⟩,
  set e : ℂ → E := line_map z w,
  have hde : differentiable ℂ e := (differentiable_id.smul_const (w - z)).add_const z,
  have hL : antilipschitz_with (nndist z w)⁻¹ e, from antilipschitz_with_line_map hne.symm,
  replace hd : diff_cont_on_cl ℂ (f ∘ e) (e ⁻¹' U),
    from hd.comp hde.diff_cont_on_cl (maps_to_preimage _ _),
  have h₀ : (0 : ℂ) ∈ e ⁻¹' U, by simpa only [e, mem_preimage, line_map_apply_zero],
  rcases exists_mem_frontier_is_max_on_norm (hL.bounded_preimage hU) ⟨0, h₀⟩ hd with ⟨ζ, hζU, hζ⟩,
  calc ‖f z‖ = ‖f (e 0)‖ : by simp only [e, line_map_apply_zero]
  ... ≤ ‖f (e ζ)‖ : hζ (subset_closure h₀)
  ... ≤ C : hC _ (hde.continuous.frontier_preimage_subset _ hζU)
end

/-- If two complex differentiable functions `f g : E → F` are equal on the boundary of a bounded set
`U`, then they are equal on `closure U`. -/
lemma eq_on_closure_of_eq_on_frontier {f g : E → F} {U : set E} (hU : bounded U)
  (hf : diff_cont_on_cl ℂ f U) (hg : diff_cont_on_cl ℂ g U) (hfg : eq_on f g (frontier U)) :
  eq_on f g (closure U) :=
begin
  suffices H : ∀ z ∈ closure U, ‖(f - g) z‖ ≤ 0, by simpa [sub_eq_zero] using H,
  refine λ z hz, norm_le_of_forall_mem_frontier_norm_le hU (hf.sub hg) (λ w hw, _) hz,
  simp [hfg hw]
end

/-- If two complex differentiable functions `f g : E → F` are equal on the boundary of a bounded set
`U`, then they are equal on `U`. -/
lemma eq_on_of_eq_on_frontier {f g : E → F} {U : set E} (hU : bounded U)
  (hf : diff_cont_on_cl ℂ f U) (hg : diff_cont_on_cl ℂ g U) (hfg : eq_on f g (frontier U)) :
  eq_on f g U :=
(eq_on_closure_of_eq_on_frontier hU hf hg hfg).mono subset_closure

end complex
