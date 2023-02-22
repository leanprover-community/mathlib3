/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.deriv
import linear_algebra.affine_space.slope

/-!
# Slope of a differentiable function

Given a function `f : 𝕜 → E` from a nontrivially normed field to a normed space over this field,
`dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b` and as `deriv f a`
for `a = b`.

In this file we define `dslope` and prove some basic lemmas about its continuity and
differentiability.
-/

open_locale classical topology filter
open function set filter

variables {𝕜 E : Type*} [nontrivially_normed_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]

/-- `dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b` and
`deriv f a` for `a = b`. -/
noncomputable def dslope (f : 𝕜 → E) (a : 𝕜) : 𝕜 → E := update (slope f a) a (deriv f a)

@[simp] lemma dslope_same (f : 𝕜 → E) (a : 𝕜) : dslope f a a = deriv f a := update_same _ _ _

variables {f : 𝕜 → E} {a b : 𝕜} {s : set 𝕜}

lemma dslope_of_ne (f : 𝕜 → E) (h : b ≠ a) : dslope f a b = slope f a b :=
update_noteq h _ _

lemma continuous_linear_map.dslope_comp {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  (f : E →L[𝕜] F) (g : 𝕜 → E) (a b : 𝕜) (H : a = b → differentiable_at 𝕜 g a) :
  dslope (f ∘ g) a b = f (dslope g a b) :=
begin
  rcases eq_or_ne b a with rfl|hne,
  { simp only [dslope_same],
    exact (f.has_fderiv_at.comp_has_deriv_at b (H rfl).has_deriv_at).deriv },
  { simpa only [dslope_of_ne _ hne] using f.to_linear_map.slope_comp g a b }
end

lemma eq_on_dslope_slope (f : 𝕜 → E) (a : 𝕜) : eq_on (dslope f a) (slope f a) {a}ᶜ :=
λ b, dslope_of_ne f

lemma dslope_eventually_eq_slope_of_ne (f : 𝕜 → E) (h : b ≠ a) : dslope f a =ᶠ[𝓝 b] slope f a :=
(eq_on_dslope_slope f a).eventually_eq_of_mem (is_open_ne.mem_nhds h)

lemma dslope_eventually_eq_slope_punctured_nhds (f : 𝕜 → E) : dslope f a =ᶠ[𝓝[≠] a] slope f a :=
(eq_on_dslope_slope f a).eventually_eq_of_mem self_mem_nhds_within

@[simp] lemma sub_smul_dslope (f : 𝕜 → E) (a b : 𝕜) : (b - a) • dslope f a b = f b - f a :=
by rcases eq_or_ne b a with rfl | hne; simp [dslope_of_ne, *]

lemma dslope_sub_smul_of_ne (f : 𝕜 → E) (h : b ≠ a) : dslope (λ x, (x - a) • f x) a b = f b :=
by rw [dslope_of_ne _ h, slope_sub_smul _ h.symm]

lemma eq_on_dslope_sub_smul (f : 𝕜 → E) (a : 𝕜) : eq_on (dslope (λ x, (x - a) • f x) a) f {a}ᶜ :=
λ b, dslope_sub_smul_of_ne f

lemma dslope_sub_smul [decidable_eq 𝕜] (f : 𝕜 → E) (a : 𝕜) :
  dslope (λ x, (x - a) • f x) a = update f a (deriv (λ x, (x - a) • f x) a) :=
eq_update_iff.2 ⟨dslope_same _ _, eq_on_dslope_sub_smul f a⟩

@[simp] lemma continuous_at_dslope_same : continuous_at (dslope f a) a ↔ differentiable_at 𝕜 f a :=
by simp only [dslope, continuous_at_update_same, ← has_deriv_at_deriv_iff,
  has_deriv_at_iff_tendsto_slope]

lemma continuous_within_at.of_dslope (h : continuous_within_at (dslope f a) s b) :
  continuous_within_at f s b :=
have continuous_within_at (λ x, (x - a) • dslope f a x + f a) s b,
  from ((continuous_within_at_id.sub continuous_within_at_const).smul h).add
    continuous_within_at_const,
by simpa only [sub_smul_dslope, sub_add_cancel] using this

lemma continuous_at.of_dslope (h : continuous_at (dslope f a) b) : continuous_at f b :=
(continuous_within_at_univ _ _).1 h.continuous_within_at.of_dslope

lemma continuous_on.of_dslope (h : continuous_on (dslope f a) s) : continuous_on f s :=
λ x hx, (h x hx).of_dslope

lemma continuous_within_at_dslope_of_ne (h : b ≠ a) :
  continuous_within_at (dslope f a) s b ↔ continuous_within_at f s b :=
begin
  refine ⟨continuous_within_at.of_dslope, λ hc, _⟩,
  simp only [dslope, continuous_within_at_update_of_ne h],
  exact ((continuous_within_at_id.sub continuous_within_at_const).inv₀
      (sub_ne_zero.2 h)).smul (hc.sub continuous_within_at_const)
end

lemma continuous_at_dslope_of_ne (h : b ≠ a) : continuous_at (dslope f a) b ↔ continuous_at f b :=
by simp only [← continuous_within_at_univ, continuous_within_at_dslope_of_ne h]

lemma continuous_on_dslope (h : s ∈ 𝓝 a) :
  continuous_on (dslope f a) s ↔ continuous_on f s ∧ differentiable_at 𝕜 f a :=
begin
  refine ⟨λ hc, ⟨hc.of_dslope, continuous_at_dslope_same.1 $ hc.continuous_at h⟩, _⟩,
  rintro ⟨hc, hd⟩ x hx,
  rcases eq_or_ne x a with rfl | hne,
  exacts [(continuous_at_dslope_same.2 hd).continuous_within_at,
    (continuous_within_at_dslope_of_ne hne).2 (hc x hx)]
end

lemma differentiable_within_at.of_dslope (h : differentiable_within_at 𝕜 (dslope f a) s b) :
  differentiable_within_at 𝕜 f s b :=
by simpa only [id, sub_smul_dslope f a, sub_add_cancel]
  using ((differentiable_within_at_id.sub_const a).smul h).add_const (f a)

lemma differentiable_at.of_dslope (h : differentiable_at 𝕜 (dslope f a) b) :
  differentiable_at 𝕜 f b :=
differentiable_within_at_univ.1 h.differentiable_within_at.of_dslope

lemma differentiable_on.of_dslope (h : differentiable_on 𝕜 (dslope f a) s) :
  differentiable_on 𝕜 f s :=
λ x hx, (h x hx).of_dslope

lemma differentiable_within_at_dslope_of_ne (h : b ≠ a) :
  differentiable_within_at 𝕜 (dslope f a) s b ↔ differentiable_within_at 𝕜 f s b :=
begin
  refine ⟨differentiable_within_at.of_dslope, λ hd, _⟩,
  refine (((differentiable_within_at_id.sub_const a).inv
    (sub_ne_zero.2 h)).smul (hd.sub_const (f a))).congr_of_eventually_eq _ (dslope_of_ne _ h),
  refine (eq_on_dslope_slope _ _).eventually_eq_of_mem _,
  exact mem_nhds_within_of_mem_nhds (is_open_ne.mem_nhds h)
end

lemma differentiable_on_dslope_of_nmem (h : a ∉ s) :
  differentiable_on 𝕜 (dslope f a) s ↔ differentiable_on 𝕜 f s :=
forall_congr $ λ x, forall_congr $ λ hx, differentiable_within_at_dslope_of_ne $
  ne_of_mem_of_not_mem hx h

lemma differentiable_at_dslope_of_ne (h : b ≠ a) :
  differentiable_at 𝕜 (dslope f a) b ↔ differentiable_at 𝕜 f b :=
by simp only [← differentiable_within_at_univ,
  differentiable_within_at_dslope_of_ne h]
