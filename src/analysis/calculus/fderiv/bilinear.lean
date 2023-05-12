/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.fderiv.prod

open filter asymptotics continuous_linear_map set metric
open_locale topology classical nnreal filter asymptotics ennreal

noncomputable theory


section

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
variables {G' : Type*} [normed_add_comm_group G'] [normed_space 𝕜 G']

variables {f f₀ f₁ g : E → F}
variables {f' f₀' f₁' g' : E →L[𝕜] F}
variables (e : E →L[𝕜] F)
variables {x : E}
variables {s t : set E}
variables {L L₁ L₂ : filter E}

section bilinear_map
/-! ### Derivative of a bounded bilinear map -/

variables {b : E × F → G} {u : set (E × F)}

open normed_field

lemma is_bounded_bilinear_map.has_strict_fderiv_at (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  has_strict_fderiv_at b (h.deriv p) p :=
begin
  rw has_strict_fderiv_at,
  set T := (E × F) × (E × F),
  have : (λ q : T, b (q.1 - q.2)) =o[𝓝 (p, p)] (λ q : T, ‖q.1 - q.2‖ * 1),
  { refine (h.is_O'.comp_tendsto le_top).trans_is_o _,
    simp only [(∘)],
    refine (is_O_refl (λ q : T, ‖q.1 - q.2‖) _).mul_is_o (is_o.norm_left $ (is_o_one_iff _).2 _),
    rw [← sub_self p],
    exact continuous_at_fst.sub continuous_at_snd },
  simp only [mul_one, is_o_norm_right] at this,
  refine (is_o.congr_of_sub _).1 this, clear this,
  convert_to (λ q : T, h.deriv (p - q.2) (q.1 - q.2)) =o[𝓝 (p, p)] (λ q : T, q.1 - q.2),
  { ext ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩, rcases p with ⟨x, y⟩,
    simp only [is_bounded_bilinear_map_deriv_coe, prod.mk_sub_mk, h.map_sub_left, h.map_sub_right],
    abel },
  have : (λ q : T, p - q.2) =o[𝓝 (p, p)] (λ q, (1:ℝ)),
    from (is_o_one_iff _).2 (sub_self p ▸ tendsto_const_nhds.sub continuous_at_snd),
  apply is_bounded_bilinear_map_apply.is_O_comp.trans_is_o,
  refine is_o.trans_is_O _ (is_O_const_mul_self 1 _ _).of_norm_right,
  refine is_o.mul_is_O _ (is_O_refl _ _),
  exact (((h.is_bounded_linear_map_deriv.is_O_id ⊤).comp_tendsto le_top : _).trans_is_o
    this).norm_left
end

lemma is_bounded_bilinear_map.has_fderiv_at (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  has_fderiv_at b (h.deriv p) p :=
(h.has_strict_fderiv_at p).has_fderiv_at

lemma is_bounded_bilinear_map.has_fderiv_within_at (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  has_fderiv_within_at b (h.deriv p) u p :=
(h.has_fderiv_at p).has_fderiv_within_at

lemma is_bounded_bilinear_map.differentiable_at (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  differentiable_at 𝕜 b p :=
(h.has_fderiv_at p).differentiable_at

lemma is_bounded_bilinear_map.differentiable_within_at (h : is_bounded_bilinear_map 𝕜 b)
  (p : E × F) :
  differentiable_within_at 𝕜 b u p :=
(h.differentiable_at p).differentiable_within_at

lemma is_bounded_bilinear_map.fderiv (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  fderiv 𝕜 b p = h.deriv p :=
has_fderiv_at.fderiv (h.has_fderiv_at p)

lemma is_bounded_bilinear_map.fderiv_within (h : is_bounded_bilinear_map 𝕜 b) (p : E × F)
  (hxs : unique_diff_within_at 𝕜 u p) : fderiv_within 𝕜 b u p = h.deriv p :=
begin
  rw differentiable_at.fderiv_within (h.differentiable_at p) hxs,
  exact h.fderiv p
end

lemma is_bounded_bilinear_map.differentiable (h : is_bounded_bilinear_map 𝕜 b) :
  differentiable 𝕜 b :=
λx, h.differentiable_at x

lemma is_bounded_bilinear_map.differentiable_on (h : is_bounded_bilinear_map 𝕜 b) :
  differentiable_on 𝕜 b u :=
h.differentiable.differentiable_on

variable (B : E →L[𝕜] F →L[𝕜] G)

lemma continuous_linear_map.has_fderiv_within_at_of_bilinear
  {f : G' → E} {g : G' → F} {f' : G' →L[𝕜] E} {g' : G' →L[𝕜] F} {x : G'} {s : set G'}
  (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at g g' s x) :
  has_fderiv_within_at (λ y, B (f y) (g y)) (B.precompR G' (f x) g' + B.precompL G' f' (g x)) s x :=
(B.is_bounded_bilinear_map.has_fderiv_at (f x, g x)).comp_has_fderiv_within_at x (hf.prod hg)

lemma continuous_linear_map.has_fderiv_at_of_bilinear
  {f : G' → E} {g : G' → F} {f' : G' →L[𝕜] E} {g' : G' →L[𝕜] F} {x : G'}
  (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ y, B (f y) (g y)) (B.precompR G' (f x) g' + B.precompL G' f' (g x)) x :=
(B.is_bounded_bilinear_map.has_fderiv_at (f x, g x)).comp x (hf.prod hg)

lemma continuous_linear_map.fderiv_within_of_bilinear
  {f : G' → E} {g : G' → F} {x : G'} {s : set G'}
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x)
  (hs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λ y, B (f y) (g y)) s x =
    (B.precompR G' (f x) (fderiv_within 𝕜 g s x) + B.precompL G' (fderiv_within 𝕜 f s x) (g x)) :=
(B.has_fderiv_within_at_of_bilinear hf.has_fderiv_within_at hg.has_fderiv_within_at).fderiv_within
  hs

lemma continuous_linear_map.fderiv_of_bilinear {f : G' → E} {g : G' → F} {x : G'}
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  fderiv 𝕜 (λ y, B (f y) (g y)) x =
    (B.precompR G' (f x) (fderiv 𝕜 g x) + B.precompL G' (fderiv 𝕜 f x) (g x)) :=
(B.has_fderiv_at_of_bilinear hf.has_fderiv_at hg.has_fderiv_at).fderiv

end bilinear_map

end
