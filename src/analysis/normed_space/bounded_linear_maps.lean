/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import analysis.normed_space.multilinear
import analysis.normed_space.units
import analysis.asymptotics.asymptotics

/-!
# Bounded linear maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a class stating that a map between normed vector spaces is (bi)linear and
continuous.
Instead of asking for continuity, the definition takes the equivalent condition (because the space
is normed) that `‖f x‖` is bounded by a multiple of `‖x‖`. Hence the "bounded" in the name refers to
`‖f x‖/‖x‖` rather than `‖f x‖` itself.

## Main definitions

* `is_bounded_linear_map`: Class stating that a map `f : E → F` is linear and has `‖f x‖` bounded
  by a multiple of `‖x‖`.
* `is_bounded_bilinear_map`: Class stating that a map `f : E × F → G` is bilinear and continuous,
  but through the simpler to provide statement that `‖f (x, y)‖` is bounded by a multiple of
  `‖x‖ * ‖y‖`
* `is_bounded_bilinear_map.linear_deriv`: Derivative of a continuous bilinear map as a linear map.
* `is_bounded_bilinear_map.deriv`: Derivative of a continuous bilinear map as a continuous linear
  map. The proof that it is indeed the derivative is `is_bounded_bilinear_map.has_fderiv_at` in
  `analysis.calculus.fderiv`.

## Main theorems

* `is_bounded_bilinear_map.continuous`: A bounded bilinear map is continuous.
* `continuous_linear_equiv.is_open`: The continuous linear equivalences are an open subset of the
  set of continuous linear maps between a pair of Banach spaces.  Placed in this file because its
  proof uses `is_bounded_bilinear_map.continuous`.

## Notes

The main use of this file is `is_bounded_bilinear_map`. The file `analysis.normed_space.multilinear`
already expounds the theory of multilinear maps, but the `2`-variables case is sufficiently simpler
to currently deserve its own treatment.

`is_bounded_linear_map` is effectively an unbundled version of `continuous_linear_map` (defined
in `topology.algebra.module.basic`, theory over normed spaces developed in
`analysis.normed_space.operator_norm`), albeit the name disparity. A bundled
`continuous_linear_map` is to be preferred over a `is_bounded_linear_map` hypothesis. Historical
artifact, really.
-/

noncomputable theory
open_locale big_operators topology

open filter (tendsto) metric continuous_linear_map

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
          {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
          {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
          {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]

/-- A function `f` satisfies `is_bounded_linear_map 𝕜 f` if it is linear and satisfies the
inequality `‖f x‖ ≤ M * ‖x‖` for some positive constant `M`. -/
structure is_bounded_linear_map (𝕜 : Type*) [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F] (f : E → F)
  extends is_linear_map 𝕜 f : Prop :=
(bound : ∃ M, 0 < M ∧ ∀ x : E, ‖f x‖ ≤ M * ‖x‖)

lemma is_linear_map.with_bound
  {f : E → F} (hf : is_linear_map 𝕜 f) (M : ℝ) (h : ∀ x : E, ‖f x‖ ≤ M * ‖x‖) :
  is_bounded_linear_map 𝕜 f :=
⟨ hf, classical.by_cases
  (assume : M ≤ 0, ⟨1, zero_lt_one, λ x,
    (h x).trans $ mul_le_mul_of_nonneg_right (this.trans zero_le_one) (norm_nonneg x)⟩)
  (assume : ¬ M ≤ 0, ⟨M, lt_of_not_ge this, h⟩)⟩

/-- A continuous linear map satisfies `is_bounded_linear_map` -/
lemma continuous_linear_map.is_bounded_linear_map (f : E →L[𝕜] F) : is_bounded_linear_map 𝕜 f :=
{ bound := f.bound,
  ..f.to_linear_map.is_linear }

namespace is_bounded_linear_map

/-- Construct a linear map from a function `f` satisfying `is_bounded_linear_map 𝕜 f`. -/
def to_linear_map (f : E → F) (h : is_bounded_linear_map 𝕜 f) : E →ₗ[𝕜] F :=
(is_linear_map.mk' _ h.to_is_linear_map)

/-- Construct a continuous linear map from is_bounded_linear_map -/
def to_continuous_linear_map {f : E → F} (hf : is_bounded_linear_map 𝕜 f) : E →L[𝕜] F :=
{ cont := let ⟨C, Cpos, hC⟩ :=
    hf.bound in add_monoid_hom_class.continuous_of_bound (to_linear_map f hf) C hC,
  ..to_linear_map f hf}

lemma zero : is_bounded_linear_map 𝕜 (λ (x:E), (0:F)) :=
(0 : E →ₗ[𝕜] F).is_linear.with_bound 0 $ by simp [le_refl]

lemma id : is_bounded_linear_map 𝕜 (λ (x:E), x) :=
linear_map.id.is_linear.with_bound 1 $ by simp [le_refl]

lemma fst : is_bounded_linear_map 𝕜 (λ x : E × F, x.1) :=
begin
  refine (linear_map.fst 𝕜 E F).is_linear.with_bound 1 (λ x, _),
  rw one_mul,
  exact le_max_left _ _
end

lemma snd : is_bounded_linear_map 𝕜 (λ x : E × F, x.2) :=
begin
  refine (linear_map.snd 𝕜 E F).is_linear.with_bound 1 (λ x, _),
  rw one_mul,
  exact le_max_right _ _
end

variables {f g : E → F}

lemma smul (c : 𝕜) (hf : is_bounded_linear_map 𝕜 f) :
  is_bounded_linear_map 𝕜 (c • f) :=
let ⟨hlf, M, hMp, hM⟩ := hf in
(c • hlf.mk' f).is_linear.with_bound (‖c‖ * M) $ λ x,
  calc ‖c • f x‖ = ‖c‖ * ‖f x‖ : norm_smul c (f x)
  ... ≤ ‖c‖ * (M * ‖x‖)        : mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  ... = (‖c‖ * M) * ‖x‖        : (mul_assoc _ _ _).symm

lemma neg (hf : is_bounded_linear_map 𝕜 f) :
  is_bounded_linear_map 𝕜 (λ e, -f e) :=
begin
  rw show (λ e, -f e) = (λ e, (-1 : 𝕜) • f e), { funext, simp },
  exact smul (-1) hf
end

lemma add (hf : is_bounded_linear_map 𝕜 f) (hg : is_bounded_linear_map 𝕜 g) :
  is_bounded_linear_map 𝕜 (λ e, f e + g e) :=
let ⟨hlf, Mf, hMfp, hMf⟩ := hf in
let ⟨hlg, Mg, hMgp, hMg⟩ := hg in
(hlf.mk' _ + hlg.mk' _).is_linear.with_bound (Mf + Mg) $ λ x,
  calc ‖f x + g x‖ ≤ Mf * ‖x‖ + Mg * ‖x‖ : norm_add_le_of_le (hMf x) (hMg x)
               ... ≤ (Mf + Mg) * ‖x‖     : by rw add_mul

lemma sub (hf : is_bounded_linear_map 𝕜 f) (hg : is_bounded_linear_map 𝕜 g) :
  is_bounded_linear_map 𝕜 (λ e, f e - g e) :=
by simpa [sub_eq_add_neg] using add hf (neg hg)

lemma comp {g : F → G}
  (hg : is_bounded_linear_map 𝕜 g) (hf : is_bounded_linear_map 𝕜 f) :
  is_bounded_linear_map 𝕜 (g ∘ f) :=
(hg.to_continuous_linear_map.comp hf.to_continuous_linear_map).is_bounded_linear_map

protected lemma tendsto (x : E) (hf : is_bounded_linear_map 𝕜 f) :
  tendsto f (𝓝 x) (𝓝 (f x)) :=
let ⟨hf, M, hMp, hM⟩ := hf in
tendsto_iff_norm_tendsto_zero.2 $
  squeeze_zero (λ e, norm_nonneg _)
    (λ e,
      calc ‖f e - f x‖ = ‖hf.mk' f (e - x)‖ : by rw (hf.mk' _).map_sub e x; refl
                   ... ≤ M * ‖e - x‖        : hM (e - x))
    (suffices tendsto (λ (e : E), M * ‖e - x‖) (𝓝 x) (𝓝 (M * 0)), by simpa,
      tendsto_const_nhds.mul (tendsto_norm_sub_self _))

lemma continuous (hf : is_bounded_linear_map 𝕜 f) : continuous f :=
continuous_iff_continuous_at.2 $ λ _, hf.tendsto _

lemma lim_zero_bounded_linear_map (hf : is_bounded_linear_map 𝕜 f) :
  tendsto f (𝓝 0) (𝓝 0) :=
(hf.1.mk' _).map_zero ▸ continuous_iff_continuous_at.1 hf.continuous 0

section
open asymptotics filter

theorem is_O_id {f : E → F} (h : is_bounded_linear_map 𝕜 f) (l : filter E) :
  f =O[l] (λ x, x) :=
let ⟨M, hMp, hM⟩ := h.bound in is_O.of_bound _ (mem_of_superset univ_mem (λ x _, hM x))

theorem is_O_comp {E : Type*} {g : F → G} (hg : is_bounded_linear_map 𝕜 g)
  {f : E → F} (l : filter E) : (λ x', g (f x')) =O[l] f :=
(hg.is_O_id ⊤).comp_tendsto le_top

theorem is_O_sub {f : E → F} (h : is_bounded_linear_map 𝕜 f)
  (l : filter E) (x : E) : (λ x', f (x' - x)) =O[l] (λ x', x' - x) :=
is_O_comp h l

end

end is_bounded_linear_map

section
variables {ι : Type*} [fintype ι]

/-- Taking the cartesian product of two continuous multilinear maps
is a bounded linear operation. -/
lemma is_bounded_linear_map_prod_multilinear
  {E : ι → Type*} [∀ i, normed_add_comm_group (E i)] [∀ i, normed_space 𝕜 (E i)] :
  is_bounded_linear_map 𝕜
  (λ p : (continuous_multilinear_map 𝕜 E F) × (continuous_multilinear_map 𝕜 E G), p.1.prod p.2) :=
{ map_add := λ p₁ p₂, by { ext1 m, refl },
  map_smul := λ c p, by { ext1 m, refl },
  bound := ⟨1, zero_lt_one, λ p, begin
    rw one_mul,
    apply continuous_multilinear_map.op_norm_le_bound _ (norm_nonneg _) (λ m, _),
    rw [continuous_multilinear_map.prod_apply, norm_prod_le_iff],
    split,
    { exact (p.1.le_op_norm m).trans
        (mul_le_mul_of_nonneg_right (norm_fst_le p) (finset.prod_nonneg (λ i hi, norm_nonneg _))) },
    { exact (p.2.le_op_norm m).trans
        (mul_le_mul_of_nonneg_right (norm_snd_le p) (finset.prod_nonneg (λ i hi, norm_nonneg _))) },
  end⟩ }

/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g m₁, ..., g mₙ)` is a bounded linear operation. -/
lemma is_bounded_linear_map_continuous_multilinear_map_comp_linear (g : G →L[𝕜] E) :
  is_bounded_linear_map 𝕜 (λ f : continuous_multilinear_map 𝕜 (λ (i : ι), E) F,
    f.comp_continuous_linear_map (λ _, g)) :=
begin
  refine is_linear_map.with_bound ⟨λ f₁ f₂, by { ext m, refl }, λ c f, by { ext m, refl }⟩
    (‖g‖ ^ (fintype.card ι)) (λ f, _),
  apply continuous_multilinear_map.op_norm_le_bound _ _ (λ m, _),
  { apply_rules [mul_nonneg, pow_nonneg, norm_nonneg] },
  calc ‖f (g ∘ m)‖ ≤
    ‖f‖ * ∏ i, ‖g (m i)‖ : f.le_op_norm _
    ... ≤ ‖f‖ * ∏ i, (‖g‖ * ‖m i‖) : begin
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
      exact finset.prod_le_prod (λ i hi, norm_nonneg _) (λ i hi, g.le_op_norm _)
    end
    ... = ‖g‖ ^ fintype.card ι * ‖f‖ * ∏ i, ‖m i‖ :
      by { simp [finset.prod_mul_distrib, finset.card_univ], ring }
end

end

section bilinear_map

namespace continuous_linear_map

/-! We prove some computation rules for continuous (semi-)bilinear maps in their first argument.
  If `f` is a continuuous bilinear map, to use the corresponding rules for the second argument, use
  `(f _).map_add` and similar.

We have to assume that `F` and `G` are normed spaces in this section, to use
`continuous_linear_map.to_normed_add_comm_group`, but we don't need to assume this for the first
argument of `f`.
-/

variables {R : Type*}
variables {𝕜₂ 𝕜' : Type*} [nontrivially_normed_field 𝕜'] [nontrivially_normed_field 𝕜₂]
variables {M : Type*} [topological_space M]
variables {σ₁₂ : 𝕜 →+* 𝕜₂}
variables {G' : Type*} [normed_add_comm_group G'] [normed_space 𝕜₂ G'] [normed_space 𝕜' G']
variables [smul_comm_class 𝕜₂ 𝕜' G']

section semiring
variables [semiring R] [add_comm_monoid M] [module R M] {ρ₁₂ : R →+* 𝕜'}

lemma map_add₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (x x' : M) (y : F) :
  f (x + x') y = f x y + f x' y :=
by rw [f.map_add, add_apply]

lemma map_zero₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (y : F) : f 0 y = 0 :=
by rw [f.map_zero, zero_apply]

lemma map_smulₛₗ₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (c : R) (x : M) (y : F) :
  f (c • x) y = ρ₁₂ c • f x y :=
by rw [f.map_smulₛₗ, smul_apply]
end semiring

section ring

variables [ring R] [add_comm_group M] [module R M] {ρ₁₂ : R →+* 𝕜'}

lemma map_sub₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (x x' : M) (y : F) :
  f (x - x') y = f x y - f x' y :=
by rw [f.map_sub, sub_apply]

lemma map_neg₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (x : M) (y : F) : f (- x) y = - f x y :=
by rw [f.map_neg, neg_apply]

end ring

lemma map_smul₂ (f : E →L[𝕜] F →L[𝕜] G) (c : 𝕜) (x : E) (y : F) : f (c • x) y = c • f x y :=
by rw [f.map_smul, smul_apply]

end continuous_linear_map

variable (𝕜)

/-- A map `f : E × F → G` satisfies `is_bounded_bilinear_map 𝕜 f` if it is bilinear and
continuous. -/
structure is_bounded_bilinear_map (f : E × F → G) : Prop :=
(add_left   : ∀ (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y))
(smul_left  : ∀ (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y))
(add_right  : ∀ (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂))
(smul_right : ∀ (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x,y))
(bound      : ∃ C > 0, ∀ (x : E) (y : F), ‖f (x, y)‖ ≤ C * ‖x‖ * ‖y‖)

variable {𝕜}
variable {f : E × F → G}

lemma continuous_linear_map.is_bounded_bilinear_map (f : E →L[𝕜] F →L[𝕜] G) :
  is_bounded_bilinear_map 𝕜 (λ x : E × F, f x.1 x.2) :=
{ add_left := f.map_add₂,
  smul_left := f.map_smul₂,
  add_right := λ x, (f x).map_add,
  smul_right := λ c x, (f x).map_smul c,
  bound := ⟨max ‖f‖ 1, zero_lt_one.trans_le (le_max_right _ _),
    λ x y, (f.le_op_norm₂ x y).trans $
      by apply_rules [mul_le_mul_of_nonneg_right, norm_nonneg, le_max_left]⟩ }

protected lemma is_bounded_bilinear_map.is_O (h : is_bounded_bilinear_map 𝕜 f) :
  f =O[⊤] (λ p : E × F, ‖p.1‖ * ‖p.2‖) :=
let ⟨C, Cpos, hC⟩ := h.bound in asymptotics.is_O.of_bound _ $
filter.eventually_of_forall $ λ ⟨x, y⟩, by simpa [mul_assoc] using hC x y

lemma is_bounded_bilinear_map.is_O_comp {α : Type*} (H : is_bounded_bilinear_map 𝕜 f)
  {g : α → E} {h : α → F} {l : filter α} :
  (λ x, f (g x, h x)) =O[l] (λ x, ‖g x‖ * ‖h x‖) :=
H.is_O.comp_tendsto le_top

protected lemma is_bounded_bilinear_map.is_O' (h : is_bounded_bilinear_map 𝕜 f) :
  f =O[⊤] (λ p : E × F, ‖p‖ * ‖p‖) :=
h.is_O.trans $ (@asymptotics.is_O_fst_prod' _ E F _ _ _ _).norm_norm.mul
  (@asymptotics.is_O_snd_prod' _ E F _ _ _ _).norm_norm

lemma is_bounded_bilinear_map.map_sub_left (h : is_bounded_bilinear_map 𝕜 f) {x y : E} {z : F} :
  f (x - y, z) = f (x, z) - f(y, z) :=
calc f (x - y, z) = f (x + (-1 : 𝕜) • y, z) : by simp [sub_eq_add_neg]
... = f (x, z) + (-1 : 𝕜) • f (y, z) : by simp only [h.add_left, h.smul_left]
... = f (x, z) - f (y, z) : by simp [sub_eq_add_neg]

lemma is_bounded_bilinear_map.map_sub_right (h : is_bounded_bilinear_map 𝕜 f) {x : E} {y z : F} :
  f (x, y - z) = f (x, y) - f (x, z) :=
calc f (x, y - z) = f (x, y + (-1 : 𝕜) • z) : by simp [sub_eq_add_neg]
... = f (x, y) + (-1 : 𝕜) • f (x, z) : by simp only [h.add_right, h.smul_right]
... = f (x, y) - f (x, z) : by simp [sub_eq_add_neg]

/-- Useful to use together with `continuous.comp₂`. -/
lemma is_bounded_bilinear_map.continuous (h : is_bounded_bilinear_map 𝕜 f) :
  continuous f :=
begin
  have one_ne : (1:ℝ) ≠ 0 := by simp,
  obtain ⟨C, (Cpos : 0 < C), hC⟩ := h.bound,
  rw continuous_iff_continuous_at,
  intros x,
  have H : ∀ (a:E) (b:F), ‖f (a, b)‖ ≤ C * ‖‖a‖ * ‖b‖‖,
  { intros a b,
    simpa [mul_assoc] using hC a b },
  have h₁ : (λ e : E × F, f (e.1 - x.1, e.2)) =o[𝓝 x] (λ e, (1:ℝ)),
  { refine (asymptotics.is_O_of_le' (𝓝 x) (λ e, H (e.1 - x.1) e.2)).trans_is_o _,
    rw asymptotics.is_o_const_iff one_ne,
    convert ((continuous_fst.sub continuous_const).norm.mul continuous_snd.norm).continuous_at,
    { simp },
    apply_instance },
  have h₂ : (λ e : E × F, f (x.1, e.2 - x.2)) =o[𝓝 x] (λ e, (1:ℝ)),
  { refine (asymptotics.is_O_of_le' (𝓝 x) (λ e, H x.1 (e.2 - x.2))).trans_is_o _,
    rw asymptotics.is_o_const_iff one_ne,
    convert (continuous_const.mul (continuous_snd.sub continuous_const).norm).continuous_at,
    { simp },
    apply_instance },
  have := h₁.add h₂,
  rw asymptotics.is_o_const_iff one_ne at this,
  change tendsto _ _ _,
  convert this.add_const (f x),
  { ext e,
    simp [h.map_sub_left, h.map_sub_right], },
  { simp }
end

lemma is_bounded_bilinear_map.continuous_left (h : is_bounded_bilinear_map 𝕜 f) {e₂ : F} :
  continuous (λe₁, f (e₁, e₂)) :=
h.continuous.comp (continuous_id.prod_mk continuous_const)

lemma is_bounded_bilinear_map.continuous_right (h : is_bounded_bilinear_map 𝕜 f) {e₁ : E} :
  continuous (λe₂, f (e₁, e₂)) :=
h.continuous.comp (continuous_const.prod_mk continuous_id)

/-- Useful to use together with `continuous.comp₂`. -/
lemma continuous_linear_map.continuous₂ (f : E →L[𝕜] F →L[𝕜] G) :
  continuous (function.uncurry (λ x y, f x y)) :=
f.is_bounded_bilinear_map.continuous

lemma is_bounded_bilinear_map.is_bounded_linear_map_left (h : is_bounded_bilinear_map 𝕜 f) (y : F) :
  is_bounded_linear_map 𝕜 (λ x, f (x, y)) :=
{ map_add  := λ x x', h.add_left _ _ _,
  map_smul := λ c x, h.smul_left _ _ _,
  bound    := begin
    rcases h.bound with ⟨C, C_pos, hC⟩,
    refine ⟨C * (‖y‖ + 1), mul_pos C_pos (lt_of_lt_of_le (zero_lt_one) (by simp)), λ x, _⟩,
    have : ‖y‖ ≤ ‖y‖ + 1, by simp [zero_le_one],
    calc ‖f (x, y)‖ ≤ C * ‖x‖ * ‖y‖ : hC x y
    ... ≤ C * ‖x‖ * (‖y‖ + 1) :
      by apply_rules [norm_nonneg, mul_le_mul_of_nonneg_left, le_of_lt C_pos, mul_nonneg]
    ... = C * (‖y‖ + 1) * ‖x‖ : by ring
  end }

lemma is_bounded_bilinear_map.is_bounded_linear_map_right
  (h : is_bounded_bilinear_map 𝕜 f) (x : E) :
  is_bounded_linear_map 𝕜 (λ y, f (x, y)) :=
{ map_add  := λ y y', h.add_right _ _ _,
  map_smul := λ c y, h.smul_right _ _ _,
  bound    := begin
    rcases h.bound with ⟨C, C_pos, hC⟩,
    refine ⟨C * (‖x‖ + 1), mul_pos C_pos (lt_of_lt_of_le (zero_lt_one) (by simp)), λ y, _⟩,
    have : ‖x‖ ≤ ‖x‖ + 1, by simp [zero_le_one],
    calc ‖f (x, y)‖ ≤ C * ‖x‖ * ‖y‖ : hC x y
    ... ≤ C * (‖x‖ + 1) * ‖y‖ :
      by apply_rules [mul_le_mul_of_nonneg_right, norm_nonneg, mul_le_mul_of_nonneg_left,
                      le_of_lt C_pos]
  end }

lemma is_bounded_bilinear_map_smul {𝕜' : Type*} [normed_field 𝕜']
  [normed_algebra 𝕜 𝕜'] {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] [normed_space 𝕜' E]
  [is_scalar_tower 𝕜 𝕜' E] :
  is_bounded_bilinear_map 𝕜 (λ (p : 𝕜' × E), p.1 • p.2) :=
(lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] E →L[𝕜] E).is_bounded_bilinear_map

lemma is_bounded_bilinear_map_mul :
  is_bounded_bilinear_map 𝕜 (λ (p : 𝕜 × 𝕜), p.1 * p.2) :=
by simp_rw ← smul_eq_mul; exact is_bounded_bilinear_map_smul

lemma is_bounded_bilinear_map_comp :
  is_bounded_bilinear_map 𝕜 (λ (p : (F →L[𝕜] G) × (E →L[𝕜] F)), p.1.comp p.2) :=
(compL 𝕜 E F G).is_bounded_bilinear_map

lemma continuous_linear_map.is_bounded_linear_map_comp_left (g : F →L[𝕜] G) :
  is_bounded_linear_map 𝕜 (λ (f : E →L[𝕜] F), continuous_linear_map.comp g f) :=
is_bounded_bilinear_map_comp.is_bounded_linear_map_right _

lemma continuous_linear_map.is_bounded_linear_map_comp_right (f : E →L[𝕜] F) :
  is_bounded_linear_map 𝕜 (λ (g : F →L[𝕜] G), continuous_linear_map.comp g f) :=
is_bounded_bilinear_map_comp.is_bounded_linear_map_left _

lemma is_bounded_bilinear_map_apply :
  is_bounded_bilinear_map 𝕜 (λ p : (E →L[𝕜] F) × E, p.1 p.2) :=
(continuous_linear_map.flip (apply 𝕜 F : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F)).is_bounded_bilinear_map

/-- The function `continuous_linear_map.smul_right`, associating to a continuous linear map
`f : E → 𝕜` and a scalar `c : F` the tensor product `f ⊗ c` as a continuous linear map from `E` to
`F`, is a bounded bilinear map. -/
lemma is_bounded_bilinear_map_smul_right :
  is_bounded_bilinear_map 𝕜
    (λ p, (continuous_linear_map.smul_right : (E →L[𝕜] 𝕜) → F → (E →L[𝕜] F)) p.1 p.2) :=
(smul_rightL 𝕜 E F).is_bounded_bilinear_map

/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
lemma is_bounded_bilinear_map_comp_multilinear {ι : Type*} {E : ι → Type*}
  [fintype ι] [∀ i, normed_add_comm_group (E i)] [∀ i, normed_space 𝕜 (E i)] :
  is_bounded_bilinear_map 𝕜 (λ p : (F →L[𝕜] G) × (continuous_multilinear_map 𝕜 E F),
    p.1.comp_continuous_multilinear_map p.2) :=
(comp_continuous_multilinear_mapL 𝕜 E F G).is_bounded_bilinear_map

/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q ↦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here as a linear map `E × F →ₗ[𝕜] G`, then `is_bounded_bilinear_map.deriv`
strengthens it to a continuous linear map `E × F →L[𝕜] G`.
``. -/
def is_bounded_bilinear_map.linear_deriv (h : is_bounded_bilinear_map 𝕜 f) (p : E × F) :
  E × F →ₗ[𝕜] G :=
{ to_fun := λ q, f (p.1, q.2) + f (q.1, p.2),
  map_add' := λ q₁ q₂, begin
    change f (p.1, q₁.2 + q₂.2) + f (q₁.1 + q₂.1, p.2) =
      f (p.1, q₁.2) + f (q₁.1, p.2) + (f (p.1, q₂.2) + f (q₂.1, p.2)),
    simp [h.add_left, h.add_right], abel
  end,
  map_smul' := λ c q, begin
    change f (p.1, c • q.2) + f (c • q.1, p.2) = c • (f (p.1, q.2) + f (q.1, p.2)),
    simp [h.smul_left, h.smul_right, smul_add]
  end }

/-- The derivative of a bounded bilinear map at a point `p : E × F`, as a continuous linear map
from `E × F` to `G`. The statement that this is indeed the derivative of `f` is
`is_bounded_bilinear_map.has_fderiv_at` in `analysis.calculus.fderiv`. -/
def is_bounded_bilinear_map.deriv (h : is_bounded_bilinear_map 𝕜 f) (p : E × F) : E × F →L[𝕜] G :=
(h.linear_deriv p).mk_continuous_of_exists_bound $ begin
  rcases h.bound with ⟨C, Cpos, hC⟩,
  refine ⟨C * ‖p.1‖ + C * ‖p.2‖, λ q, _⟩,
  calc ‖f (p.1, q.2) + f (q.1, p.2)‖
    ≤ C * ‖p.1‖ * ‖q.2‖ + C * ‖q.1‖ * ‖p.2‖ : norm_add_le_of_le (hC _ _) (hC _ _)
  ... ≤ C * ‖p.1‖ * ‖q‖ + C * ‖q‖ * ‖p.2‖ : begin
      apply add_le_add,
      exact mul_le_mul_of_nonneg_left
        (le_max_right _ _) (mul_nonneg (le_of_lt Cpos) (norm_nonneg _)),
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt Cpos),
  end
  ... = (C * ‖p.1‖ + C * ‖p.2‖) * ‖q‖ : by ring
end

@[simp] lemma is_bounded_bilinear_map_deriv_coe (h : is_bounded_bilinear_map 𝕜 f) (p q : E × F) :
  h.deriv p q = f (p.1, q.2) + f (q.1, p.2) := rfl

variables (𝕜)

/-- The function `continuous_linear_map.mul_left_right : 𝕜' × 𝕜' → (𝕜' →L[𝕜] 𝕜')` is a bounded
bilinear map. -/
lemma continuous_linear_map.mul_left_right_is_bounded_bilinear
  (𝕜' : Type*) [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] :
  is_bounded_bilinear_map 𝕜 (λ p : 𝕜' × 𝕜', continuous_linear_map.mul_left_right 𝕜 𝕜' p.1 p.2) :=
(continuous_linear_map.mul_left_right 𝕜 𝕜').is_bounded_bilinear_map

variables {𝕜}

/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
lemma is_bounded_bilinear_map.is_bounded_linear_map_deriv (h : is_bounded_bilinear_map 𝕜 f) :
  is_bounded_linear_map 𝕜 (λ p : E × F, h.deriv p) :=
begin
  rcases h.bound with ⟨C, Cpos : 0 < C, hC⟩,
  refine is_linear_map.with_bound ⟨λ p₁ p₂, _, λ c p, _⟩ (C + C) (λ p, _),
  { ext; simp only [h.add_left, h.add_right, coe_comp', function.comp_app, inl_apply,
    is_bounded_bilinear_map_deriv_coe, prod.fst_add, prod.snd_add, add_apply]; abel },
  { ext; simp only [h.smul_left, h.smul_right, smul_add, coe_comp', function.comp_app,
    is_bounded_bilinear_map_deriv_coe, prod.smul_fst, prod.smul_snd, coe_smul', pi.smul_apply] },
  { refine continuous_linear_map.op_norm_le_bound _
      (mul_nonneg (add_nonneg Cpos.le Cpos.le) (norm_nonneg _)) (λ q, _),
    calc ‖f (p.1, q.2) + f (q.1, p.2)‖
      ≤ C * ‖p.1‖ * ‖q.2‖ + C * ‖q.1‖ * ‖p.2‖ : norm_add_le_of_le (hC _ _) (hC _ _)
    ... ≤ C * ‖p‖ * ‖q‖ + C * ‖q‖ * ‖p‖ : by apply_rules [add_le_add, mul_le_mul, norm_nonneg,
      Cpos.le, le_refl, le_max_left, le_max_right, mul_nonneg]
    ... = (C + C) * ‖p‖ * ‖q‖ : by ring },
end

end bilinear_map

lemma continuous.clm_comp {X} [topological_space X] {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
  (hg : continuous g) (hf : continuous f) :
  continuous (λ x, (g x).comp (f x)) :=
(compL 𝕜 E F G).continuous₂.comp₂ hg hf

lemma continuous_on.clm_comp {X} [topological_space X] {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
  {s : set X} (hg : continuous_on g s) (hf : continuous_on f s) :
  continuous_on (λ x, (g x).comp (f x)) s :=
(compL 𝕜 E F G).continuous₂.comp_continuous_on (hg.prod hf)

namespace continuous_linear_equiv

open set

/-!
### The set of continuous linear equivalences between two Banach spaces is open

In this section we establish that the set of continuous linear equivalences between two Banach
spaces is an open subset of the space of linear maps between them.
-/

protected lemma is_open [complete_space E] : is_open (range (coe : (E ≃L[𝕜] F) → (E →L[𝕜] F))) :=
begin
  rw [is_open_iff_mem_nhds, forall_range_iff],
  refine λ e, is_open.mem_nhds _ (mem_range_self _),
  let O : (E →L[𝕜] F) → (E →L[𝕜] E) := λ f, (e.symm : F →L[𝕜] E).comp f,
  have h_O : continuous O := is_bounded_bilinear_map_comp.continuous_right,
  convert show is_open (O ⁻¹' {x | is_unit x}), from units.is_open.preimage h_O using 1,
  ext f',
  split,
  { rintros ⟨e', rfl⟩,
    exact ⟨(e'.trans e.symm).to_unit, rfl⟩ },
  { rintros ⟨w, hw⟩,
    use (units_equiv 𝕜 E w).trans e,
    ext x,
    simp [coe_fn_coe_base' w, hw] }
end

protected lemma nhds [complete_space E] (e : E ≃L[𝕜] F) :
  (range (coe : (E ≃L[𝕜] F) → (E →L[𝕜] F))) ∈ 𝓝 (e : E →L[𝕜] F) :=
is_open.mem_nhds continuous_linear_equiv.is_open (by simp)

end continuous_linear_equiv
