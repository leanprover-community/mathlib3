/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov.
-/
import analysis.calculus.inverse
import analysis.normed_space.complemented

/-!
# Implicit function theorem

We prove three versions of the implicit function theorem.

* `implicit_function_of_proj` : TODO

* `implicit_function_of_complemented`: implicit function defined by `f (g z y) = z`, where
  `f : E → F` is a function strictly differentiable at `a` such that its defivative `f'`
  is surjective and has a `complemented` kernel;

* `implicit_function`: implicit function defined by `f (g z y) = z`, where `f : E → F` is a function
  with finitely dimensional codomain such that `f` is strictly differentiable at `a` and its
  defivative `f'` is surjective.
-/

noncomputable theory

open_locale topological_space
open continuous_linear_map (fst snd subtype_val smul_right ker_prod)
open continuous_linear_equiv (of_bijective)

namespace has_strict_fderiv_at

section generic

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [complete_space E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F] [complete_space F]
  {G : Type*} [normed_group G] [normed_space 𝕜 G] [complete_space G]
  {f : E → F} {f' : E ≃L[𝕜] F × G} {a : E}

lemma implicit_aux_deriv_of_proj
  (hf : has_strict_fderiv_at f ((fst 𝕜 F G).comp f') a) :
  has_strict_fderiv_at (λ x, (f x, (f' (x - a)).2)) (f' : E →L[𝕜] F × G) a :=
begin
  convert hf.prod ((continuous_linear_equiv.has_strict_fderiv_at f').comp a
    ((has_strict_fderiv_at_id a).sub_const a)).snd,
  ext x; simp
end

section defs

variables (f f')

def implicit_to_local_homeomorph_of_proj
  (hf : has_strict_fderiv_at f ((fst 𝕜 F G).comp f') a) :
  local_homeomorph E (F × G) :=
(implicit_aux_deriv_of_proj hf).to_local_homeomorph _

def implicit_function_of_proj
  (hf : has_strict_fderiv_at f ((fst 𝕜 F G).comp f') a) :
  F → G → E :=
function.curry $ (hf.implicit_to_local_homeomorph_of_proj f f').symm

end defs

@[simp] lemma implicit_to_local_homeomorph_of_proj_apply
  (hf : has_strict_fderiv_at f ((fst 𝕜 F G).comp f') a) (x : E) :
  hf.implicit_to_local_homeomorph_of_proj f f' x = (f x, (f' (x - a)).2) :=
rfl

lemma mem_implicit_to_local_homeomorph_of_proj_source
  (hf : has_strict_fderiv_at f ((fst 𝕜 F G).comp f') a) :
  a ∈ (hf.implicit_to_local_homeomorph_of_proj f f').source :=
mem_to_local_homeomorph_source _

lemma mem_implicit_to_local_homeomorph_of_proj_target
  (hf : has_strict_fderiv_at f ((fst 𝕜 F G).comp f') a) :
  (f a, (0 : G)) ∈ (hf.implicit_to_local_homeomorph_of_proj f f').target :=
by simpa using
  ((hf.implicit_to_local_homeomorph_of_proj f f').map_source $
    (hf.mem_implicit_to_local_homeomorph_of_proj_source))

/-- `implicit_function_of_complemented` sends `(z, y)` to a point in `f ⁻¹' z`. -/
lemma map_implicit_function_of_proj_eq
  (hf : has_strict_fderiv_at f ((fst 𝕜 F G).comp f') a) :
  ∀ᶠ (p : F × G) in 𝓝 (f a, 0),
    f (hf.implicit_function_of_proj f f' p.1 p.2) = p.1 :=
((hf.implicit_to_local_homeomorph_of_proj f f').eventually_right_inverse $
  hf.mem_implicit_to_local_homeomorph_of_proj_target).mono $ λ ⟨z, y⟩ h,
    congr_arg prod.fst h

/-- Any point in some neighborhood of `a` can be represented as `implicit_function`
of some point. -/
lemma eq_implicit_function_of_proj
  (hf : has_strict_fderiv_at f ((fst 𝕜 F G).comp f') a) :
  ∀ᶠ x in 𝓝 a, hf.implicit_function_of_proj f f' (f x)
    (hf.implicit_to_local_homeomorph_of_proj f f' x).snd = x :=
hf.implicit_aux_deriv_of_proj.eventually_left_inverse

lemma to_implicit_function_of_proj (hf : has_strict_fderiv_at f ((fst 𝕜 F G).comp f') a)
  (f'inv : G →L[𝕜] E) (hf'inv : ∀ z : G, f' (f'inv z) = (0, z)) :
  has_strict_fderiv_at (hf.implicit_function_of_proj f f' (f a)) f'inv 0 :=
begin
  have := hf.implicit_aux_deriv_of_proj.to_local_inverse,
  simp only [sub_self, continuous_linear_equiv.map_zero, prod.snd_zero] at this,
  convert this.comp 0
    ((has_strict_fderiv_at_const (f a) 0).prod $ has_strict_fderiv_at_id 0),
  ext x,
  simp [continuous_linear_equiv.eq_symm_apply, hf'inv]
end

end generic

section complemented

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [complete_space E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F] [complete_space F]
  {f : E → F} {f' : E →L[𝕜] F} {a : E}

/-- An auxiliary lemma used to prove the Implicit function theorem for a map with a surjective
derivative `f' : E → F` with fixed projection `proj : E → ker f'`. This lemma states that
`x ↦ (f x, proj (x - a))` has derivative `x ↦ (f' x, proj x)`, and the latter map is a continuous
linear equivalence. -/
lemma implicit_aux_deriv_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  has_strict_fderiv_at (λ x, (f x, classical.some hker (x - a)))
    ((classical.some hker).equiv_prod_of_proj_ker_of_surjective (classical.some_spec hker) hf' :
      E →L[𝕜] F × f'.ker) a :=
hf.prod $ (classical.some hker).has_strict_fderiv_at.comp a ((has_strict_fderiv_at_id a).sub_const a)

section defs

variables (f f')

/-- A local homeomorphism between E` and `F × f'.ker` sending level surfaces of `f`
to horizontal subspaces. -/
def implicit_to_local_homeomorph_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  local_homeomorph E (F × f'.ker) :=
(implicit_aux_deriv_of_complemented hf hf' hker).to_local_homeomorph _

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicit_function_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  F → f'.ker → E :=
function.curry $ (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).symm

end defs

@[simp] lemma implicit_to_local_homeomorph_of_complemented_fst (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) (x : E) :
  (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker x).fst = f x :=
rfl

@[simp] lemma implicit_to_local_homeomorph_of_complemented_ker
  (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤)
  (hker : f'.ker.complemented) (y : f'.ker) :
  hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker (y + a) = (f (y + a), y) :=
by simp only [implicit_to_local_homeomorph_of_complemented, to_local_homeomorph_coe,
  add_sub_cancel, classical.some_spec hker]

@[simp] lemma implicit_to_local_homeomorph_of_complemented_self
  (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker a = (f a, 0) :=
by simpa only [submodule.coe_zero, zero_add]
  using hf.implicit_to_local_homeomorph_of_complemented_ker hf' hker 0

lemma mem_implicit_to_local_homeomorph_of_complemented_source (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  a ∈ (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).source :=
mem_to_local_homeomorph_source _

lemma mem_implicit_to_local_homeomorph_of_complemented_target (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  (f a, (0 : f'.ker)) ∈ (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).target :=
by simpa only [implicit_to_local_homeomorph_of_complemented_self] using
  ((hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).map_source $
    (hf.mem_implicit_to_local_homeomorph_of_complemented_source hf' hker))

/-- `implicit_function_of_complemented` sends `(z, y)` to a point in `f ⁻¹' z`. -/
lemma map_implicit_function_of_complemented_eq (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  ∀ᶠ (p : F × f'.ker) in 𝓝 (f a, 0),
    f (hf.implicit_function_of_complemented f f' hf' hker p.1 p.2) = p.1 :=
((hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).eventually_right_inverse $
  hf.mem_implicit_to_local_homeomorph_of_complemented_target hf' hker).mono $ λ ⟨z, y⟩ h,
    congr_arg prod.fst h

/-- Any point in some neighborhood of `a` can be represented as `implicit_function`
of some point. -/
lemma eq_implicit_function_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  ∀ᶠ x in 𝓝 a, hf.implicit_function_of_complemented f f' hf' hker (f x)
    (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker x).snd = x :=
(hf.implicit_aux_deriv_of_complemented hf' hker).eventually_left_inverse

lemma to_implicit_function_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  has_strict_fderiv_at (hf.implicit_function_of_complemented f f' hf' hker (f a))
    (subtype_val f'.ker) 0 :=
begin
  have := (hf.implicit_aux_deriv_of_complemented hf' hker).to_local_inverse,
  simp only [sub_self, continuous_linear_map.map_zero] at this,
  convert this.comp 0
    ((has_strict_fderiv_at_const (f a) 0).prod $ has_strict_fderiv_at_id 0),
  ext x,
  simp [continuous_linear_equiv.eq_symm_apply, classical.some_spec hker]
end

end complemented

section finite_dimensional

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [complete_space E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F]
  (f : E → F) (f' : E →L[𝕜] F) {a : E}

def implicit_to_local_homeomorph (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  local_homeomorph E (F × f'.ker) :=
by haveI := finite_dimensional.complete 𝕜 F; exact
hf.implicit_to_local_homeomorph_of_complemented f f' hf'
  f'.ker_complemented_of_finite_dimensional_range

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicit_function (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  F → f'.ker → E :=
function.curry $ (hf.implicit_to_local_homeomorph f f' hf').symm

variables {f f'}

@[simp] lemma implicit_to_local_homeomorph_fst (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (x : E) :
  (hf.implicit_to_local_homeomorph f f' hf' x).fst = f x :=
rfl

@[simp] lemma implicit_to_local_homeomorph_ker
  (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) (y : f'.ker) :
  hf.implicit_to_local_homeomorph f f' hf' (y + a) = (f (y + a), y) :=
by apply implicit_to_local_homeomorph_of_complemented_ker

@[simp] lemma implicit_to_local_homeomorph_self
  (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  hf.implicit_to_local_homeomorph f f' hf' a = (f a, 0) :=
by apply implicit_to_local_homeomorph_of_complemented_self

lemma mem_implicit_to_local_homeomorph_source (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) :
  a ∈ (hf.implicit_to_local_homeomorph f f' hf').source :=
mem_to_local_homeomorph_source _

lemma mem_implicit_to_local_homeomorph_target (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) :
  (f a, (0 : f'.ker)) ∈ (hf.implicit_to_local_homeomorph f f' hf').target :=
by apply mem_implicit_to_local_homeomorph_of_complemented_target

/-- `implicit_function_of_complemented` sends `(z, y)` to a point in `f ⁻¹' z`. -/
lemma map_implicit_function_eq (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  ∀ᶠ (p : F × f'.ker) in 𝓝 (f a, 0), f (hf.implicit_function f f' hf' p.1 p.2) = p.1 :=
by apply map_implicit_function_of_complemented_eq

/-- Any point in some neighborhood of `a` can be represented as `implicit_function`
of some point. -/
lemma eq_implicit_function (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  ∀ᶠ x in 𝓝 a, hf.implicit_function f f' hf' (f x)
    (hf.implicit_to_local_homeomorph f f' hf' x).snd = x :=
by apply eq_implicit_function_of_complemented

lemma to_implicit_function (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  has_strict_fderiv_at (hf.implicit_function f f' hf' (f a))
    (subtype_val f'.ker) 0 :=
by apply to_implicit_function_of_complemented

end finite_dimensional


end has_strict_fderiv_at
