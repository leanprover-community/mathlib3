/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov.
-/
import analysis.calculus.inverse
import analysis.normed_space.complemented

/-!
# Implicit function theorem

We prove three versions of the implicit function theorem. First we define a structure
`implicit_function_data` that holds arguments for the most general version of the implicit function
theorem, see `implicit_function_data.implicit_function`
and `implicit_function_data.to_implicit_function`. This version allows a user to choose
a specific implicit function but provides only a little convenience over the inverse function
theorem.

Then we define `implicit_function_of_complemented`: implicit function defined by `f (g z y) = z`,
where `f : E → F` is a function strictly differentiable at `a` such that its defivative `f'`
is surjective and has a `complemented` kernel.

Finally, if the codomain of `f` is a finitely dimensional space, then we can automatically prove
that the kernel of `f'` is complemented, hence the only assumptions are `has_strict_fderiv_at`
and `f'.range = ⊤`. This version is named `implicit_function`.

## Tags

implicit function, inverse function
-/

noncomputable theory

open_locale topological_space
open filter
open continuous_linear_map (fst snd subtype_val smul_right ker_prod)
open continuous_linear_equiv (of_bijective)

/-- Data for the general version -/
structure implicit_function_data (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] [complete_space E]
  (F : Type*) [normed_group F] [normed_space 𝕜 F] [complete_space F]
  (G : Type*) [normed_group G] [normed_space 𝕜 G] [complete_space G] :=
(left_fun : E → F)
(left_deriv : E →L[𝕜] F)
(right_fun : E → G)
(right_deriv : E →L[𝕜] G)
(pt : E)
(left_has_deriv : has_strict_fderiv_at left_fun left_deriv pt)
(right_has_deriv : has_strict_fderiv_at right_fun right_deriv pt)
(left_range : left_deriv.range = ⊤)
(right_range : right_deriv.range = ⊤)
(is_compl_ker : is_compl left_deriv.ker right_deriv.ker)

namespace implicit_function_data

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [complete_space E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F] [complete_space F]
  {G : Type*} [normed_group G] [normed_space 𝕜 G] [complete_space G]
  (φ : implicit_function_data 𝕜 E F G)

/-- The function given by `x ↦ (left_fun x, right_fun x)`. -/
def prod_fun (x : E) : F × G := (φ.left_fun x, φ.right_fun x)

@[simp] lemma prod_fun_apply (x : E) : φ.prod_fun x = (φ.left_fun x, φ.right_fun x) := rfl

protected lemma has_strict_fderiv_at :
  has_strict_fderiv_at φ.prod_fun
    (φ.left_deriv.equiv_prod_of_surjective_of_is_compl φ.right_deriv φ.left_range φ.right_range
       φ.is_compl_ker : E →L[𝕜] F × G) φ.pt :=
φ.left_has_deriv.prod φ.right_has_deriv

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complement subspaces of `E`, then `x ↦ (f x, g x)` defines a local homeomorphism between
`E` and `F × G`. In particular, `f x = f a` is locally homeomorphic to `G`. -/
def to_local_homeomorph : local_homeomorph E (F × G) :=
φ.has_strict_fderiv_at.to_local_homeomorph _

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complement subspaces of `E`, then `implicit_function_of_is_compl_ker` is the unique (germ of a) map
`φ : F → G → E` such that `f (φ y z) = y` and `g (φ y z) = z`. -/
def implicit_function : F → G → E := function.curry $ φ.to_local_homeomorph.symm

@[simp] lemma to_local_homeomorph_coe : ⇑(φ.to_local_homeomorph) = φ.prod_fun := rfl

lemma to_local_homeomorph_apply (x : E) :
  φ.to_local_homeomorph x = (φ.left_fun x, φ.right_fun x) :=
rfl

lemma pt_mem_to_local_homeomorph_source :
  φ.pt ∈ φ.to_local_homeomorph.source :=
φ.has_strict_fderiv_at.mem_to_local_homeomorph_source

lemma map_pt_mem_to_local_homeomorph_target :
  (φ.left_fun φ.pt, φ.right_fun φ.pt) ∈ φ.to_local_homeomorph.target :=
φ.to_local_homeomorph.map_source $ φ.pt_mem_to_local_homeomorph_source

lemma prod_map_implicit_function :
  ∀ᶠ (p : F × G) in 𝓝 (φ.prod_fun φ.pt), φ.prod_fun (φ.implicit_function p.1 p.2) = p :=
φ.has_strict_fderiv_at.eventually_right_inverse.mono $ λ ⟨z, y⟩ h, h

lemma left_map_implicit_function :
  ∀ᶠ (p : F × G) in 𝓝 (φ.prod_fun φ.pt), φ.left_fun (φ.implicit_function p.1 p.2) = p.1 :=
φ.prod_map_implicit_function.mono $ λ z, congr_arg prod.fst

lemma right_map_implicit_function :
  ∀ᶠ (p : F × G) in 𝓝 (φ.prod_fun φ.pt), φ.right_fun (φ.implicit_function p.1 p.2) = p.2 :=
φ.prod_map_implicit_function.mono $ λ z, congr_arg prod.snd

lemma implicit_function_apply_image :
  ∀ᶠ x in 𝓝 φ.pt, φ.implicit_function (φ.left_fun x) (φ.right_fun x) = x :=
φ.has_strict_fderiv_at.eventually_left_inverse

lemma to_implicit_function
  (g'inv : G →L[𝕜] E) (hg'inv : φ.right_deriv.comp g'inv = continuous_linear_map.id 𝕜 G)
  (hg'invf : φ.left_deriv.comp g'inv = 0) :
  has_strict_fderiv_at (φ.implicit_function (φ.left_fun φ.pt)) g'inv (φ.right_fun φ.pt) :=
begin
  have := φ.has_strict_fderiv_at.to_local_inverse,
  simp only [prod_fun] at this,
  convert this.comp (φ.right_fun φ.pt)
    ((has_strict_fderiv_at_const _ _).prod (has_strict_fderiv_at_id _)),
  simp only [continuous_linear_map.ext_iff, continuous_linear_map.coe_comp', function.comp_app]
    at hg'inv hg'invf ⊢,
  simp [continuous_linear_equiv.eq_symm_apply, *]
end


end implicit_function_data

namespace has_strict_fderiv_at

section complemented

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [complete_space E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F] [complete_space F]
  {f : E → F} {f' : E →L[𝕜] F} {a : E}

section defs

variables (f f')

/-- Data used to apply generic implicit function theorem to the case of a strictrly differentiable
 map such that its derivative is surjective has has a complemented kernel. -/
@[simp] def implicit_function_data_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.closed_complemented) :
  implicit_function_data 𝕜 E F f'.ker :=
{ left_fun := f,
  left_deriv := f',
  right_fun := λ x, classical.some hker (x - a),
  right_deriv := classical.some hker,
  pt := a,
  left_has_deriv := hf,
  right_has_deriv := (classical.some hker).has_strict_fderiv_at.comp a
    ((has_strict_fderiv_at_id a).sub_const a),
  left_range := hf',
  right_range := linear_map.range_eq_of_proj (classical.some_spec hker),
  is_compl_ker := linear_map.is_compl_of_proj (classical.some_spec hker) }

/-- A local homeomorphism between E` and `F × f'.ker` sending level surfaces of `f`
to horizontal subspaces. -/
def implicit_to_local_homeomorph_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.closed_complemented) :
  local_homeomorph E (F × f'.ker) :=
(implicit_function_data_of_complemented f f' hf hf' hker).to_local_homeomorph

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicit_function_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.closed_complemented) :
  F → f'.ker → E :=
(implicit_function_data_of_complemented f f' hf hf' hker).implicit_function

end defs

@[simp] lemma implicit_to_local_homeomorph_of_complemented_fst (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.closed_complemented) (x : E) :
  (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker x).fst = f x :=
rfl

lemma implicit_to_local_homeomorph_of_complemented_apply
  (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤)
  (hker : f'.ker.closed_complemented) (y : E) :
  hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker y =
    (f y, classical.some hker (y - a)) :=
rfl

@[simp] lemma implicit_to_local_homeomorph_of_complemented_apply_ker
  (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤)
  (hker : f'.ker.closed_complemented) (y : f'.ker) :
  hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker (y + a) = (f (y + a), y) :=
by simp only [implicit_to_local_homeomorph_of_complemented_apply, add_sub_cancel,
  classical.some_spec hker]

@[simp] lemma implicit_to_local_homeomorph_of_complemented_self
  (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.closed_complemented) :
  hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker a = (f a, 0) :=
by simp [hf.implicit_to_local_homeomorph_of_complemented_apply]

lemma mem_implicit_to_local_homeomorph_of_complemented_source (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.closed_complemented) :
  a ∈ (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).source :=
mem_to_local_homeomorph_source _

lemma mem_implicit_to_local_homeomorph_of_complemented_target (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.closed_complemented) :
  (f a, (0 : f'.ker)) ∈ (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).target :=
by simpa only [implicit_to_local_homeomorph_of_complemented_self] using
  ((hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).map_source $
    (hf.mem_implicit_to_local_homeomorph_of_complemented_source hf' hker))

/-- `implicit_function_of_complemented` sends `(z, y)` to a point in `f ⁻¹' z`. -/
lemma map_implicit_function_of_complemented_eq (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.closed_complemented) :
  ∀ᶠ (p : F × f'.ker) in 𝓝 (f a, 0),
    f (hf.implicit_function_of_complemented f f' hf' hker p.1 p.2) = p.1 :=
((hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).eventually_right_inverse $
  hf.mem_implicit_to_local_homeomorph_of_complemented_target hf' hker).mono $ λ ⟨z, y⟩ h,
    congr_arg prod.fst h

/-- Any point in some neighborhood of `a` can be represented as `implicit_function`
of some point. -/
lemma eq_implicit_function_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.closed_complemented) :
  ∀ᶠ x in 𝓝 a, hf.implicit_function_of_complemented f f' hf' hker (f x)
    (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker x).snd = x :=
(implicit_function_data_of_complemented f f' hf hf' hker).implicit_function_apply_image

lemma to_implicit_function_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.closed_complemented) :
  has_strict_fderiv_at (hf.implicit_function_of_complemented f f' hf' hker (f a))
    (subtype_val f'.ker) 0 :=
by convert (implicit_function_data_of_complemented f f' hf hf' hker).to_implicit_function
  (subtype_val f'.ker) _ _; [skip, ext, ext]; simp [classical.some_spec hker]

end complemented

section finite_dimensional

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [complete_space E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F]
  (f : E → F) (f' : E →L[𝕜] F) {a : E}

/-- Given a map `f : E → F` to a finite dimensional space with a surjective derivative `f'`,
returns a local homeomorphism between `E` and `F × ker f'`. -/
def implicit_to_local_homeomorph (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  local_homeomorph E (F × f'.ker) :=
by haveI := finite_dimensional.complete 𝕜 F; exact
hf.implicit_to_local_homeomorph_of_complemented f f' hf'
  f'.ker_closed_complemented_of_finite_dimensional_range

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicit_function (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  F → f'.ker → E :=
function.curry $ (hf.implicit_to_local_homeomorph f f' hf').symm

variables {f f'}

@[simp] lemma implicit_to_local_homeomorph_fst (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (x : E) :
  (hf.implicit_to_local_homeomorph f f' hf' x).fst = f x :=
rfl

@[simp] lemma implicit_to_local_homeomorph_apply_ker
  (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) (y : f'.ker) :
  hf.implicit_to_local_homeomorph f f' hf' (y + a) = (f (y + a), y) :=
by apply implicit_to_local_homeomorph_of_complemented_apply_ker

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
