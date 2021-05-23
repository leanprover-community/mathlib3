/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import topology.uniform_space.uniform_embedding

/-!
# Abstract theory of Hausdorff completions of uniform spaces

This file characterizes Hausdorff completions of a uniform space α as complete Hausdorff spaces
equipped with a map from α which has dense image and induce the original uniform structure on α.
Assuming these properties we "extend" uniformly continuous maps from α to complete Hausdorff spaces
to the completions of α. This is the universal property expected from a completion.
It is then used to extend uniformly continuous maps from α to α' to maps between
completions of α and α'.

This file does not construct any such completion, it only study consequences of their existence.
The first advantage is that formal properties are clearly highlighted without interference from
construction details. The second advantage is that this framework can then be used to compare
different completion constructions. See `topology/uniform_space/compare_reals` for an example.
Of course the comparison comes from the universal property as usual.

A general explicit construction of completions is done in `uniform_space/completion`, leading
to a functor from uniform spaces to complete Hausdorff uniform spaces that is left adjoint to the
inclusion, see `uniform_space/UniformSpace` for the category packaging.

## Implementation notes

A tiny technical advantage of using a characteristic predicate such as the properties listed in
`abstract_completion` instead of stating the universal property is that the universal property
derived from the predicate is more universe polymorphic.

## References

We don't know any traditional text discussing this. Real world mathematics simply silently
identify the results of any two constructions that lead to something one could reasonnably
call a completion.

## Tags

uniform spaces, completion, universal property
-/

noncomputable theory
local attribute [instance, priority 10] classical.prop_decidable

open filter set function

universes u
/-- A completion of `α` is the data of a complete separated uniform space (from the same universe)
and a map from `α` with dense range and inducing the original uniform structure on `α`. -/
structure abstract_completion (α : Type u) [uniform_space α] :=
(space : Type u)
(coe : α → space)
(uniform_struct : uniform_space space)
(complete : complete_space space)
(separation : separated_space space)
(uniform_inducing : uniform_inducing coe)
(dense : dense_range coe)

local attribute [instance]
abstract_completion.uniform_struct abstract_completion.complete abstract_completion.separation

namespace abstract_completion
variables {α : Type*} [uniform_space α] (pkg : abstract_completion α)
local notation `hatα` := pkg.space
local notation `ι` := pkg.coe

lemma closure_range : closure (range ι) = univ :=
pkg.dense.closure_range

lemma dense_inducing : dense_inducing ι :=
⟨pkg.uniform_inducing.inducing, pkg.dense⟩

lemma uniform_continuous_coe : uniform_continuous ι :=
uniform_inducing.uniform_continuous pkg.uniform_inducing

lemma continuous_coe : continuous ι :=
pkg.uniform_continuous_coe.continuous

@[elab_as_eliminator]
lemma induction_on {p : hatα → Prop}
  (a : hatα) (hp : is_closed {a | p a}) (ih : ∀ a, p (ι a)) : p a :=
is_closed_property pkg.dense hp ih a

variables {β : Type*} [uniform_space β]

protected lemma funext [t2_space β] {f g : hatα → β} (hf : continuous f) (hg : continuous g)
  (h : ∀ a, f (ι a) = g (ι a)) : f = g :=
funext $ assume a, pkg.induction_on a (is_closed_eq hf hg) h

section extend
/-- Extension of maps to completions -/
protected def extend (f : α → β) : hatα → β :=
if uniform_continuous f then
  pkg.dense_inducing.extend f
else
  λ x, f (pkg.dense.some x)

variables {f : α → β}

lemma extend_def (hf : uniform_continuous f) : pkg.extend f = pkg.dense_inducing.extend f :=
if_pos hf

lemma extend_coe [t2_space β] (hf : uniform_continuous f) (a : α) :
(pkg.extend f) (ι a) = f a :=
begin
  rw pkg.extend_def hf,
  exact pkg.dense_inducing.extend_eq hf.continuous a
end

variables [complete_space β] [separated_space β]

lemma uniform_continuous_extend : uniform_continuous (pkg.extend f) :=
begin
  by_cases hf : uniform_continuous f,
  { rw pkg.extend_def hf,
    exact uniform_continuous_uniformly_extend (pkg.uniform_inducing)
      (pkg.dense) hf },
  { change uniform_continuous (ite _ _ _),
    rw if_neg hf,
    exact uniform_continuous_of_const (assume a b, by congr) }
end

lemma continuous_extend : continuous (pkg.extend f) :=
pkg.uniform_continuous_extend.continuous

lemma extend_unique (hf : uniform_continuous f) {g : hatα → β} (hg : uniform_continuous g)
  (h : ∀ a : α, f a = g (ι a)) : pkg.extend f = g :=
begin
  apply pkg.funext pkg.continuous_extend hg.continuous,
  simpa only [pkg.extend_coe hf] using h
end

@[simp] lemma extend_comp_coe {f : hatα → β} (hf : uniform_continuous f) :
  pkg.extend (f ∘ ι) = f :=
funext $ λ x, pkg.induction_on x (is_closed_eq pkg.continuous_extend hf.continuous)
    (λ y, pkg.extend_coe (hf.comp $ pkg.uniform_continuous_coe) y)

end extend

section map_sec

variables (pkg' : abstract_completion β)
local notation `hatβ` := pkg'.space
local notation `ι'` := pkg'.coe

/-- Lifting maps to completions -/
protected def map (f : α → β) : hatα → hatβ := pkg.extend (ι' ∘ f)

local notation `map` := pkg.map pkg'

variables (f : α → β)

lemma uniform_continuous_map : uniform_continuous (map f) :=
pkg.uniform_continuous_extend

lemma continuous_map : continuous (map f) := pkg.continuous_extend

variables {f}

@[simp] lemma map_coe (hf : uniform_continuous f) (a : α) : map f (ι a) = ι' (f a) :=
pkg.extend_coe (pkg'.uniform_continuous_coe.comp hf) a

lemma map_unique {f : α → β} {g : hatα → hatβ}
  (hg : uniform_continuous g) (h : ∀ a, ι' (f a) = g (ι a)) : map f = g :=
pkg.funext (pkg.continuous_map _ _) hg.continuous $
begin
  intro a,
  change pkg.extend (ι' ∘ f) _ = _,
  simp only [(∘), h],
  rw [pkg.extend_coe (hg.comp pkg.uniform_continuous_coe)]
end

@[simp] lemma map_id : pkg.map pkg id = id :=
pkg.map_unique pkg uniform_continuous_id (assume a, rfl)

variables {γ : Type*} [uniform_space γ]

lemma extend_map [complete_space γ] [separated_space γ] {f : β → γ} {g : α → β}
  (hf : uniform_continuous f) (hg : uniform_continuous g) :
  pkg'.extend f ∘ map g = pkg.extend (f ∘ g) :=
pkg.funext (pkg'.continuous_extend.comp (pkg.continuous_map pkg' _)) pkg.continuous_extend $ λ a,
  by rw [pkg.extend_coe (hf.comp hg), comp_app, pkg.map_coe pkg' hg, pkg'.extend_coe hf]

variables (pkg'' : abstract_completion γ)

lemma map_comp {g : β → γ} {f : α → β} (hg : uniform_continuous g) (hf : uniform_continuous f) :
  (pkg'.map pkg'' g) ∘ (pkg.map pkg' f) = pkg.map pkg'' (g ∘ f) :=
pkg.extend_map pkg' (pkg''.uniform_continuous_coe.comp hg) hf

end map_sec

section compare
-- We can now compare two completion packages for the same uniform space

variables (pkg' : abstract_completion α)

/-- The comparison map between two completions of the same uniform space. -/
def compare : pkg.space → pkg'.space :=
pkg.extend pkg'.coe

lemma uniform_continuous_compare : uniform_continuous (pkg.compare pkg') :=
pkg.uniform_continuous_extend

lemma compare_coe (a : α) : pkg.compare pkg' (pkg.coe a) = pkg'.coe a :=
pkg.extend_coe pkg'.uniform_continuous_coe a

lemma inverse_compare : (pkg.compare pkg') ∘ (pkg'.compare pkg) = id :=
begin
  have uc := pkg.uniform_continuous_compare pkg',
  have uc' := pkg'.uniform_continuous_compare pkg,
  apply pkg'.funext (uc.comp uc').continuous continuous_id,
  intro a,
  rw [comp_app, pkg'.compare_coe pkg, pkg.compare_coe pkg'],
  refl
end

/-- The bijection between two completions of the same uniform space. -/
def compare_equiv : pkg.space ≃ pkg'.space :=
{ to_fun := pkg.compare pkg',
  inv_fun := pkg'.compare pkg,
  left_inv := congr_fun (pkg'.inverse_compare pkg),
  right_inv := congr_fun (pkg.inverse_compare pkg') }

lemma uniform_continuous_compare_equiv : uniform_continuous (pkg.compare_equiv pkg') :=
pkg.uniform_continuous_compare pkg'

lemma uniform_continuous_compare_equiv_symm : uniform_continuous (pkg.compare_equiv pkg').symm :=
pkg'.uniform_continuous_compare pkg

end compare

section prod
variables (pkg' : abstract_completion β)
local notation `hatβ` := pkg'.space
local notation `ι'` := pkg'.coe

/-- Products of completions -/
protected def prod : abstract_completion (α × β) :=
{ space := hatα × hatβ,
  coe := λ p, ⟨ι p.1, ι' p.2⟩,
  uniform_struct := prod.uniform_space,
  complete := by apply_instance,
  separation := by apply_instance,
  uniform_inducing := uniform_inducing.prod pkg.uniform_inducing pkg'.uniform_inducing,
  dense := pkg.dense.prod_map pkg'.dense }
end prod



section extension₂
variables (pkg' : abstract_completion β)
local notation `hatβ` := pkg'.space
local notation `ι'` := pkg'.coe

variables {γ : Type*} [uniform_space γ]

open function

/-- Extend two variable map to completions. -/
protected def extend₂ (f : α → β → γ) : hatα → hatβ → γ :=
curry $ (pkg.prod pkg').extend (uncurry f)

variables [separated_space γ] {f : α → β → γ}

lemma extension₂_coe_coe (hf : uniform_continuous $ uncurry f) (a : α) (b : β) :
  pkg.extend₂ pkg' f (ι a) (ι' b) = f a b :=
show (pkg.prod pkg').extend (uncurry f) ((pkg.prod pkg').coe (a, b)) = uncurry f (a, b),
  from (pkg.prod pkg').extend_coe hf _

variables [complete_space γ] (f)

lemma uniform_continuous_extension₂ : uniform_continuous₂ (pkg.extend₂ pkg' f) :=
begin
  rw [uniform_continuous₂_def, abstract_completion.extend₂, uncurry_curry],
  apply uniform_continuous_extend
end

end extension₂

section map₂
variables (pkg' : abstract_completion β)
local notation `hatβ` := pkg'.space
local notation `ι'` := pkg'.coe

variables {γ : Type*} [uniform_space γ] (pkg'' : abstract_completion γ)
local notation `hatγ` := pkg''.space
local notation `ι''` := pkg''.coe

local notation f `∘₂` g := bicompr f g

/-- Lift two variable maps to completions. -/
protected def map₂ (f : α → β → γ) : hatα → hatβ → hatγ :=
pkg.extend₂ pkg' (pkg''.coe ∘₂ f)

lemma uniform_continuous_map₂ (f : α → β → γ) : uniform_continuous₂ (pkg.map₂ pkg' pkg'' f) :=
pkg.uniform_continuous_extension₂ pkg' _

lemma continuous_map₂ {δ} [topological_space δ] {f : α → β → γ}
  {a : δ → hatα} {b : δ → hatβ} (ha : continuous a) (hb : continuous b) :
  continuous (λd:δ, pkg.map₂ pkg' pkg'' f (a d) (b d)) :=
((pkg.uniform_continuous_map₂ pkg' pkg'' f).continuous.comp (continuous.prod_mk ha hb) : _)

lemma map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : uniform_continuous₂ f) :
  pkg.map₂ pkg' pkg'' f (ι a) (ι' b) = ι'' (f a b) :=
pkg.extension₂_coe_coe pkg' (pkg''.uniform_continuous_coe.comp hf) a b

end map₂
end abstract_completion
