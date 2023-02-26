/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import topology.continuous_function.basic

/-!
# Cocompact continuous maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The type of *cocompact continuous maps* are those which tend to the cocompact filter on the
codomain along the cocompact filter on the domain. When the domain and codomain are Hausdorff, this
is equivalent to many other conditions, including that preimages of compact sets are compact. -/

universes u v w

open filter set

/-! ### Cocompact continuous maps -/

/-- A *cocompact continuous map* is a continuous function between topological spaces which
tends to the cocompact filter along the cocompact filter. Functions for which preimages of compact
sets are compact always satisfy this property, and the converse holds for cocompact continuous maps
when the codomain is Hausdorff (see `cocompact_map.tendsto_of_forall_preimage` and
`cocompact_map.is_compact_preimage`).

Cocompact maps thus generalise proper maps, with which they correspond when the codomain is
Hausdorff. -/
structure cocompact_map (α : Type u) (β : Type v) [topological_space α] [topological_space β]
  extends continuous_map α β : Type (max u v) :=
(cocompact_tendsto' : tendsto to_fun (cocompact α) (cocompact β))

section
set_option old_structure_cmd true

/-- `cocompact_map_class F α β` states that `F` is a type of cocompact continuous maps.

You should also extend this typeclass when you extend `cocompact_map`. -/
class cocompact_map_class (F : Type*) (α β : out_param $ Type*) [topological_space α]
  [topological_space β] extends continuous_map_class F α β :=
(cocompact_tendsto (f : F) : tendsto f (cocompact α) (cocompact β))

end

namespace cocompact_map_class

variables {F α β : Type*} [topological_space α] [topological_space β]
  [cocompact_map_class F α β]

instance : has_coe_t F (cocompact_map α β) := ⟨λ f, ⟨f, cocompact_tendsto f⟩⟩

end cocompact_map_class

export cocompact_map_class (cocompact_tendsto)

namespace cocompact_map

section basics
variables {α β γ δ : Type*} [topological_space α] [topological_space β] [topological_space γ]
  [topological_space δ]

instance : cocompact_map_class (cocompact_map α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_continuous := λ f, f.continuous_to_fun,
  cocompact_tendsto := λ f, f.cocompact_tendsto' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (cocompact_map α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma coe_to_continuous_fun {f : cocompact_map α β} :
  (f.to_continuous_map : α → β) = f := rfl

@[ext] lemma ext {f g : cocompact_map α β} (h : ∀ x, f x = g x) : f = g := fun_like.ext _ _ h

/-- Copy of a `cocompact_map` with a new `to_fun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : cocompact_map α β) (f' : α → β) (h : f' = f) : cocompact_map α β :=
{ to_fun := f',
  continuous_to_fun := by {rw h, exact f.continuous_to_fun},
  cocompact_tendsto' := by { simp_rw h, exact f.cocompact_tendsto' } }

@[simp]
lemma coe_copy (f : cocompact_map α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl

lemma copy_eq (f : cocompact_map α β) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

@[simp] lemma coe_mk (f : C(α, β)) (h : tendsto f (cocompact α) (cocompact β)) :
  ⇑(⟨f, h⟩ : cocompact_map α β) = f := rfl

section
variable (α)
/-- The identity as a cocompact continuous map. -/
protected def id : cocompact_map α α := ⟨continuous_map.id _, tendsto_id⟩
@[simp] lemma coe_id : ⇑(cocompact_map.id α) = id := rfl
end

instance : inhabited (cocompact_map α α) := ⟨cocompact_map.id α⟩

/-- The composition of cocompact continuous maps, as a cocompact continuous map. -/
def comp (f : cocompact_map β γ) (g : cocompact_map α β) : cocompact_map α γ :=
⟨f.to_continuous_map.comp g, (cocompact_tendsto f).comp (cocompact_tendsto g)⟩

@[simp] lemma coe_comp (f : cocompact_map β γ) (g : cocompact_map α β) :
  ⇑(comp f g) = f ∘ g := rfl

@[simp] lemma comp_apply (f : cocompact_map β γ) (g : cocompact_map α β) (a : α) :
  comp f g a = f (g a) := rfl

@[simp] lemma comp_assoc (f : cocompact_map γ δ) (g : cocompact_map β γ)
  (h : cocompact_map α β) : (f.comp g).comp h = f.comp (g.comp h) := rfl

@[simp] lemma id_comp (f : cocompact_map α β) : (cocompact_map.id _).comp f = f :=
ext $ λ _, rfl

@[simp] lemma comp_id (f : cocompact_map α β) : f.comp (cocompact_map.id _) = f :=
ext $ λ _, rfl

lemma tendsto_of_forall_preimage {f : α → β} (h : ∀ s, is_compact s → is_compact (f ⁻¹' s)) :
  tendsto f (cocompact α) (cocompact β) :=
λ s hs, match mem_cocompact.mp hs with ⟨t, ht, hts⟩ :=
  mem_map.mpr (mem_cocompact.mpr ⟨f ⁻¹' t, h t ht, by simpa using preimage_mono hts⟩) end

/-- If the codomain is Hausdorff, preimages of compact sets are compact under a cocompact
continuous map. -/
lemma is_compact_preimage [t2_space β] (f : cocompact_map α β) ⦃s : set β⦄ (hs : is_compact s) :
  is_compact (f ⁻¹' s) :=
begin
  obtain ⟨t, ht, hts⟩ := mem_cocompact'.mp (by simpa only [preimage_image_preimage, preimage_compl]
    using mem_map.mp (cocompact_tendsto f $ mem_cocompact.mpr ⟨s, hs, compl_subset_compl.mpr
    (image_preimage_subset f _)⟩)),
  exact is_compact_of_is_closed_subset ht (hs.is_closed.preimage $ map_continuous f)
    (by simpa using hts),
end

end basics

end cocompact_map

/-- A homemomorphism is a cocompact map. -/
@[simps] def homeomorph.to_cocompact_map
  {α β : Type*} [topological_space α] [topological_space β] (f : α ≃ₜ β) : cocompact_map α β :=
{ to_fun := f,
  continuous_to_fun := f.continuous,
  cocompact_tendsto' :=
  begin
    refine cocompact_map.tendsto_of_forall_preimage (λ K hK, _),
    erw K.preimage_equiv_eq_image_symm,
    exact hK.image f.symm.continuous,
  end }
