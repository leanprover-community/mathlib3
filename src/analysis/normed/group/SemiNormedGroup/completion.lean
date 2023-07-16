/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
import analysis.normed.group.SemiNormedGroup
import category_theory.preadditive.additive_functor
import analysis.normed.group.hom_completion

/-!
# Completions of normed groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains an API for completions of seminormed groups (basic facts about
objects and morphisms).

## Main definitions

- `SemiNormedGroup.Completion : SemiNormedGroup ⥤ SemiNormedGroup` : the completion of a
  seminormed group (defined as a functor on `SemiNormedGroup` to itself).
- `SemiNormedGroup.Completion.lift (f : V ⟶ W) : (Completion.obj V ⟶ W)` : a normed group hom
  from `V` to complete `W` extends ("lifts") to a seminormed group hom from the completion of
  `V` to `W`.

## Projects

1. Construct the category of complete seminormed groups, say `CompleteSemiNormedGroup`
  and promote the `Completion` functor below to a functor landing in this category.
2. Prove that the functor `Completion : SemiNormedGroup ⥤ CompleteSemiNormedGroup`
  is left adjoint to the forgetful functor.

-/

noncomputable theory

universe u

open uniform_space mul_opposite category_theory normed_add_group_hom

namespace SemiNormedGroup

/-- The completion of a seminormed group, as an endofunctor on `SemiNormedGroup`. -/
@[simps]
def Completion : SemiNormedGroup.{u} ⥤ SemiNormedGroup.{u} :=
{ obj := λ V, SemiNormedGroup.of (completion V),
  map := λ V W f, f.completion,
  map_id' := λ V, completion_id,
  map_comp' := λ U V W f g, (completion_comp f g).symm }

instance Completion_complete_space {V : SemiNormedGroup} : complete_space (Completion.obj V) :=
completion.complete_space _

/-- The canonical morphism from a seminormed group `V` to its completion. -/
@[simps]
def Completion.incl {V : SemiNormedGroup} : V ⟶ Completion.obj V :=
{ to_fun := λ v, (v : completion V),
  map_add' := completion.coe_add,
  bound' := ⟨1, λ v, by simp⟩ }

lemma Completion.norm_incl_eq {V : SemiNormedGroup} {v : V} : ‖Completion.incl v‖ = ‖v‖ := by simp

lemma Completion.map_norm_noninc {V W : SemiNormedGroup} {f : V ⟶ W} (hf : f.norm_noninc) :
  (Completion.map f).norm_noninc :=
normed_add_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.2 $
  (normed_add_group_hom.norm_completion f).le.trans $
  normed_add_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.1 hf

/-- Given a normed group hom `V ⟶ W`, this defines the associated morphism
from the completion of `V` to the completion of `W`.
The difference from the definition obtained from the functoriality of completion is in that the
map sending a morphism `f` to the associated morphism of completions is itself additive. -/
def Completion.map_hom (V W : SemiNormedGroup.{u}) :
  (V ⟶ W) →+ (Completion.obj V ⟶ Completion.obj W) :=
add_monoid_hom.mk' (category_theory.functor.map Completion) $ λ f g,
  f.completion_add g

@[simp] lemma Completion.map_zero (V W : SemiNormedGroup) : Completion.map (0 : V ⟶ W) = 0 :=
(Completion.map_hom V W).map_zero

instance : preadditive SemiNormedGroup.{u} :=
{ hom_group := λ P Q, infer_instance,
  add_comp' := by { intros, ext,
    simp only [normed_add_group_hom.add_apply, category_theory.comp_apply, map_add] },
  comp_add' := by { intros, ext,
    simp only [normed_add_group_hom.add_apply, category_theory.comp_apply, map_add] } }

instance : functor.additive Completion :=
{ map_add' := λ X Y, (Completion.map_hom _ _).map_add }

/-- Given a normed group hom `f : V → W` with `W` complete, this provides a lift of `f` to
the completion of `V`. The lemmas `lift_unique` and `lift_comp_incl` provide the api for the
universal property of the completion. -/
def Completion.lift {V W : SemiNormedGroup} [complete_space W] [separated_space W] (f : V ⟶ W) :
  Completion.obj V ⟶ W :=
{ to_fun := f.extension,
  map_add' := f.extension.to_add_monoid_hom.map_add',
  bound' := f.extension.bound' }

lemma Completion.lift_comp_incl {V W : SemiNormedGroup} [complete_space W] [separated_space W]
  (f : V ⟶ W) : Completion.incl ≫ (Completion.lift f) = f :=
by { ext, apply normed_add_group_hom.extension_coe }

lemma Completion.lift_unique {V W : SemiNormedGroup} [complete_space W] [separated_space W]
  (f : V ⟶ W) (g : Completion.obj V ⟶ W) : Completion.incl ≫ g = f → g = Completion.lift f :=
λ h, (normed_add_group_hom.extension_unique _ (λ v, ((ext_iff.1 h) v).symm)).symm

end SemiNormedGroup
