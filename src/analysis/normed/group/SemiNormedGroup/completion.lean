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

This file contains an API for completions of seminormed groups (basic facts about
objects and morphisms).

## Main definitions

- `SemiNormedGroup.Completion` : the completion of a seminormed group (defined as a functor on
  `SemiNormedGroup`).
- `SemiNormedGroup.Completion.lift` : a normed group hom from `V` to complete `W` extends ("lifts")
  to a seminormed group from the completion of `V` to `W`.

-/

noncomputable theory

universe u

namespace SemiNormedGroup
open uniform_space opposite category_theory normed_group_hom

/-- The completion of a seminormed group, as an endofunctor on `SemiNormedGroup`. -/
@[simps]
def Completion : SemiNormedGroup.{u} ⥤ SemiNormedGroup.{u} :=
{ obj := λ V, SemiNormedGroup.of (completion V),
  map := λ V W f, normed_group_hom.completion f,
  map_id' := λ V, completion_id,
  map_comp' := λ U V W f g, (completion_comp f g).symm }

instance Completion_complete_space {V : SemiNormedGroup} : complete_space (Completion.obj V) :=
begin
  change complete_space (completion V),
  apply_instance
end

/-- The canonical morphism from a seminormed group `V` to its completion. -/
@[simps]
def incl {V : SemiNormedGroup} : V ⟶ Completion.obj V :=
{ to_fun := λ v, (v : completion V),
  map_add' := completion.coe_add,
  bound' := ⟨1, λ v, by simp⟩ }

lemma norm_incl_eq {V : SemiNormedGroup} {v : V} : ∥incl v∥ = ∥v∥ := by simp

lemma Completion_map_norm_noninc {V W : SemiNormedGroup} {f : V ⟶ W} (hf : f.norm_noninc) :
  (Completion.map f).norm_noninc :=
normed_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.2 $ le_trans
  (normed_group_hom.norm_completion f).le $
  normed_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.1 hf

/-- Given a normed group hom `V ⟶ W`, this defines the associated morphism
from the completion of `V` to the completion of `W`.
The difference from the definition obtained from the functoriality of completion is in that the
map sending a morphism `f` to the associated morphism of completions is itself additive. -/
def Completion.map_hom (V W : SemiNormedGroup.{u}) :
  (V ⟶ W) →+ (Completion.obj V ⟶ Completion.obj W) :=
add_monoid_hom.mk' (category_theory.functor.map Completion) $ λ f g,
  normed_group_hom.completion_add f g


@[simp] lemma Completion.map_zero (V W : SemiNormedGroup) : Completion.map (0 : V ⟶ W) = 0 :=
(Completion.map_hom V W).map_zero

instance : preadditive SemiNormedGroup.{u} :=
{ hom_group := λ P Q, infer_instance,
  add_comp' := by { intros, ext,
    simp only [normed_group_hom.add_apply, category_theory.comp_apply, normed_group_hom.map_add] },
  comp_add' := by { intros, ext,
    simp only [normed_group_hom.add_apply, category_theory.comp_apply, normed_group_hom.map_add] } }

instance : functor.additive Completion :=
{ map_zero' := Completion.map_zero,
  map_add' := λ X Y, (Completion.map_hom _ _).map_add }

/-- Given a normed group hom `f : V → W` with `W` complete, this provides a lift of `f` to
the completion of `V`. The lemmas `lift_unique` and `lift_comp_incl` provide the api for the
universal property of the completion. -/
def Completion.lift {V W : SemiNormedGroup} [complete_space W] [separated_space W] (f : V ⟶ W) :
  Completion.obj V ⟶ W :=
{ to_fun := completion.extension f,
  map_add' := λ x y, begin
    refine completion.induction_on₂ x y (is_closed_eq _ _) (λ x y, _),
    { exact continuous.comp completion.continuous_extension continuous_add },
    { exact continuous.add (continuous.comp completion.continuous_extension continuous_fst)
      (continuous.comp completion.continuous_extension continuous_snd) },
    { rw [← completion.coe_add],
      repeat {rw completion.extension_coe},
      { exact normed_group_hom.map_add _ _ _ },
      all_goals {exact normed_group_hom.uniform_continuous _} }
  end,
  bound' := begin
    rcases f.bound with ⟨c, hc, h⟩,
    refine ⟨c, λ v, completion.induction_on v (is_closed_le _ _) (λ a, _)⟩,
    { exact continuous.comp continuous_norm completion.continuous_extension },
    { exact continuous.mul continuous_const continuous_norm },
    { rw completion.extension_coe,
      { change _ ≤ c * ∥incl _∥,
        simpa using h a },
      { exact normed_group_hom.uniform_continuous _ }}
  end }

lemma lift_comp_incl {V W : SemiNormedGroup} [complete_space W] [separated_space W] (f : V ⟶ W) :
  incl ≫ (Completion.lift f) = f :=
by {ext, exact completion.extension_coe (normed_group_hom.uniform_continuous _) _ }

lemma lift_unique {V W : SemiNormedGroup} [complete_space W] [separated_space W] (f : V ⟶ W)
  (g : Completion.obj V ⟶ W) : incl ≫ g = f → g = Completion.lift f :=
begin
  intros h,
  ext,
  simpa [← completion.extension_unique f.uniform_continuous g.uniform_continuous
    (λ a, ((ext_iff.1 h) a).symm)],
end

end SemiNormedGroup
