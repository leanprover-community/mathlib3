/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.basic
import topology.local_at_target

/-!
# Universally closed morphism

A morphism of schemes `f : X ⟶ Y` is universally closed if `X ×[Y] Y' ⟶ Y'` is a closed map
for all base change `Y' ⟶ Y`.

We show that being universally closed is local at the target, and is stable under compositions and
base changes.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universes v u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

open category_theory.morphism_property
open algebraic_geometry.morphism_property (topologically)

/--
A morphism of schemes `f : X ⟶ Y` is universally closed if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) a closed map.
-/
@[mk_iff]
class universally_closed (f : X ⟶ Y) : Prop :=
(out : universally (topologically @is_closed_map) f)

lemma universally_closed_eq :
  @universally_closed = universally (topologically @is_closed_map) :=
begin
  ext X Y f, rw universally_closed_iff
end

lemma universally_closed_respects_iso :
  respects_iso @universally_closed :=
universally_closed_eq.symm ▸ universally_respects_iso (topologically @is_closed_map)

lemma universally_closed_stable_under_base_change :
  stable_under_base_change @universally_closed :=
universally_closed_eq.symm ▸ universally_stable_under_base_change (topologically @is_closed_map)

lemma universally_closed_stable_under_composition :
  stable_under_composition @universally_closed :=
begin
  rw universally_closed_eq,
  exact stable_under_composition.universally (λ X Y Z f g hf hg, is_closed_map.comp hg hf),
end

instance universally_closed_type_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : universally_closed f] [hg : universally_closed g] :
  universally_closed (f ≫ g) :=
universally_closed_stable_under_composition f g hf hg

instance universally_closed_fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
  [hg : universally_closed g] :
  universally_closed (pullback.fst : pullback f g ⟶ _) :=
universally_closed_stable_under_base_change.fst f g hg

instance universally_closed_snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
  [hf : universally_closed f] :
  universally_closed (pullback.snd : pullback f g ⟶ _) :=
universally_closed_stable_under_base_change.snd f g hf

lemma morphism_restrict_base {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) :
  ⇑(f ∣_ U).1.base = U.1.restrict_preimage f.1 :=
funext (λ x, subtype.ext $ morphism_restrict_base_coe f U x)

lemma universally_closed_is_local_at_target :
  property_is_local_at_target @universally_closed :=
begin
  rw universally_closed_eq,
  apply universally_is_local_at_target_of_morphism_restrict,
  { exact stable_under_composition.respects_iso (λ X Y Z f g hf hg, is_closed_map.comp hg hf)
      (λ X Y f, (Top.homeo_of_iso (Scheme.forget_to_Top.map_iso f)).is_closed_map) },
  { intros X Y f ι U hU H,
    simp_rw [topologically, morphism_restrict_base] at H,
    exact (is_closed_map_iff_is_closed_map_of_supr_eq_top hU).mpr H }
end

lemma universally_closed.open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} Y) :
  universally_closed f ↔
    (∀ i, universally_closed (pullback.snd : pullback f (𝒰.map i) ⟶ _)) :=
universally_closed_is_local_at_target.open_cover_iff f 𝒰

end algebraic_geometry
