/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import category_theory.over
import category_theory.adjunction.opposites
import category_theory.limits.preserves.basic
import category_theory.limits.shapes.pullbacks
import category_theory.limits.creates
import category_theory.limits.comma

/-!
# Limits and colimits in the over and under categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Show that the forgetful functor `forget X : over X ⥤ C` creates colimits, and hence `over X` has
any colimits that `C` has (as well as the dual that `forget X : under X ⟶ C` creates limits).

Note that the folder `category_theory.limits.shapes.constructions.over` further shows that
`forget X : over X ⥤ C` creates connected limits (so `over X` has connected limits), and that
`over X` has `J`-indexed products if `C` has `J`-indexed wide pullbacks.

TODO: If `C` has binary products, then `forget X : over X ⥤ C` has a right adjoint.
-/
noncomputable theory

universes v u -- morphism levels before object levels. See note [category_theory universes].

open category_theory category_theory.limits

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]
variable {X : C}

namespace category_theory.over

instance has_colimit_of_has_colimit_comp_forget
  (F : J ⥤ over X) [i : has_colimit (F ⋙ forget X)] : has_colimit F :=
@@costructured_arrow.has_colimit _ _ _ _ i _

instance [has_colimits_of_shape J C] : has_colimits_of_shape J (over X) := {}
instance [has_colimits C] : has_colimits (over X) := ⟨infer_instance⟩

instance creates_colimits : creates_colimits (forget X) := costructured_arrow.creates_colimits

-- We can automatically infer that the forgetful functor preserves and reflects colimits.
example [has_colimits C] : preserves_colimits (forget X) := infer_instance
example : reflects_colimits (forget X) := infer_instance

lemma epi_left_of_epi [has_pushouts C] {f g : over X} (h : f ⟶ g) [epi h] : epi h.left :=
costructured_arrow.epi_left_of_epi _

lemma epi_iff_epi_left [has_pushouts C] {f g : over X} (h : f ⟶ g) : epi h ↔ epi h.left :=
costructured_arrow.epi_iff_epi_left _

section
variables [has_pullbacks C]

open tactic

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `over Y ⥤ over X`,
by pulling back a morphism along `f`. -/
@[simps]
def pullback {X Y : C} (f : X ⟶ Y) : over Y ⥤ over X :=
{ obj := λ g, over.mk (pullback.snd : pullback g.hom f ⟶ X),
  map := λ g h k,
    over.hom_mk
      (pullback.lift (pullback.fst ≫ k.left) pullback.snd (by simp [pullback.condition]))
      (by tidy) }

/-- `over.map f` is left adjoint to `over.pullback f`. -/
def map_pullback_adj {A B : C} (f : A ⟶ B) :
  over.map f ⊣ pullback f :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ g h,
  { to_fun := λ X, over.hom_mk (pullback.lift X.left g.hom (over.w X)) (pullback.lift_snd _ _ _),
    inv_fun := λ Y,
    begin
      refine over.hom_mk _ _,
      refine Y.left ≫ pullback.fst,
      dsimp,
      rw [← over.w Y, category.assoc, pullback.condition, category.assoc], refl,
    end,
    left_inv := λ X, by { ext, dsimp, simp, },
    right_inv := λ Y, begin
      ext, dsimp,
      simp only [pullback.lift_fst],
      dsimp,
      rw [pullback.lift_snd, ← over.w Y],
      refl,
    end } }

/-- pullback (𝟙 A) : over A ⥤ over A is the identity functor. -/
def pullback_id {A : C} : pullback (𝟙 A) ≅ 𝟭 _ :=
adjunction.right_adjoint_uniq
  (map_pullback_adj _)
  (adjunction.id.of_nat_iso_left over.map_id.symm)

/-- pullback commutes with composition (up to natural isomorphism). -/
def pullback_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
adjunction.right_adjoint_uniq
  (map_pullback_adj _)
  (((map_pullback_adj _).comp (map_pullback_adj _)).of_nat_iso_left
    (over.map_comp _ _).symm)

instance pullback_is_right_adjoint {A B : C} (f : A ⟶ B) :
  is_right_adjoint (pullback f) :=
⟨_, map_pullback_adj f⟩

end

end category_theory.over

namespace category_theory.under

instance has_limit_of_has_limit_comp_forget
  (F : J ⥤ under X) [i : has_limit (F ⋙ forget X)] : has_limit F :=
@@structured_arrow.has_limit _ _ _ _ i _

instance [has_limits_of_shape J C] : has_limits_of_shape J (under X) := {}
instance [has_limits C] : has_limits (under X) := ⟨infer_instance⟩

lemma mono_right_of_mono [has_pullbacks C] {f g : under X} (h : f ⟶ g) [mono h] : mono h.right :=
structured_arrow.mono_right_of_mono _

lemma mono_iff_mono_right [has_pullbacks C] {f g : under X} (h : f ⟶ g) : mono h ↔ mono h.right :=
structured_arrow.mono_iff_mono_right _

instance creates_limits : creates_limits (forget X) := structured_arrow.creates_limits

-- We can automatically infer that the forgetful functor preserves and reflects limits.
example [has_limits C] : preserves_limits (forget X) := infer_instance
example : reflects_limits (forget X) := infer_instance

section
variables [has_pushouts C]

/-- When `C` has pushouts, a morphism `f : X ⟶ Y` induces a functor `under X ⥤ under Y`,
by pushing a morphism forward along `f`. -/
@[simps]
def pushout {X Y : C} (f : X ⟶ Y) : under X ⥤ under Y :=
{ obj := λ g, under.mk (pushout.inr : Y ⟶ pushout g.hom f),
  map := λ g h k,
    under.hom_mk
      (pushout.desc (k.right ≫ pushout.inl) pushout.inr (by { simp [←pushout.condition], }))
      (by tidy) }

end

end category_theory.under
