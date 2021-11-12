/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.sites.sheaf
import category_theory.limits.shapes.multiequalizer

/-!

# The plus construction for presheaves.

This file contains the construction of `P⁺`, for a presheaf `P : Cᵒᵖ ⥤ D`
where `C` is endowed with a grothendieck topology `J`.

See https://stacks.math.columbia.edu/tag/00W1 for details.

-/

namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits
open opposite

universes w v u
variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)
variables {D : Type w} [category.{max v u} D]

noncomputable theory

variables [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]
variables (P : Cᵒᵖ ⥤ D)

/-- The diagram whose colimit defines the values of `plus`. -/
@[simps]
def diagram (X : C) : (J.cover X)ᵒᵖ ⥤ D :=
{ obj := λ S, multiequalizer (S.unop.index P),
  map := λ S T f,
    multiequalizer.lift _ _ (λ I, multiequalizer.ι (S.unop.index P) (I.map f.unop)) $
      λ I, multiequalizer.condition (S.unop.index P) (I.map f.unop),
  map_id' := λ S, by { ext I, cases I, simpa },
  map_comp' := λ S T W f g, by { ext I, simpa } }

/-- A helper definition used to define the morphisms for `plus`. -/
@[simps]
def diagram_pullback {X Y : C} (f : X ⟶ Y) :
  J.diagram P Y ⟶ (J.pullback f).op ⋙ J.diagram P X :=
{ app := λ S, multiequalizer.lift _ _
    (λ I, multiequalizer.ι (S.unop.index P) I.base) $
      λ I, multiequalizer.condition (S.unop.index P) I.base,
  naturality' := λ S T f, by { ext, dsimp, simpa } }

variable [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]

/-- The plus construction, associating a presheaf to any presheaf.
See `plus` below for a functorial version.
-/
@[simps]
def plus_obj : Cᵒᵖ ⥤ D :=
{ obj := λ X, colimit (J.diagram P X.unop),
  map := λ X Y f, colim_map (J.diagram_pullback P f.unop) ≫ colimit.pre _ _,
  map_id' := begin
    intros X,
    ext S,
    dsimp,
    simp only [diagram_pullback_app, colimit.ι_pre,
      ι_colim_map_assoc, category.comp_id],
    let e := S.unop.pullback_id,
    dsimp only [functor.op, pullback_obj],
    erw [← colimit.w _ e.inv.op, ← category.assoc],
    convert category.id_comp _,
    ext I,
    dsimp,
    simp only [multiequalizer.lift_ι, category.id_comp, category.assoc],
    dsimp [cover.L.map, cover.L.base],
    cases I,
    congr,
    simp,
  end,
  map_comp' := begin
    intros X Y Z f g,
    ext S,
    dsimp,
    simp only [diagram_pullback_app, colimit.ι_pre_assoc,
      colimit.ι_pre, ι_colim_map_assoc, category.assoc],
    let e := S.unop.pullback_comp g.unop f.unop,
    dsimp only [functor.op, pullback_obj],
    erw [← colimit.w _ e.inv.op, ← category.assoc, ← category.assoc],
    congr' 1,
    ext I,
    dsimp,
    simp only [multiequalizer.lift_ι, category.assoc],
    cases I,
    dsimp only [cover.L.base, cover.L.map],
    congr' 2,
    simp,
  end }

/-- An auxiliary definition used in `plus` below. -/
@[simps]
def plus_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.plus_obj P ⟶ J.plus_obj Q :=
{ app := λ X, colim_map
  { app := λ S, multiequalizer.lift _ _
      (λ I, multiequalizer.ι (S.unop.index P) I ≫ η.app (op I.Y)) begin
        intros I,
        erw [category.assoc, category.assoc, ← η.naturality, ← η.naturality,
          ← category.assoc, ← category.assoc, multiequalizer.condition],
        refl,
      end,
    naturality' := λ S T e, by { dsimp, ext, simpa } },
  naturality' := begin
    intros X Y f,
    dsimp,
    ext,
    simp only [diagram_pullback_app, ι_colim_map, colimit.ι_pre_assoc,
      colimit.ι_pre, ι_colim_map_assoc, category.assoc],
    simp_rw ← category.assoc,
    congr' 1,
    ext,
    dsimp,
    simpa,
  end }

variable (D)

/-- The plus construction, a functor sending `P` to `J.plus_obj P`. -/
@[simps]
def plus_functor : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D :=
{ obj := λ P, J.plus_obj P,
  map := λ P Q η, J.plus_map η,
  map_id' := begin
    intros P,
    ext,
    dsimp,
    simp only [ι_colim_map, category.comp_id],
    convert category.id_comp _,
    ext,
    simp only [multiequalizer.lift_ι, category.id_comp],
    exact category.comp_id _,
  end,
  map_comp' := begin
    intros P Q R η γ,
    ext,
    dsimp,
    simp only [ι_colim_map, ι_colim_map_assoc],
    rw ← category.assoc,
    congr' 1,
    ext,
    dsimp,
    simp,
  end }

variable {D}

/-- The canonical map from `P` to `J.plus.obj P`.
See `to_plus` for a functorial version. -/
@[simps]
def to_plus : P ⟶ J.plus_obj P :=
{ app := λ X, cover.to_multiequalizer (⊤ : J.cover X.unop) P ≫
    colimit.ι (J.diagram P X.unop) (op ⊤),
  naturality' := begin
    intros X Y f,
    dsimp,
    delta cover.to_multiequalizer,
    simp only [diagram_pullback_app, colimit.ι_pre, ι_colim_map_assoc, category.assoc],
    dsimp only [functor.op, unop_op],
    let e : (J.pullback f.unop).obj ⊤ ⟶ ⊤ := hom_of_le (semilattice_inf_top.le_top _),
    rw [← colimit.w _ e.op, ← category.assoc, ← category.assoc, ← category.assoc],
    congr' 1,
    ext,
    dsimp,
    simp only [multiequalizer.lift_ι, category.assoc],
    dsimp [cover.L.base],
    simp,
  end }

variable (D)

/-- The natural transformation from the identity functor to `plus`. -/
@[simps]
def to_plus_nat_trans : (𝟭 (Cᵒᵖ ⥤ D)) ⟶ J.plus_functor D :=
{ app := λ P, J.to_plus P,
  naturality' := begin
    intros P Q η,
    ext,
    dsimp,
    delta cover.to_multiequalizer,
    simp only [ι_colim_map, category.assoc],
    simp_rw ← category.assoc,
    congr' 1,
    ext,
    dsimp,
    simp,
  end }

variable {D}

/-- `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺ -/
@[simp]
lemma plus_map_to_plus : J.plus_map (J.to_plus P) = J.to_plus (J.plus_obj P) :=
begin
  ext X S,
  dsimp,
  delta cover.to_multiequalizer,
  simp only [ι_colim_map],
  let e : S.unop ⟶ ⊤ := hom_of_le (semilattice_inf_top.le_top _),
  simp_rw [← colimit.w _ e.op, ← category.assoc],
  congr' 1,
  ext I,
  dsimp,
  simp only [diagram_pullback_app, colimit.ι_pre, multiequalizer.lift_ι,
    ι_colim_map_assoc, category.assoc],
  dsimp only [functor.op],
  let ee : (J.pullback (I.map e).f).obj S.unop ⟶ ⊤ := hom_of_le (semilattice_inf_top.le_top _),
  simp_rw [← colimit.w _ ee.op, ← category.assoc],
  congr' 1,
  ext II,
  dsimp,
  simp only [limit.lift_π, multifork.of_ι_π_app, multiequalizer.lift_ι, category.assoc],
  dsimp [multifork.of_ι],
  convert multiequalizer.condition (S.unop.index P)
    ⟨_, _, _, II.f, 𝟙 _, I.f, II.f ≫ I.f, I.hf, sieve.downward_closed _ I.hf _, by simp⟩,
  { cases I, refl },
  { dsimp [cover.index],
    erw [P.map_id, category.comp_id],
    refl }
end

end category_theory.grothendieck_topology
