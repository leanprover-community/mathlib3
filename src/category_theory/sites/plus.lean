/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.sites.sheaf

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
    dsimp [cover.arrow.map, cover.arrow.base],
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
    dsimp only [cover.arrow.base, cover.arrow.map],
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
    dsimp [cover.arrow.base],
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

/-- `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺` -/
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

lemma is_iso_to_plus_of_is_sheaf (hP : presheaf.is_sheaf J P) : is_iso (J.to_plus P) :=
begin
  rw presheaf.is_sheaf_iff_multiequalizer at hP,
  resetI,
  suffices : ∀ X, is_iso ((J.to_plus P).app X),
  { resetI, apply nat_iso.is_iso_of_is_iso_app },
  intros X, dsimp,
  suffices : is_iso (colimit.ι (J.diagram P X.unop) (op ⊤)),
  { resetI, apply is_iso.comp_is_iso },
  suffices : ∀ (S T : (J.cover X.unop)ᵒᵖ) (f : S ⟶ T), is_iso ((J.diagram P X.unop).map f),
  { resetI, apply is_iso_ι_of_is_initial (initial_op_of_terminal is_terminal_top) },
  intros S T e,
  have : S.unop.to_multiequalizer P ≫ (J.diagram P (X.unop)).map e =
    T.unop.to_multiequalizer P, by { ext, dsimp, simpa },
  have : (J.diagram P (X.unop)).map e = inv (S.unop.to_multiequalizer P) ≫
    T.unop.to_multiequalizer P, by simp [← this],
  rw this, apply_instance,
end

/-- The natural isomorphism between `P` and `P⁺` when `P` is a sheaf. -/
def iso_to_plus (hP : presheaf.is_sheaf J P) : P ≅ J.plus_obj P :=
by letI := is_iso_to_plus_of_is_sheaf J P hP; exact as_iso (J.to_plus P)

/-- Lift a morphism `P ⟶ Q` to `P⁺ ⟶ Q` when `Q` is a sheaf. -/
def plus_lift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) :
  J.plus_obj P ⟶ Q :=
J.plus_map η ≫ (J.iso_to_plus Q hQ).inv

lemma to_plus_plus_lift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) :
  J.to_plus P ≫ J.plus_lift η hQ = η :=
begin
  dsimp [plus_lift],
  rw ← category.assoc,
  rw iso.comp_inv_eq,
  dsimp only [iso_to_plus, as_iso],
  change (J.to_plus_nat_trans D).app _ ≫ _ = _,
  erw (J.to_plus_nat_trans D).naturality,
  refl,
end

lemma plus_lift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q)
  (γ : J.plus_obj P ⟶ Q) (hγ : J.to_plus P ≫ γ = η) : γ = J.plus_lift η hQ :=
begin
  dsimp only [plus_lift],
  symmetry,
  change (J.plus_functor D).map η ≫ _ = _,
  rw [iso.comp_inv_eq, ← hγ, (J.plus_functor D).map_comp],
  dsimp only [iso_to_plus, as_iso],
  change _ = (𝟭 _).map γ ≫ (J.to_plus_nat_trans D).app _,
  erw (J.to_plus_nat_trans D).naturality,
  congr' 1,
  dsimp only [plus_functor, to_plus_nat_trans],
  rw [J.plus_map_to_plus P],
end

lemma plus_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.plus_obj P ⟶ Q) (hQ : presheaf.is_sheaf J Q)
  (h : J.to_plus P ≫ η = J.to_plus P ≫ γ) : η = γ :=
begin
  have : γ = J.plus_lift (J.to_plus P ≫ γ) hQ,
  { apply plus_lift_unique, refl },
  rw this,
  apply plus_lift_unique, exact h
end

end category_theory.grothendieck_topology
