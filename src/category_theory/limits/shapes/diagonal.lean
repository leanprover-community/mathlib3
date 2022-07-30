/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.kernel_pair

/-!
# The diagonal object of a morphism.

We provide various API and isomorphisms considering the diagonal object `Δ_{Y/X} := pullback f f`
of a morphism `f : X ⟶ Y`.

-/

open category_theory

noncomputable theory

namespace category_theory.limits

variables {C : Type*} [category C] {X Y Z : C}

namespace pullback

section diagonal

variables (f : X ⟶ Y) [has_pullback f f]

/-- The diagonal object of a morphism `f : X ⟶ Y` is `Δ_{X/Y} := pullback f f`. -/
abbreviation diagonal_obj : C := pullback f f

/-- The diagonal morphism `X ⟶ Δ_{X/Y}` for a morphism `f : X ⟶ Y`. -/
def diagonal : X ⟶ diagonal_obj f :=
pullback.lift (𝟙 _) (𝟙 _) rfl

@[simp, reassoc] lemma diagonal_fst : diagonal f ≫ pullback.fst = 𝟙 _ :=
pullback.lift_fst _ _ _

@[simp, reassoc] lemma diagonal_snd : diagonal f ≫ pullback.snd = 𝟙 _ :=
pullback.lift_snd _ _ _

instance : split_mono (diagonal f) :=
⟨pullback.fst, diagonal_fst f⟩

instance : split_epi (pullback.fst : pullback f f ⟶ X) :=
⟨diagonal f, diagonal_fst f⟩

instance : split_epi (pullback.snd : pullback f f ⟶ X) :=
⟨diagonal f, diagonal_snd f⟩

instance [mono f] : is_iso (diagonal f) :=
begin
  rw (is_iso.inv_eq_of_inv_hom_id (diagonal_fst f)).symm,
  apply_instance
end

/-- The two projections `Δ_{X/Y} ⟶ X` forms a kernel pair for `f : X ⟶ Y`. -/
def diagonal_is_kernel_pair :
  is_kernel_pair f (pullback.fst : diagonal_obj f ⟶ _) pullback.snd :=
⟨pullback.condition, pullback_is_pullback _ _⟩

end diagonal

end pullback

variable [has_pullbacks C]

open pullback

section

variables {U V₁ V₂ : C} (f : X ⟶ Y) (i : U ⟶ Y)
variables (i₁ : V₁ ⟶ pullback f i) (i₂ : V₂ ⟶ pullback f i)

@[simp, reassoc]
lemma pullback_diagonal_map_snd_fst_fst :
  (pullback.snd : pullback (diagonal f) (map (i₁ ≫ snd) (i₂ ≫ snd) f f (i₁ ≫ fst) (i₂ ≫ fst) i
    (by simp [condition]) (by simp [condition])) ⟶ _) ≫ fst ≫ i₁ ≫ fst = pullback.fst :=
begin
  conv_rhs { rw ← category.comp_id pullback.fst },
  rw [← diagonal_fst f, pullback.condition_assoc, pullback.lift_fst]
end

@[simp, reassoc]
lemma pullback_diagonal_map_snd_snd_fst :
  (pullback.snd : pullback (diagonal f) (map (i₁ ≫ snd) (i₂ ≫ snd) f f (i₁ ≫ fst) (i₂ ≫ fst) i
    (by simp [condition]) (by simp [condition])) ⟶ _) ≫ snd ≫ i₂ ≫ fst = pullback.fst :=
begin
  conv_rhs { rw ← category.comp_id pullback.fst },
  rw [← diagonal_snd f, pullback.condition_assoc, pullback.lift_snd]
end

variable [has_pullback i₁ i₂]

/--
This iso witnesses the fact that
given `f : X ⟶ Y`, `i : U ⟶ Y`, and `i₁ : V₁ ⟶ X ×[Y] U`, `i₂ : V₂ ⟶ X ×[Y] U`, the diagram

V₁ ×[X ×[Y] U] V₂ ⟶ V₁ ×[U] V₂
        |                 |
        |                 |
        ↓                 ↓
        X         ⟶  X ×[Y] X

is a pullback square.
-/
def pullback_diagonal_map_iso :
  pullback (diagonal f) (map (i₁ ≫ snd) (i₂ ≫ snd) f f (i₁ ≫ fst) (i₂ ≫ fst) i
    (by simp [condition]) (by simp [condition])) ≅ pullback i₁ i₂ :=
{ hom := pullback.lift (pullback.snd ≫ pullback.fst) (pullback.snd ≫ pullback.snd)
    begin
      ext; simp only [category.assoc, pullback.condition, pullback_diagonal_map_snd_fst_fst,
        pullback_diagonal_map_snd_snd_fst],
    end,
  inv := pullback.lift (pullback.fst ≫ i₁ ≫ pullback.fst) (pullback.map _ _ _ _ (𝟙 _) (𝟙 _)
      pullback.snd (category.id_comp _).symm (category.id_comp _).symm)
    begin
      ext; simp only [diagonal_fst, diagonal_snd, category.comp_id, pullback.condition_assoc,
        category.assoc, lift_fst, lift_fst_assoc, lift_snd, lift_snd_assoc],
    end,
  hom_inv_id' := by ext; simp only [category.id_comp, category.assoc, lift_fst_assoc,
    pullback_diagonal_map_snd_fst_fst, lift_fst, lift_snd, category.comp_id],
  inv_hom_id' := by ext; simp }

@[simp, reassoc]
lemma pullback_diagonal_map_iso_hom_fst :
  (pullback_diagonal_map_iso f i i₁ i₂).hom ≫ pullback.fst = pullback.snd ≫ pullback.fst :=
by { delta pullback_diagonal_map_iso, simp }

@[simp, reassoc]
lemma pullback_diagonal_map_iso_hom_snd :
  (pullback_diagonal_map_iso f i i₁ i₂).hom ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by { delta pullback_diagonal_map_iso, simp }

@[simp, reassoc]
lemma pullback_diagonal_map_iso_inv_fst :
  (pullback_diagonal_map_iso f i i₁ i₂).inv ≫ pullback.fst = pullback.fst ≫ i₁ ≫ pullback.fst :=
by { delta pullback_diagonal_map_iso, simp }

@[simp, reassoc]
lemma pullback_diagonal_map_iso_inv_snd_fst :
  (pullback_diagonal_map_iso f i i₁ i₂).inv ≫ pullback.snd ≫ pullback.fst = pullback.fst :=
by { delta pullback_diagonal_map_iso, simp }

@[simp, reassoc]
lemma pullback_diagonal_map_iso_inv_snd_snd :
  (pullback_diagonal_map_iso f i i₁ i₂).inv ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
by { delta pullback_diagonal_map_iso, simp }

end

section

variables {S T : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S)
variables [has_pullback i i] [has_pullback f g] [has_pullback (f ≫ i) (g ≫ i)]
variable [has_pullback (diagonal i) (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _)
    (category.comp_id _) (category.comp_id _))]

/--
This iso witnesses the fact that
given `f : X ⟶ T`, `g : Y ⟶ T`, and `i : T ⟶ S`, the diagram

X ×ₜ Y ⟶ X ×ₛ Y
   |         |
   |         |
   ↓         ↓
   T   ⟶ T ×ₛ T

is a pullback square.
-/
def pullback_diagonal_map_id_iso :
  pullback (diagonal i) (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _)
    (category.comp_id _) (category.comp_id _)) ≅ pullback f g :=
begin
  refine (as_iso $ pullback.map _ _ _ _ (𝟙 _) (pullback.congr_hom _ _).hom (𝟙 _) _ _) ≪≫
    pullback_diagonal_map_iso i (𝟙 _) (f ≫ inv pullback.fst) (g ≫ inv pullback.fst) ≪≫
      (as_iso $ pullback.map _ _ _ _ (𝟙 _) (𝟙 _) pullback.fst _ _),
  { rw [← category.comp_id pullback.snd, ← condition, category.assoc, is_iso.inv_hom_id_assoc] },
  { rw [← category.comp_id pullback.snd, ← condition, category.assoc, is_iso.inv_hom_id_assoc] },
  { rw [category.comp_id, category.id_comp] },
  { ext; simp },
  { apply_instance },
  { rw [category.assoc, category.id_comp, is_iso.inv_hom_id, category.comp_id] },
  { rw [category.assoc, category.id_comp, is_iso.inv_hom_id, category.comp_id] },
  { apply_instance },
end

@[simp, reassoc]
lemma pullback_diagonal_map_id_iso_hom_fst :
  (pullback_diagonal_map_id_iso f g i).hom ≫ pullback.fst = pullback.snd ≫ pullback.fst :=
by { delta pullback_diagonal_map_id_iso, simp }

@[simp, reassoc]
lemma pullback_diagonal_map_id_iso_hom_snd :
  (pullback_diagonal_map_id_iso f g i).hom ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by { delta pullback_diagonal_map_id_iso, simp }

@[simp, reassoc]
lemma pullback_diagonal_map_id_iso_inv_fst :
  (pullback_diagonal_map_id_iso f g i).inv ≫ pullback.fst = pullback.fst ≫ f :=
begin
  rw [iso.inv_comp_eq, ← category.comp_id pullback.fst, ← diagonal_fst i, pullback.condition_assoc],
  simp,
end

@[simp, reassoc]
lemma pullback_diagonal_map_id_iso_inv_snd_fst :
  (pullback_diagonal_map_id_iso f g i).inv ≫ pullback.snd ≫ pullback.fst = pullback.fst :=
by { rw iso.inv_comp_eq, simp }

@[simp, reassoc]
lemma pullback_diagonal_map_id_iso_inv_snd_snd :
  (pullback_diagonal_map_id_iso f g i).inv ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
by { rw iso.inv_comp_eq, simp }

lemma pullback.diagonal_comp (f : X ⟶ Y) (g : Y ⟶ Z) [has_pullback f f] [has_pullback g g]
  [has_pullback (f ≫ g) (f ≫ g)] :
  diagonal (f ≫ g) = diagonal f ≫ (pullback_diagonal_map_id_iso f f g).inv ≫ pullback.snd :=
by ext; simp

/-- The diagonal object of `X ×[Z] Y ⟶ X` is isomorphic to `Δ_{Y/Z} ×[Z] X`. -/
def diagonal_obj_pullback_fst_iso {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  diagonal_obj (pullback.fst : pullback f g ⟶ X) ≅
    pullback (pullback.snd ≫ g : diagonal_obj g ⟶ Z) f :=
pullback_right_pullback_fst_iso _ _ _ ≪≫ pullback.congr_hom pullback.condition rfl ≪≫
  pullback_assoc _ _ _ _ ≪≫ pullback_symmetry _ _ ≪≫ pullback.congr_hom pullback.condition rfl

@[simp, reassoc] lemma diagonal_obj_pullback_fst_iso_hom_fst_fst {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) :
  (diagonal_obj_pullback_fst_iso f g).hom ≫ pullback.fst ≫ pullback.fst =
    pullback.fst ≫ pullback.snd :=
by { delta diagonal_obj_pullback_fst_iso, simp }

@[simp, reassoc] lemma diagonal_obj_pullback_fst_iso_hom_fst_snd {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) :
  (diagonal_obj_pullback_fst_iso f g).hom ≫ pullback.fst ≫ pullback.snd =
    pullback.snd ≫ pullback.snd :=
by { delta diagonal_obj_pullback_fst_iso, simp }

@[simp, reassoc] lemma diagonal_obj_pullback_fst_iso_hom_snd {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) :
  (diagonal_obj_pullback_fst_iso f g).hom ≫ pullback.snd = pullback.fst ≫ pullback.fst :=
by { delta diagonal_obj_pullback_fst_iso, simp }

@[simp, reassoc] lemma diagonal_obj_pullback_fst_iso_inv_fst_fst {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) :
  (diagonal_obj_pullback_fst_iso f g).inv ≫ pullback.fst ≫ pullback.fst =
    pullback.snd :=
by { delta diagonal_obj_pullback_fst_iso, simp }

@[simp, reassoc] lemma diagonal_obj_pullback_fst_iso_inv_fst_snd {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) :
  (diagonal_obj_pullback_fst_iso f g).inv ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst :=
by { delta diagonal_obj_pullback_fst_iso, simp }

@[simp, reassoc] lemma diagonal_obj_pullback_fst_iso_inv_snd_fst {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) :
  (diagonal_obj_pullback_fst_iso f g).inv ≫ pullback.snd ≫ pullback.fst = pullback.snd :=
by { delta diagonal_obj_pullback_fst_iso, simp }

@[simp, reassoc] lemma diagonal_obj_pullback_fst_iso_inv_snd_snd {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) :
  (diagonal_obj_pullback_fst_iso f g).inv ≫ pullback.snd ≫ pullback.snd =
    pullback.fst ≫ pullback.snd :=
by { delta diagonal_obj_pullback_fst_iso, simp }

lemma diagonal_pullback_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  diagonal (pullback.fst : pullback f g ⟶ _) =
    (pullback_symmetry _ _).hom ≫ ((base_change f).map
      (over.hom_mk (diagonal g) (by simp) : over.mk g ⟶ over.mk (pullback.snd ≫ g))).left ≫
    (diagonal_obj_pullback_fst_iso f g).inv :=
by ext; simp

end

/--
Given the following diagram with `S ⟶ S'` a monomorphism,

    X  ⟶ X'
      ↘      ↘
        S  ⟶ S'
      ↗      ↗
    Y  ⟶ Y'

This iso witnesses the fact that

      X ×[S] Y ⟶ (X' ×[S'] Y') ×[X'] X
          |                  |
          |                  |
          ↓                  ↓
(X' ×[S'] Y') ×[X'] X ⟶ X' ×[S'] Y'

is a pullback square. The diagonal map of this square is `pullback.map`.

-/
@[simps]
def pullback_fst_fst_iso {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
  (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
  (e₂ : g ≫ i₃ = i₂ ≫ g') [mono i₃] :
    pullback (pullback.fst : pullback (pullback.fst : pullback f' g' ⟶ _) i₁ ⟶ _)
      (pullback.fst : pullback (pullback.snd : pullback f' g' ⟶ _) i₂ ⟶ _) ≅ pullback f g :=
{ hom := pullback.lift (pullback.fst ≫ pullback.snd) (pullback.snd ≫ pullback.snd)
    begin
      rw [← cancel_mono i₃, category.assoc, category.assoc, category.assoc, category.assoc, e₁, e₂,
        ← pullback.condition_assoc, pullback.condition_assoc, pullback.condition,
        pullback.condition_assoc]
    end,
  inv := pullback.lift
    (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) pullback.fst (pullback.lift_fst _ _ _))
    (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) pullback.snd (pullback.lift_snd _ _ _))
    begin
      rw [pullback.lift_fst, pullback.lift_fst]
    end,
  hom_inv_id' := by ext; simp only [category.assoc, category.id_comp, lift_fst, lift_snd,
    lift_fst_assoc, lift_snd_assoc, condition, ← condition_assoc],
  inv_hom_id' := by ext; simp only [category.assoc, category.id_comp, lift_fst, lift_snd,
    lift_fst_assoc, lift_snd_assoc], }

lemma pullback_map_eq_pullback_fst_fst_iso_inv {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S)
  (f' : X' ⟶ S')
  (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
  (e₂ : g ≫ i₃ = i₂ ≫ g') [mono i₃] :
  pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ =
    (pullback_fst_fst_iso f g f' g' i₁ i₂ i₃ e₁ e₂).inv ≫ pullback.snd ≫ pullback.fst :=
begin
  ext; simp only [category.assoc, category.id_comp, lift_fst, lift_snd, lift_fst_assoc,
    lift_snd_assoc, pullback_fst_fst_iso_inv, ← pullback.condition, ← pullback.condition_assoc],
end

end category_theory.limits
