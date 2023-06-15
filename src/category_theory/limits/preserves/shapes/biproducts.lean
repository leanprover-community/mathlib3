/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.shapes.biproducts
import category_theory.limits.preserves.shapes.zero

/-!
# Preservation of biproducts

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the image of a (binary) bicone under a functor that preserves zero morphisms and define
classes `preserves_biproduct` and `preserves_binary_biproduct`. We then

* show that a functor that preserves biproducts of a two-element type preserves binary biproducts,
* construct the comparison morphisms between the image of a biproduct and the biproduct of the
  images and show that the biproduct is preserved if one of them is an isomorphism,
* give the canonical isomorphism between the image of a biproduct and the biproduct of the images
  in case that the biproduct is preserved.

-/

universes w₁ w₂ v₁ v₂ u₁ u₂

noncomputable theory

open category_theory
open category_theory.limits

namespace category_theory

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

section has_zero_morphisms
variables [has_zero_morphisms C] [has_zero_morphisms D]

namespace functor

section map
variables (F : C ⥤ D) [preserves_zero_morphisms F]

section bicone
variables {J : Type w₁}

/-- The image of a bicone under a functor. -/
@[simps]
def map_bicone {f : J → C} (b : bicone f) : bicone (F.obj ∘ f) :=
{ X := F.obj b.X,
  π := λ j, F.map (b.π j),
  ι := λ j, F.map (b.ι j),
  ι_π := λ j j',
  begin
    rw ← F.map_comp,
    split_ifs,
    { subst h,
      simp only [bicone_ι_π_self, category_theory.functor.map_id, eq_to_hom_refl] },
    { rw [bicone_ι_π_ne _ h, F.map_zero] }
  end }

lemma map_bicone_whisker {K : Type w₂} {g : K ≃ J} {f : J → C} (c : bicone f) :
  F.map_bicone (c.whisker g) = (F.map_bicone c).whisker g := rfl

end bicone

/-- The image of a binary bicone under a functor. -/
@[simps]
def map_binary_bicone {X Y : C} (b : binary_bicone X Y) : binary_bicone (F.obj X) (F.obj Y) :=
{ X := F.obj b.X,
  fst := F.map b.fst,
  snd := F.map b.snd,
  inl := F.map b.inl,
  inr := F.map b.inr,
  inl_fst' := by rw [← F.map_comp, b.inl_fst, F.map_id],
  inl_snd' := by rw [← F.map_comp, b.inl_snd, F.map_zero],
  inr_fst' := by rw [← F.map_comp, b.inr_fst, F.map_zero],
  inr_snd' := by rw [← F.map_comp, b.inr_snd, F.map_id] }

end map

end functor

open category_theory.functor

namespace limits

section bicone
variables {J : Type w₁} {K : Type w₂}

/-- A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over `f` to a
    bilimit bicone over `F.obj ∘ f`. -/
class preserves_biproduct (f : J → C) (F : C ⥤ D) [preserves_zero_morphisms F] :=
(preserves : Π {b : bicone f}, b.is_bilimit → (F.map_bicone b).is_bilimit)

/-- A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over `f` to a
    bilimit bicone over `F.obj ∘ f`. -/
def is_bilimit_of_preserves {f : J → C} (F : C ⥤ D) [preserves_zero_morphisms F]
  [preserves_biproduct f F] {b : bicone f} (hb : b.is_bilimit) : (F.map_bicone b).is_bilimit :=
preserves_biproduct.preserves hb

variables (J)

/-- A functor `F` preserves biproducts of shape `J` if it preserves biproducts of `f` for every
    `f : J → C`. -/
class preserves_biproducts_of_shape (F : C ⥤ D) [preserves_zero_morphisms F] :=
(preserves : Π {f : J → C}, preserves_biproduct f F)

attribute [instance, priority 100] preserves_biproducts_of_shape.preserves

end bicone

/-- A functor `F` preserves finite biproducts if it preserves biproducts of shape `J` whenever
    `J` is a fintype. -/
class preserves_finite_biproducts (F : C ⥤ D) [preserves_zero_morphisms F] :=
(preserves : Π {J : Type} [fintype J], preserves_biproducts_of_shape J F)

attribute [instance, priority 100] preserves_finite_biproducts.preserves

/-- A functor `F` preserves biproducts if it preserves biproducts of any shape `J` of size `w`.
    The usual notion of preservation of biproducts is recovered by choosing `w` to be the universe
    of the morphisms of `C`. -/
class preserves_biproducts (F : C ⥤ D) [preserves_zero_morphisms F] :=
(preserves : Π {J : Type w₁}, preserves_biproducts_of_shape J F)

attribute [instance, priority 100] preserves_biproducts.preserves

/-- Preserving biproducts at a bigger universe level implies preserving biproducts at a
smaller universe level. -/
def preserves_biproducts_shrink (F : C ⥤ D) [preserves_zero_morphisms F]
  [hp : preserves_biproducts.{max w₁ w₂} F] : preserves_biproducts.{w₁} F :=
⟨λ J, ⟨λ f, ⟨λ b ib, ((F.map_bicone b).whisker_is_bilimit_iff _).to_fun
  (is_bilimit_of_preserves F ((b.whisker_is_bilimit_iff equiv.ulift.{w₂}).inv_fun ib))⟩⟩⟩

@[priority 100]
instance preserves_finite_biproducts_of_preserves_biproducts (F : C ⥤ D)
  [preserves_zero_morphisms F] [preserves_biproducts.{w₁} F] : preserves_finite_biproducts F :=
{ preserves := λ J _, by letI := preserves_biproducts_shrink.{0} F; apply_instance }

/-- A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilimit bicone over
    `X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`. -/
class preserves_binary_biproduct (X Y : C) (F : C ⥤ D) [preserves_zero_morphisms F] :=
(preserves : Π {b : binary_bicone X Y}, b.is_bilimit → (F.map_binary_bicone b).is_bilimit)

/-- A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilimit bicone over
    `X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`. -/
def is_binary_bilimit_of_preserves {X Y : C} (F : C ⥤ D) [preserves_zero_morphisms F]
  [preserves_binary_biproduct X Y F] {b : binary_bicone X Y} (hb : b.is_bilimit) :
  (F.map_binary_bicone b).is_bilimit :=
preserves_binary_biproduct.preserves hb

/-- A functor `F` preserves binary biproducts if it preserves the binary biproduct of `X` and `Y`
    for all `X` and `Y`. -/
class preserves_binary_biproducts (F : C ⥤ D) [preserves_zero_morphisms F] :=
(preserves : Π {X Y : C}, preserves_binary_biproduct X Y F . tactic.apply_instance)

/-- A functor that preserves biproducts of a pair preserves binary biproducts. -/
def preserves_binary_biproduct_of_preserves_biproduct (F : C ⥤ D) [preserves_zero_morphisms F]
  (X Y : C) [preserves_biproduct (pair_function X Y) F] : preserves_binary_biproduct X Y F :=
{ preserves := λ b hb,
  { is_limit := is_limit.of_iso_limit
      ((is_limit.postcompose_hom_equiv (by exact diagram_iso_pair _) _).symm
        ((is_bilimit_of_preserves F (b.to_bicone_is_bilimit.symm hb)).is_limit)) $
      cones.ext (iso.refl _) (λ j, by { rcases j with ⟨⟨⟩⟩, tidy, }),
    is_colimit := is_colimit.of_iso_colimit
      ((is_colimit.precompose_inv_equiv (by exact diagram_iso_pair _ ) _).symm
        ((is_bilimit_of_preserves F (b.to_bicone_is_bilimit.symm hb)).is_colimit)) $
      cocones.ext (iso.refl _) (λ j, by { rcases j with ⟨⟨⟩⟩, tidy, }) } }

/-- A functor that preserves biproducts of a pair preserves binary biproducts. -/
def preserves_binary_biproducts_of_preserves_biproducts (F : C ⥤ D)
  [preserves_zero_morphisms F] [preserves_biproducts_of_shape walking_pair F] :
  preserves_binary_biproducts F :=
{ preserves := λ X Y, preserves_binary_biproduct_of_preserves_biproduct F X Y }

attribute [instance, priority 100] preserves_binary_biproducts.preserves

end limits

open category_theory.limits

namespace functor

section bicone
variables {J : Type w₁} (F : C ⥤ D) (f : J → C)
  [has_biproduct f]

section
variables [has_biproduct (F.obj ∘ f)]

/-- As for products, any functor between categories with biproducts gives rise to a morphism
    `F.obj (⨁ f) ⟶ ⨁ (F.obj ∘ f)`. -/
def biproduct_comparison : F.obj (⨁ f) ⟶ ⨁ (F.obj ∘ f) :=
biproduct.lift (λ j, F.map (biproduct.π f j))

@[simp, reassoc] lemma biproduct_comparison_π (j : J) :
  biproduct_comparison F f ≫ biproduct.π _ j = F.map (biproduct.π f j) :=
biproduct.lift_π _ _

/-- As for coproducts, any functor between categories with biproducts gives rise to a morphism
    `⨁ (F.obj ∘ f) ⟶ F.obj (⨁ f)` -/
def biproduct_comparison' : ⨁ (F.obj ∘ f) ⟶ F.obj (⨁ f) :=
biproduct.desc (λ j, F.map (biproduct.ι f j))

@[simp, reassoc] lemma ι_biproduct_comparison' (j : J) :
  biproduct.ι _ j ≫ biproduct_comparison' F f = F.map (biproduct.ι f j) :=
biproduct.ι_desc _ _

variables [preserves_zero_morphisms F]

/-- The composition in the opposite direction is equal to the identity if and only if `F` preserves
    the biproduct, see `preserves_biproduct_of_mono_biproduct_comparison`.  -/
@[simp, reassoc] lemma biproduct_comparison'_comp_biproduct_comparison :
  biproduct_comparison' F f ≫ biproduct_comparison F f = 𝟙 (⨁ (F.obj ∘ f)) :=
by { classical, ext, simp [biproduct.ι_π, ← functor.map_comp, eq_to_hom_map] }

/-- `biproduct_comparison F f` is a split epimorphism. -/
@[simps]
def split_epi_biproduct_comparison : split_epi (biproduct_comparison F f) :=
⟨biproduct_comparison' F f⟩

instance : is_split_epi (biproduct_comparison F f) :=
is_split_epi.mk' (split_epi_biproduct_comparison F f)

/-- `biproduct_comparison' F f` is a split monomorphism. -/
@[simps]
def split_mono_biproduct_comparison' : split_mono (biproduct_comparison' F f) :=
⟨biproduct_comparison F f⟩

instance : is_split_mono (biproduct_comparison' F f) :=
is_split_mono.mk' (split_mono_biproduct_comparison' F f)

end

variables [preserves_zero_morphisms F] [preserves_biproduct f F]

instance has_biproduct_of_preserves : has_biproduct (F.obj ∘ f) :=
has_biproduct.mk
{ bicone := F.map_bicone (biproduct.bicone f),
  is_bilimit := preserves_biproduct.preserves (biproduct.is_bilimit _) }

/-- If `F` preserves a biproduct, we get a definitionally nice isomorphism
    `F.obj (⨁ f) ≅ ⨁ (F.obj ∘ f)`. -/
@[simp]
def map_biproduct : F.obj (⨁ f) ≅ ⨁ (F.obj ∘ f) :=
biproduct.unique_up_to_iso _ (preserves_biproduct.preserves (biproduct.is_bilimit _))

lemma map_biproduct_hom : (map_biproduct F f).hom = biproduct.lift (λ j, F.map (biproduct.π f j)) :=
rfl

lemma map_biproduct_inv : (map_biproduct F f).inv = biproduct.desc (λ j, F.map (biproduct.ι f j)) :=
rfl

end bicone

variables (F : C ⥤ D) (X Y : C) [has_binary_biproduct X Y]

section
variables [has_binary_biproduct (F.obj X) (F.obj Y)]

/-- As for products, any functor between categories with binary biproducts gives rise to a
    morphism `F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y`. -/
def biprod_comparison : F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y :=
biprod.lift (F.map biprod.fst) (F.map biprod.snd)

@[simp, reassoc] lemma biprod_comparison_fst :
  biprod_comparison F X Y ≫ biprod.fst = F.map biprod.fst :=
biprod.lift_fst _ _

@[simp, reassoc] lemma biprod_comparison_snd :
  biprod_comparison F X Y ≫ biprod.snd = F.map biprod.snd :=
biprod.lift_snd _ _

/-- As for coproducts, any functor between categories with binary biproducts gives rise to a
    morphism `F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y)`. -/
def biprod_comparison' : F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y) :=
biprod.desc (F.map biprod.inl) (F.map biprod.inr)

@[simp, reassoc] lemma inl_biprod_comparison' :
  biprod.inl ≫ biprod_comparison' F X Y = F.map biprod.inl :=
biprod.inl_desc _ _

@[simp, reassoc] lemma inr_biprod_comparison' :
  biprod.inr ≫ biprod_comparison' F X Y = F.map biprod.inr :=
biprod.inr_desc _ _

variables [preserves_zero_morphisms F]

/-- The composition in the opposite direction is equal to the identity if and only if `F` preserves
    the biproduct, see `preserves_binary_biproduct_of_mono_biprod_comparison`. -/
@[simp, reassoc] lemma biprod_comparison'_comp_biprod_comparison :
  biprod_comparison' F X Y ≫ biprod_comparison F X Y = 𝟙 (F.obj X ⊞ F.obj Y) :=
by { ext; simp [← functor.map_comp] }

/-- `biprod_comparison F X Y` is a split epi. -/
@[simps]
def split_epi_biprod_comparison : split_epi (biprod_comparison F X Y) :=
⟨biprod_comparison' F X Y⟩

instance : is_split_epi (biprod_comparison F X Y) :=
is_split_epi.mk' (split_epi_biprod_comparison F X Y)

/-- `biprod_comparison' F X Y` is a split mono. -/
@[simps]
def split_mono_biprod_comparison' : split_mono (biprod_comparison' F X Y) :=
⟨biprod_comparison F X Y⟩

instance : is_split_mono (biprod_comparison' F X Y) :=
is_split_mono.mk' (split_mono_biprod_comparison' F X Y)

end

variables [preserves_zero_morphisms F] [preserves_binary_biproduct X Y F]

instance has_binary_biproduct_of_preserves : has_binary_biproduct (F.obj X) (F.obj Y) :=
has_binary_biproduct.mk
{ bicone := F.map_binary_bicone (binary_biproduct.bicone X Y),
  is_bilimit := preserves_binary_biproduct.preserves (binary_biproduct.is_bilimit _ _) }

/-- If `F` preserves a binary biproduct, we get a definitionally nice isomorphism
    `F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y`. -/
@[simp]
def map_biprod : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
biprod.unique_up_to_iso _ _
  (preserves_binary_biproduct.preserves (binary_biproduct.is_bilimit _ _))

lemma map_biprod_hom : (map_biprod F X Y).hom = biprod.lift (F.map biprod.fst) (F.map biprod.snd) :=
rfl

lemma map_biprod_inv : (map_biprod F X Y).inv = biprod.desc (F.map biprod.inl) (F.map biprod.inr) :=
rfl

end functor

namespace limits
variables (F : C ⥤ D) [preserves_zero_morphisms F]

section bicone
variables {J : Type w₁} (f : J → C) [has_biproduct f] [preserves_biproduct f F]
  {W : C}

lemma biproduct.map_lift_map_biprod (g : Π j, W ⟶ f j) :
  F.map (biproduct.lift g) ≫ (F.map_biproduct f).hom = biproduct.lift (λ j, F.map (g j)) :=
by { ext, simp [← F.map_comp] }

lemma biproduct.map_biproduct_inv_map_desc (g : Π j, f j ⟶ W) :
  (F.map_biproduct f).inv ≫ F.map (biproduct.desc g) = biproduct.desc (λ j, F.map (g j)) :=
by { ext, simp [← F.map_comp] }

lemma biproduct.map_biproduct_hom_desc (g : Π j, f j ⟶ W) :
  (F.map_biproduct f).hom ≫ biproduct.desc (λ j, F.map (g j)) = F.map (biproduct.desc g) :=
by rw [← biproduct.map_biproduct_inv_map_desc, iso.hom_inv_id_assoc]

end bicone

section binary_bicone
variables (X Y : C) [has_binary_biproduct X Y] [preserves_binary_biproduct X Y F] {W : C}

lemma biprod.map_lift_map_biprod (f : W ⟶ X) (g : W ⟶ Y) :
  F.map (biprod.lift f g) ≫ (F.map_biprod X Y).hom = biprod.lift (F.map f) (F.map g) :=
by ext; simp [← F.map_comp]

lemma biprod.lift_map_biprod (f : W ⟶ X) (g : W ⟶ Y) :
  biprod.lift (F.map f) (F.map g) ≫ (F.map_biprod X Y).inv = F.map (biprod.lift f g) :=
by rw [← biprod.map_lift_map_biprod, category.assoc, iso.hom_inv_id, category.comp_id]

lemma biprod.map_biprod_inv_map_desc (f : X ⟶ W) (g : Y ⟶ W) :
  (F.map_biprod X Y).inv ≫ F.map (biprod.desc f g) = biprod.desc (F.map f) (F.map g) :=
by ext; simp [← F.map_comp]

lemma biprod.map_biprod_hom_desc (f : X ⟶ W) (g : Y ⟶ W) :
 (F.map_biprod X Y).hom ≫ biprod.desc (F.map f) (F.map g) = F.map (biprod.desc f g) :=
by rw [← biprod.map_biprod_inv_map_desc, iso.hom_inv_id_assoc]

end binary_bicone

end limits

end has_zero_morphisms

end category_theory
