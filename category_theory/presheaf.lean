import category_theory.yoneda
import category_theory.limits.functor_category
import category_theory.limits.types
import category_theory.comma
import category_theory.punit

namespace category_theory
open category_theory.limits

universes u v

-- TODO: How much of this should be generalized to a possibly large category?
variables (C : Type v) [𝒞 : small_category.{v} C]
include 𝒞

def presheaf := Cᵒᵖ ⥤ Type v
variables {C}

namespace presheaf

section simp
variable (X : presheaf C)

@[simp] lemma map_id {c : C} : X.map (𝟙 c) = 𝟙 (X.obj c) := X.map_id c

@[simp] lemma map_id' {c : C} :
X.map (@category.id C 𝒞 c) = 𝟙 (X.obj c) := functor.map_id X c

@[simp] lemma map_comp {c₁ c₂ c₃ : C} {f : c₁ ⟶ c₂} {g : c₂ ⟶ c₃} :
X.map (g ≫ f) = (X.map g) ≫ (X.map f) := X.map_comp g f

@[simp] lemma map_comp' {c₁ c₂ c₃ : C} {f : c₁ ⟶ c₂} {g : c₂ ⟶ c₃} :
X.map (@category.comp C 𝒞 _ _ _ f g) = (X.map g) ≫ (X.map f) := functor.map_comp X g f

end simp

instance : category.{(v+1) v}     (presheaf C) := by dunfold presheaf; apply_instance
instance : has_limits.{(v+1) v}   (presheaf C) := by dunfold presheaf; apply_instance
instance : has_colimits.{(v+1) v} (presheaf C) := by dunfold presheaf; apply_instance
-- instance : has_pullbacks.{(v+1) v} (presheaf C) := limits.functor_category_has_pullbacks
-- instance : has_coproducts.{(v+1) v} (presheaf C) := limits.functor_category_has_coproducts
-- instance : has_coequalizers.{(v+1) v} (presheaf C) := limits.functor_category_has_coequalizers

section restriction_extension
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

def restricted_yoneda (F : C ⥤ D) : D ⥤ presheaf C :=
{ obj := λ d, F.op ⋙ yoneda.obj d,
  map := λ d₁ d₂ g, whisker_left _ $ yoneda.map g }

variables [has_colimits.{u v} D]

def yoneda_extension (F : C ⥤ D) : presheaf C ⥤ D :=
{ obj := λ X, colimit (comma.fst.{v v v v} yoneda (functor.of.obj X) ⋙ F),
  map := λ X₁ X₂ f, colimit.pre (comma.fst.{v v v v} yoneda (functor.of.obj X₂) ⋙ F) (comma.map_right yoneda $ functor.of.map f),
  map_id' := λ X,
  begin
    -- tidy,
    erw functor.of.map_id, -- why doesn't this simplify automatically?
    erw colimit.pre_map
      (comma.fst.{v v v v} yoneda (functor.of.obj X) ⋙ F)
      (comma.map_right_id'.{v v v} yoneda (functor.of.obj X)).hom,
    erw colimit.pre_id,
    erw ← colim.map_comp,
    erw ← colim.map_id,
    congr,
    tidy
  end,
  map_comp' := λ X₁ X₂ X₃ f g,
  begin
    erw functor.of.map_comp,
    erw colimit.pre_map
      (comma.fst.{v v v v} yoneda (functor.of.obj X₃) ⋙ F)
      (comma.map_right_comp.{v v v} yoneda (functor.of.map f) (functor.of.map g)).hom,
    erw colimit.pre_pre
      (comma.fst.{v v v v} yoneda (functor.of.obj X₃) ⋙ F)
      (comma.map_right yoneda (functor.of.map g))
      (comma.map_right yoneda (functor.of.map f)),
    erw limits.colimit.pre_comp _ _ _,
    erw ← category.assoc,
    erw ← colim.map_comp,
    congr,
    dsimp [whisker_right, whiskering_right, functor.associator],
    ext1,
    simp,
    erw category.comp_id,
    exact limits.has_colimits_of_shape_of_has_colimits
  end }

@[simp] lemma restricted_yoneda_obj (F : C ⥤ D) (d : D) : (restricted_yoneda F).obj d = F.op ⋙ yoneda.obj d := rfl
@[simp] lemma restricted_yoneda_map (F : C ⥤ D) {d₁ d₂ : D} (g : d₁ ⟶ d₂) : (restricted_yoneda F).map g = (whisker_left _ $ yoneda.map g) := rfl
@[simp] lemma yoneda_extension_obj (F : C ⥤ D) (X : presheaf C) : (yoneda_extension F).obj X = colimit (comma.fst.{v v v v} yoneda (functor.of.obj X) ⋙ F) := rfl
@[simp] lemma yoneda_extension_map (F : C ⥤ D) {X₁ X₂ : presheaf C} (f : X₁ ⟶ X₂) :
(yoneda_extension F).map f = colimit.pre (comma.fst.{v v v v} yoneda (functor.of.obj X₂) ⋙ F) (comma.map_right yoneda $ functor.of.map f) := rfl

end restriction_extension

end presheaf

end category_theory
