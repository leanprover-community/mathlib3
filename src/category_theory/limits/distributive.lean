import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.terminal
import category_theory.limits.preserves.basic

universes v u u₂

open category_theory category_theory.category

namespace category_theory.limits

variables (C : Type u) [category.{v} C] [has_binary_products C] [has_binary_coproducts C]

class distributive :=
(dist_iso (X Y Z : C) : is_iso (distribution X Y Z))

attribute [instance] distributive.dist_iso

variables {C} [distributive C]

-- TODO: opposite version
instance {X Y : C} : mono (coprod.inl : X ⟶ X ⨿ Y) :=
⟨begin
  intros Z f g eq,
  let i : Z ⨯ X ⟶ (Z ⨯ X) ⨿ (Z ⨯ Y) := coprod.inl,
  haveI : split_mono i := { retraction := coprod.desc (𝟙 _) (prod.fst ≫ prod.lift (𝟙 _) f) },
  have hi : mono (i ≫ distribution _ _ _) := mono_comp _ _,
  have : mono (prod.map (𝟙 Z) (coprod.inl : X ⟶ X ⨿ Y)),
    rwa inl_distribution at hi,
  resetI,
  suffices : prod.lift (𝟙 Z) f = prod.lift (𝟙 Z) g,
    simpa using this =≫ prod.snd,
  rw ← cancel_mono (prod.map (𝟙 Z) (coprod.inl : X ⟶ X ⨿ Y)),
  simp only [comp_id, limits.prod.lift_map, eq],
end⟩

noncomputable def prod_initial {X I : C} (hT : is_initial I) :
  is_initial (X ⨯ I) :=
{ desc := λ Y, prod.snd ≫ hT.to _,
  uniq' := λ s m w,
  begin
    have : (coprod.inl : _ ⟶ (X ⨯ I) ⨿ (X ⨯ I)) = coprod.inr,
      rw [← cancel_mono (distribution X I I), inl_distribution, inr_distribution],
      refine prod.hom_ext (by simp) _,
      rw [prod.map_snd, prod.map_snd],
      congr' 1,
      apply hT.hom_ext,
    simpa using this =≫ coprod.desc m (prod.snd ≫ hT.to s.X),
  end }

end category_theory.limits
