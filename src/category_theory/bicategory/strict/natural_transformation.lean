import category_theory.bicategory.strict
import category_theory.bicategory.natural_transformation

namespace category_theory

namespace strict_bicategory

open_locale bicategory
open bicategory category oplax_nat_trans

universes w₁ w₂ v₁ v₂ u₁ u₂

variables {B : Type u₁} [bicategory.{w₁ v₁} B]
variables {C : Type u₂} [bicategory.{w₂ v₂} C] [strict C]
variables {F G H : oplax_functor B C}

variables {a b c d e : B}

namespace oplax_nat_trans

-- We need strict version of simp lemmas if associators or unitors appear in the LHS.

@[simp, reassoc]
lemma whisker_right_naturality_comp (η : oplax_nat_trans F G)
  {a b c : B} {a' : C} (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
  η.naturality (f ≫ g) ▷ h ≫ eq_to_hom (by simp) ≫ η.app a ◁ G.map_comp f g ▷ h =
    F.map_comp f g ▷ η.app c ▷ h ≫ eq_to_hom (by simp) ≫
      F.map f ◁ η.naturality g ▷ h ≫ eq_to_hom (by simp) ≫
        η.naturality f ▷ G.map g ▷ h ≫ eq_to_hom (by simp) :=
by simpa using oplax_nat_trans.whisker_right_naturality_comp η f g h

@[simp, reassoc]
lemma whisker_right_naturality_id (η : oplax_nat_trans F G)
  {a : B} {a' : C} (f : G.obj a ⟶ a') :
  η.naturality (𝟙 a) ▷ f ≫ eq_to_hom (by simp) ≫ η.app a ◁ G.map_id a ▷ f =
    F.map_id a ▷ η.app a ▷ f ≫ eq_to_hom (by simp) :=
by simpa using oplax_nat_trans.whisker_right_naturality_id η f

/-- Vertical composition of oplax natural transformations. -/
@[simps]
def vcomp (η : oplax_nat_trans F G) (θ : oplax_nat_trans G H) : oplax_nat_trans F H :=
{ app := λ a, η.app a ≫ θ.app a,
  naturality := λ a b f,
    (α_ _ _ _).inv ≫ η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫
      η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv,
  naturality_id' := by tidy,
  naturality_naturality' := by tidy,
  naturality_comp' := λ a b c f g, by
  { calc _ = eq_to_hom _ ≫
    F.map_comp f g ▷ η.app c ▷ θ.app c ≫ eq_to_hom _ ≫
      F.map f ◁ η.naturality g ▷ θ.app c ≫ eq_to_hom _ ≫
        η.naturality f ▷ G.map g ▷ θ.app c ≫ eq_to_hom _ ≫
          η.app a ◁ G.map f ◁ θ.naturality g ≫ eq_to_hom _ ≫
            η.app a ◁ θ.naturality f ▷ H.map g ≫ eq_to_hom _  : _
    ... = eq_to_hom _ ≫
    F.map_comp f g ▷ η.app c ▷ θ.app c ≫ eq_to_hom _ ≫
      F.map f ◁ η.naturality g ▷ θ.app c ≫ eq_to_hom _ ≫
        (F.map f ≫ η.app b) ◁ θ.naturality g ≫
          η.naturality f ▷ (θ.app b ≫ H.map g) ≫ eq_to_hom _ ≫
            η.app a ◁ θ.naturality f ▷ H.map g ≫ eq_to_hom _  : _
    ... = eq_to_hom _ ≫
    F.map_comp f g ▷ η.app c ▷ θ.app c ≫ eq_to_hom _ ≫
      F.map f ◁ η.naturality g ▷ θ.app c ≫ eq_to_hom _ ≫
        F.map f ◁ η.app b ◁ θ.naturality g ≫ eq_to_hom _ ≫
          η.naturality f ▷ θ.app b ▷ H.map g ≫ eq_to_hom _ ≫
            η.app a ◁ θ.naturality f ▷ H.map g ≫ eq_to_hom _ : _
    ... = _ : _,
    all_goals {
      -- fill underlines in `eq_to_hom _'
      solve1 { simp only [category.assoc] } <|>
      -- apply exchange law of whiskering
      { rw [whisker_exchange_assoc], simp } <|>
      -- simplify
      simp } } }

end oplax_nat_trans

end strict_bicategory

end category_theory
