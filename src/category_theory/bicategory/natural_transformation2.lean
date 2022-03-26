import category_theory.bicategory.natural_transformation

namespace category_theory

open category bicategory
open_locale bicategory

universes w₁ w₂ v₁ v₂ u₁ u₂

variables {B : Type u₁} [bicategory.{w₁ v₁} B] {C : Type u₂} [bicategory.{w₂ v₂} C]
variables {F G H : oplax_functor B C}

namespace oplax_nat_trans

/-- Vertical composition of oplax natural transformations. -/
@[simps]
def vcomp' (η : oplax_nat_trans F G) (θ : oplax_nat_trans G H) : oplax_nat_trans F H :=
{ app := λ a, η.app a ≫ θ.app a,
  naturality := λ a b f,
    (α_ _ _ _).inv ≫ η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫
      η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv,
  naturality_id' := by tidy,
  naturality_naturality' := by tidy,
  naturality_comp' := λ a b c f g, by
  { calc _ =  _ ≫
    -- F.map_comp f g ▷ η.app c ▷ θ.app c ≫ _ ≫
    --   F.map f ◁ η.naturality g ▷ θ.app c ≫ _ ≫
    --     (η.naturality f ▷ (G.map g ≫ θ.app c) ≫
    --       (η.app a ≫ G.map f) ◁ θ.naturality g) ≫ _ ≫
    --         η.app a ◁ θ.naturality f ▷ H.map g ≫ _  : _
    -- ... =  _ ≫
    F.map_comp f g ▷ η.app c ▷ θ.app c ≫ _ ≫
      F.map f ◁ η.naturality g ▷ θ.app c ≫ _ ≫
        ((F.map f ≫ η.app b) ◁ θ.naturality g ≫
          η.naturality f ▷ (θ.app b ≫ H.map g)) ≫ _ ≫
            η.app a ◁ θ.naturality f ▷ H.map g ≫ _  : _
    ... =  _ : _,
    exact (α_ _ _ _).inv,
    exact (α_ _ _ _).hom ▷ _ ≫ (α_ _ _ _).hom,
    exact _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv,
    exact (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv,
    exact _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv,
    { rw [whisker_exchange], simp },
    { simp },
    -- exact (α_ _ _ _).inv ≫ (α_ _ _ _).hom ≫ (α_ _ _ _).inv,
    -- exact (α_ _ _ _).hom ▷ _ ≫ (α_ _ _ _).hom,
    -- exact _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv,
    -- exact (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv,
    -- exact _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv,
    -- { repeat { coherence <|> solve1 { rw [whisker_exchange] } <|> congr' 1 } }
    } }

end oplax_nat_trans

end category_theory
