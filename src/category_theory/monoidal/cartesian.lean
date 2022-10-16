import category_theory.limits.constructions.binary_products
import category_theory.monoidal.category

noncomputable theory

namespace category_theory

open category_theory.limits

namespace monoidal_category

universes u v
variables (C : Type u) [category.{v} C] [has_binary_products C] [has_terminal C]

instance : monoidal_category C :=
{ tensor_obj := λ X Y, X ⨯ Y,
  tensor_hom := λ X1 Y1 X2 Y2 f g, limits.prod.map f g,
  tensor_id' := λ _ _, limits.prod.map_id_id,
  tensor_comp' := λ _ _ _ _ _ _, prod.map_comp_comp,
  tensor_unit := ⊤_ C,
  associator := prod.associator,
  associator_naturality' := λ _ _ _ _ _ _, prod.associator_naturality,
  left_unitor := λ c,
  { hom := limits.prod.snd,
    inv := limits.prod.lift (terminal_is_terminal.from _) $ 𝟙 _,
    hom_inv_id' :=
    begin
      ext,
      { simp only [category.assoc, is_terminal.comp_from, prod.lift_fst, category.id_comp],
        congr' 1 },
      { simp only [prod.comp_lift, category.comp_id, prod.lift_snd, category.id_comp], },
    end,
    inv_hom_id' := prod.lift_snd _ _ },
  left_unitor_naturality' := λ _ _ _, limits.prod.map_snd _ _,
  right_unitor := λ c,
  { hom := limits.prod.fst,
    inv := limits.prod.lift (𝟙 _) $ terminal_is_terminal.from _,
    hom_inv_id' :=
    begin
      ext,
      { simp only [prod.comp_lift, category.comp_id, prod.lift_fst, category.id_comp], },
      { simp only [prod.comp_lift, is_terminal.comp_from, prod.lift_snd, category.id_comp],
        congr' 1 },
    end,
    inv_hom_id' := prod.lift_fst _ _ },
  right_unitor_naturality' := λ _ _ _, limits.prod.map_fst _ _,
  pentagon' := prod.pentagon,
  triangle' := λ X Y, begin
    ext,
    { simp only [prod.lift_fst, category.comp_id, prod.associator_hom, prod.lift_map,
      limits.prod.map_fst], },
    { simp only [category.comp_id, prod.lift_snd, prod.associator_hom, prod.lift_map,
      limits.prod.map_snd], },
  end }

end monoidal_category

end category_theory
