import category_theory.category
import category_theory.arrow
import category_theory.model_categories.lifting_properties
import category_theory.model_categories.squares

namespace category_theory

universes v₁ u₁
variables {C : Type u₁} [category.{v₁} C]

variables {A B X Y Z : C}



/-- Definition: X is a retract of U if there are maps X → U → X whose composite is the identity. -/
structure retract (X U : C) :=
  (into : X ⟶ U)
  (onto : U ⟶ X)
  (retract : into ≫ onto = 𝟙 X)

/-- Retract lemma: if `i ≫ p` has the right lifting property
w.r.t. `i`, then `i ≫ p` is a retract of `p`. -/
lemma retract_of_lifting {X T Y : C} {i : X ⟶ T} {p : T ⟶ Y}
  (h: has_lifting_property (arrow.mk i) (arrow.mk (i ≫ p))) :
  retract (arrow.mk (i ≫ p)) (arrow.mk p) :=
{ into := square_from_composable_right_id i p,
  onto := begin
    haveI := h (square_from_composable_left_id i p),
    have lift_structure_sq1 := arrow.has_lift.struct (square_from_composable_left_id i p),
    let q := lift_structure_sq1.fac_right,
    simp only [arrow.mk_hom] at q,
    have : lift_structure_sq1.lift ≫ (arrow.mk (i ≫ p)).hom = (arrow.mk p).hom ≫ 𝟙 Y :=
    begin
      simp only [arrow.mk_hom],
      tidy,
    end,
    exact arrow.hom_mk this,
  end,
  retract := begin
    simp,
    ext,
    {
      haveI := h (square_from_composable_left_id i p),
      let lift_structure_sq1 := arrow.has_lift.struct (square_from_composable_left_id i p),
      have : (square_from_composable_right_id i p).left ≫  lift_structure_sq1.lift = 𝟙 X :=
      begin
        have q := (arrow.has_lift.struct (square_from_composable_left_id i p)).fac_left,
        tidy,
      end,
      simp only [arrow.id_left, comma.comp_left, arrow.hom_mk_left],
      tidy,
    },
    {
      tidy,
    }
  end }

end category_theory
