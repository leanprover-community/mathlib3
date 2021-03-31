import category_theory.comma
import category_theory.limits.has_limits
import category_theory.limits.preserves.basic

namespace category_theory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes v u
variables {A : Type u} [category.{v} A]
variables {B : Type u} [category.{v} B]
variables {T : Type u} [category.{v} T]
variables {L : A ⥤ T} {R : B ⥤ T}

variables {I : Type v} [small_category I]

/-- Under appropriate colimit existence and preservation properties, construct an isomorphism
`L (colim F) ≅ colim (L ∘ F)`. -/
def commute_colimit {F : I ⥤ A} [limits.has_colimit F]
  [limits.preserves_colimits_of_shape I L] [limits.has_colimit (F ⋙ L)]:
  L.obj (limits.colimit F) ≅ limits.colimit (F ⋙ L) :=
{ hom := _, -- L colim F ⟶ colim (F ⋙ L)
  inv := _,
  hom_inv_id' := _,
  inv_hom_id' := _ }

lemma comma_has_colimit {F : I ⥤ comma L R}
  [limits.preserves_limits_of_shape I L] [limits.preserves_limits_of_shape I R]
  [limits.has_colimit (F ⋙ comma.fst L R)]
  [limits.has_colimit (F ⋙ comma.snd L R)] : limits.has_colimit F :=
begin
  fconstructor,
  fconstructor,
  fconstructor,
  fconstructor,
  -- the candidate for the colimit
  fconstructor,
  exact limits.colimit (F ⋙ comma.fst L R),
  exact limits.colimit (F ⋙ comma.snd L R),
  -- L colim (F ⋙ pr₁) ≅ colim F ⋙ pr₁ ⋙ L = colim F ⋙ pr₂ ⋙ R ⟶ R colim (F ⋙ pr₂)
  --

end

end category_theory
