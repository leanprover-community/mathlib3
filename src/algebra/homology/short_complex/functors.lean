import algebra.homology.short_complex.basic

noncomputable theory

open category_theory category_theory.limits category_theory.category

variables (J C : Type*) [category J] [category C] [has_zero_morphisms C]


instance category_theory.evaluation_preserves_zero_morphisms (j : J) :
  ((evaluation J C).obj j).preserves_zero_morphisms := { }

namespace short_complex

namespace functor_equivalence

@[simps]
def functor : (short_complex (J ⥤ C)) ⥤ (J ⥤ short_complex C) :=
{ obj := λ S,
  { obj := λ j, S.map ((evaluation J C).obj j),
    map := λ j₁ j₂ f, S.map_nat_trans ((evaluation J C).map f), },
  map := λ S₁ S₂ φ,
  { app := λ j, ((evaluation J C).obj j).map_short_complex.map φ, }, }

@[simps]
def inverse : (J ⥤ short_complex C) ⥤ (short_complex (J ⥤ C)) :=
{ obj := λ F,
  { f := 𝟙 F ◫ π₁_to_π₂,
    g := 𝟙 F ◫ π₂_to_π₃,
    zero := by tidy, },
  map := λ F₁ F₂ φ, begin
    refine hom.mk (φ ◫ 𝟙 _) (φ ◫ 𝟙 _) (φ ◫ 𝟙 _) _ _,
    { ext, dsimp, simp only [id_comp, comp_id, (φ.app x).comm₁₂], },
    { ext, dsimp, simp only [id_comp, comp_id, (φ.app x).comm₂₃], },
  end, }

@[simps]
def unit_iso : 𝟭 _ ≅ functor J C ⋙ inverse J C :=
nat_iso.of_components (λ S, mk_iso
  (nat_iso.of_components (λ j, iso.refl _) (by tidy))
  (nat_iso.of_components (λ j, iso.refl _) (by tidy))
  (nat_iso.of_components (λ j, iso.refl _) (by tidy))
  (by tidy) (by tidy)) (by tidy)

@[simps]
def counit_iso : inverse J C ⋙ functor J C ≅ 𝟭 _:=
nat_iso.of_components
  (λ F, nat_iso.of_components
    (λ j, mk_iso (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy)) (by tidy))
  (by tidy)

example : ℕ := 42

end functor_equivalence

@[simps]
def functor_equivalence : (short_complex (J ⥤ C)) ≌ (J ⥤ short_complex C) :=
{ functor := functor_equivalence.functor J C,
  inverse := functor_equivalence.inverse J C,
  unit_iso := functor_equivalence.unit_iso J C,
  counit_iso := functor_equivalence.counit_iso J C, }


end short_complex
