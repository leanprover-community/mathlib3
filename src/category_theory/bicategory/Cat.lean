import category_theory.category.Cat
import category_theory.bicategory.basic

universes v u

namespace category_theory

open category_theory

end category_theory

namespace Cat

open category_theory

@[simps]
instance : bicategory (Cat.{v u}) :=
{ hom := λ C D, C ⥤ D,
  id := λ C, 𝟭 C,
  comp := λ _ _ _ F G, F ⋙ G,
  hom_category := λ C D, functor.category C D,
  whisker_left := λ _ _ _ F _ _ η, whisker_left F η,
  whisker_right := λ _ _ _ _ _ η H, whisker_right η H,
  whisker_exchange' := by { intros, ext, dsimp, simp },
  associator := λ _ _ _ _ F G H, functor.associator F G H,
  left_unitor :=  λ _ _ F, F.left_unitor,
  left_unitor_naturality' := by { intros, ext, dsimp, simp },
  right_unitor := λ _ _ F, F.right_unitor,
  right_unitor_naturality' := by { intros, ext, dsimp, simp },
  pentagon' := by { intros, apply functor.pentagon },
  triangle' := by { intros, apply functor.triangle } }

end Cat
