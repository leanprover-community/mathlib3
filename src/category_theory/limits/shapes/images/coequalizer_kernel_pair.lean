import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.pullbacks

open category_theory.limits

namespace category_theory

universes v u -- declare the `v`s first; see `category_theory.category` for an explanation

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

variables [has_pullbacks.{v} C] [has_coequalizers.{v} C]

variables {X Y : C} (f : X ⟶ Y)

def coequalizer_kernel_pair : C :=
coequalizer (pullback.fst : pullback f f ⟶ X) (pullback.snd : pullback f f ⟶ X)

namespace coequalizer_kernel_pair

def π : X ⟶ coequalizer_kernel_pair f := coequalizer.π _ _
def ι : coequalizer_kernel_pair f ⟶ Y := coequalizer.desc _ _ f (by simp)

instance : epi π := sorry -- in fact a regular epi
instance : mono ι := sorry

@[simp]
lemma fac : π f ≫ ι f = f := sorry

variables {Z : C} (g : Y ⟶ Z)
def pre_comp : coequalizer_kernel_pair (f ≫ g) ⟶ coequalizer_kernel_pair g := sorry
def post_comp : coequalizer_kernel_pair f ⟶ coequalizer_kernel_pair (f ≫ g) := sorry

variables {X' Y'} (f' : X' ⟶ Y') (dX : X ⟶ X') (dY : Y ⟶ Y')
  (w : f ≫ dY = dX ≫ f')

def map : coequalizer_kernel_pair f ⟶ coequalizer_kernel_pair f' := sorry



end coequalizer_kernel_pair

end category_theory
