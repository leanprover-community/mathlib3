/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import category_theory.comma
import topology.simplicial.singular
import topology.category.Top

/-! # Geometric realization of simplicial types -/

noncomputable theory

universe variables u

open category_theory category_theory.limits

namespace sType
open Top function opposite

structure is_realization (S : sType.{u}) (Y : Top.{u}) :=
(hom : S ⟶ singular.obj Y)
(w   : ∀ X, bijective (λ f : Y ⟶ X, hom ≫ singular.map f))

def is_realization.map {S₁ S₂ : sType} {Y₁ Y₂ : Top}
  (h₁ : is_realization S₁ Y₁) (h₂ : is_realization S₂ Y₂) (f : S₁ ⟶ S₂) : Y₁ ⟶ Y₂ :=
classical.some $ (h₁.w Y₂).2 (f ≫ h₂.hom)

lemma is_realization.map_spec {S₁ S₂ : sType} {Y₁ Y₂ : Top}
  (h₁ : is_realization S₁ Y₁) (h₂ : is_realization S₂ Y₂) (f : S₁ ⟶ S₂) :
  h₁.hom ≫ singular.map (h₁.map h₂ f) = f ≫ h₂.hom :=
classical.some_spec $ (h₁.w Y₂).2 (f ≫ h₂.hom)

-- move this
lemma singular_map_injective (X Y : Top) :
  injective (@category_theory.functor.map _ _ _ _ singular X Y) :=
begin
  intros f g h,
  ext x,
  have H := congr_fun (congr_arg nat_trans.app h) (op $ NonemptyFinLinOrd.of punit),
  dsimp [singular] at H,
  have H' := congr_fun H ⟨λ _, x, continuous_const⟩,
  dsimp at H',
  have H'' := congr_arg continuous_map.to_fun H',
  convert congr_fun H'' _,
  refine ⟨λ _, 1, _⟩,
  show has_sum (λ x : punit, (1 : nnreal)) 1,
  convert has_sum_fintype _,
  { simp },
  { apply_instance }
end

lemma singular_standard_simplex_is_realization (n : NonemptyFinLinOrd) :
  is_realization (standard_simplex.obj n) (singular_standard_simplex.obj n) :=
{ hom := (yoneda_hom_comp_yoneda singular_standard_simplex).app n,
  w   :=
  begin
    intro X,
    dsimp only [yoneda_hom_comp_yoneda],
    split,
    { intros f g h,
      apply singular_map_injective,
      -- ext x,
      -- dsimp at h,
      -- have H := congr_fun (congr_arg nat_trans.app h) (op n),
      -- dsimp [yoneda_hom_comp_yoneda] at H,
      -- have H' := congr_fun H (𝟙 _),
      -- dsimp at H',
      sorry },
    { intros f,
      let g : _ := _,
      refine ⟨g, _⟩,
      { ext1, ext1 m, dsimp [singular],
        ext1 i, change unop m ⟶ n at i,
        ext1 x,
        dsimp, sorry },
      {  } },
  end }

open simplex_category opposite

def category_of_simplices (X : sType.{u}) : Type u :=
Σ (n : simplex_category), (skeletal_functor.{u}.op ⋙ X).obj (op n)

-- The following definition has universe issues
-- Σ (n : simplex_category), (skeletal_functor.{u}.op ⋙ X).obj (op n)

namespace category_of_simplices
variables (X : sType.{u})

-- slow, sigh
-- instance : small_category (category_of_simplices X) :=
-- { hom := λ s t, ulift { f : s.1 ⟶ t.1 // (skeletal_functor.{u}.op ⋙ X).map f.op t.2 = s.2 },
--   id := λ s, ⟨⟨𝟙 _, by tidy⟩⟩,
--   comp := λ _ _ _ f g, ⟨⟨f.down.1 ≫ g.down.1, by tidy⟩⟩ }

end category_of_simplices

set_option pp.universes true

#print category_of_simplices.category

-- def realization_obj (X : sType.{u}) : Top.{u} :=
-- begin
--   refine colimit _,
-- end

/-- The geometric realization of a simplicial type.
This functor is left adjoint to `Top.singular`. -/
@[simps]
def realization : sType.{u} ⥤ Top.{u} :=
{ obj := λ X, by extract_goal realization_obj,
  map := _,
  map_id' := _,
  map_comp' := _ }


end sType
