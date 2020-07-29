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

structure has_realization (S : sType.{u}) (Y : Top.{u}) :=
(hom : S ⟶ singular.obj Y)
(w   : ∀ X, bijective (λ f : Y ⟶ X, hom ≫ singular.map f))

def has_realization.map {S₁ S₂ : sType} {Y₁ Y₂ : Top}
  (h₁ : S₁.has_realization Y₁) (h₂ : S₂.has_realization Y₂) (f : S₁ ⟶ S₂) : Y₁ ⟶ Y₂ :=
classical.some $ (h₁.w Y₂).2 (f ≫ h₂.hom)

@[simp, reassoc]
lemma has_realization.map_spec {S₁ S₂ : sType} {Y₁ Y₂ : Top}
  (h₁ : S₁.has_realization Y₁) (h₂ : S₂.has_realization Y₂) (f : S₁ ⟶ S₂) :
  h₁.hom ≫ singular.map (h₁.map h₂ f) = f ≫ h₂.hom :=
classical.some_spec $ (h₁.w Y₂).2 (f ≫ h₂.hom)

@[simp] lemma has_realization.map_id {S : sType} {Y : Top} (h : S.has_realization Y) :
  h.map h (𝟙 S) = 𝟙 Y :=
by { apply (h.w _).1, simp [h.map_spec h (𝟙 S)], }

lemma has_realization.map_comp {S₁ S₂ S₃ : sType} {Y₁ Y₂ Y₃ : Top}
  (h₁ : S₁.has_realization Y₁) (h₂ : S₂.has_realization Y₂) (h₃ : S₃.has_realization Y₃)
  (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
  h₁.map h₃ (f ≫ g) = h₁.map h₂ f ≫ h₂.map h₃ g :=
begin
  apply (h₁.w _).1,
  simp only [has_realization.map_spec, has_realization.map_spec_assoc,
    functor.map_comp, category.assoc],
end

lemma singular_standard_simplex_has_realization (n : NonemptyFinLinOrd) :
  has_realization (standard_simplex.obj n) (singular_standard_simplex.obj n) :=
{ hom := (yoneda_hom_comp_yoneda singular_standard_simplex).app n,
  w   :=
  begin
    intro X,
    split,
    { intros f g h,
      dsimp at h,
      rw [nat_trans.ext_iff, funext_iff] at h,
      specialize h (op n),
      rw [funext_iff] at h,
      specialize h (𝟙 n),
      dsimp at h,
      change singular_standard_simplex.map (𝟙 n) ≫ f = singular_standard_simplex.map (𝟙 n) ≫ g at h,
      rwa [singular_standard_simplex.map_id, category.id_comp f, category.id_comp g] at h, },
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
