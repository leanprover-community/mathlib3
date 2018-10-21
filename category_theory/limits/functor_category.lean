import category_theory.limits.limits

open category_theory

namespace category_theory.limits

universes u v

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

variables {J K : Type v} [small_category J] [small_category K]

def cone.pointwise (F : J ⥤ (K ⥤ C)) (c : cone F) (k : K) : cone (sorry) := sorry

def is_limit (F : J ⥤ (K ⥤ C)) (c : cone F) (h : is_limit c) (k : K) :
  is_limit (c.pointwise k)
  := sorry

end category_theory.limits
