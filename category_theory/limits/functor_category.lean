import category_theory.limits.limits

open category_theory

namespace category_theory.limits

universes u v

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

variables {J K : Type v} [small_category J] [small_category K]

@[simp] def switched (F : J ⥤ (K ⥤ C)) : K ⥤ (J ⥤ C) :=
{ obj := λ k,
  { obj := λ j, (F j) k,
    map' := λ j j' f, (F.map f) k,
    map_id' := λ X, begin rw category_theory.functor.map_id, refl end,
    map_comp' := λ X Y Z f g, by rw [functor.map_comp, ←functor.category.comp_app] },
  map' := λ c c' f, { app := λ j, (F j).map f, naturality' := λ X Y g, by dsimp; rw ←nat_trans.naturality } }.

@[simp] lemma switched_obj_map (F : J ⥤ (K ⥤ C)) {j j' : J} (f : j ⟶ j') (X : K) : ((switched F) X).map f = (F.map f) X := rfl

@[simp] lemma cone.functor_w {F : J ⥤ (K ⥤ C)} (c : cone F) {j j' : J} (f : j ⟶ j') (k : K) :
  (c.π j) k ≫ (F.map f) k = (c.π j') k :=
sorry

@[simp] def cone.pointwise {F : J ⥤ (K ⥤ C)} (c : cone F) (k : K) : cone ((switched F) k) :=
{ X := c.X k,
  π := λ j, c.π j k,
  w' := λ j j' f, begin rw ←(c.w f), refl, end }

def is_limit_pointwise (F : J ⥤ (K ⥤ C)) (c : cone F) (h : is_limit c) (k : K) :
  is_limit (c.pointwise k) :=
{ lift := λ s, begin sorry end,
  fac' := sorry,
  uniq' := sorry }

-- variable [has_limits.{u v} C]

def is_limit_of_pointwise (F : J ⥤ (K ⥤ C)) (c : cone F) (h : Π k, is_limit (c.pointwise k)) :
  is_limit c :=
{ lift := λ s,
  { app := λ k, (h k).lift
    { X := s.X k,
      π := λ j, (s.π j) k },
    naturality' := begin sorry end },
  fac' := begin tidy, end,
  uniq' := begin tidy, end, }

end category_theory.limits
