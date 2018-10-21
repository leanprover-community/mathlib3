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

def functor.constant (K : Type v) [small_category K] (X : C) : K ⥤ C :=
{ obj := λ k, X,
  map' := λ k k' f, 𝟙 X }

@[simp] lemma functor.constant_obj (X : C) (k : K) : ((functor.constant K X) : K ⥤ C) k = X := rfl
@[simp] lemma functor.constant_map (X : C) {k k' : K} (f : k ⟶ k') : (functor.constant K X).map f = 𝟙 X := rfl

def nat_trans.of_cone {F : J ⥤ C} (c : cone F) : functor.constant.{u v} J c.X ⟹ F :=
{ app := c.π,
  naturality' := λ j j' f, begin simp, erw category.id_comp, end }

def is_limit_pointwise (F : J ⥤ (K ⥤ C)) (c : cone F) (h : is_limit c) (k : K) :
  is_limit (c.pointwise k) :=
{ lift := λ s, (h.lift { X := functor.constant K s.X, π := λ j, { app := λ k', begin simp, exact s.π j end }, w' := sorry }).app k,
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
