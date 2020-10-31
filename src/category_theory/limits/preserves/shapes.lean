/-
Copyright (c) 2020 Scott Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.limits.preserves.limits
import category_theory.limits.shapes

universes v u₁ u₂

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)

section preserve_products

variables {J : Type v} (f : J → C)

/--
(Implementation). The map of a fan is a limit iff the fan consisting of the mapped morphisms
is a limit.
This essentially lets us commute `fan.mk` with `functor.map_cone`.
-/
def fan_map_cone_limit {P : C} (g : Π j, P ⟶ f j) :
  is_limit (G.map_cone (fan.mk P g)) ≃
  is_limit (fan.mk _ (λ j, G.map (g j)) : fan (λ j, G.obj (f j))) :=
begin
  refine (is_limit.postcompose_hom_equiv _ _).symm.trans (is_limit.equiv_iso_limit _),
  refine discrete.nat_iso (λ j, iso.refl (G.obj (f j))),
  refine cones.ext (iso.refl _) (λ j, by { dsimp, simp }),
end

/-- The property of reflecting products expressed in terms of fans. -/
def is_limit_of_reflects_of_map_is_limit [reflects_limit (discrete.functor f) G]
  {P : C} (g : Π j, P ⟶ f j) (t : is_limit (fan.mk _ (λ j, G.map (g j)) : fan (λ j, G.obj (f j)))) :
  is_limit (fan.mk P g) :=
reflects_limit.reflects ((fan_map_cone_limit _ _ _).symm t)

/-- The property of preserving products expressed in terms of fans. -/
def map_is_limit_of_preserves_of_is_limit [preserves_limit (discrete.functor f) G]
  {P : C} (g : Π j, P ⟶ f j) (t : is_limit (fan.mk _ g)) :
  is_limit (fan.mk _ (λ j, G.map (g j)) : fan (λ j, G.obj (f j))) :=
fan_map_cone_limit _ _ _ (preserves_limit.preserves t)

variables [has_product f] [preserves_limit (discrete.functor f) G]

/--
If `G` preserves products and `C` has them, then the fan constructed of the mapped projection of a
product is a limit.
-/
def preserves_the_product :
  is_limit (fan.mk _ (λ (j : J), G.map (pi.π f j)) : fan (λ j, G.obj (f j))) :=
map_is_limit_of_preserves_of_is_limit G f _ (product_is_product _)

variables [has_product (λ (j : J), G.obj (f j))]

/--
If `G` preserves limits, we have an isomorphism from the image of a product to the product of the
images.
-/
def preserves_products_iso : G.obj (∏ f) ≅ ∏ (λ j, G.obj (f j)) :=
is_limit.cone_point_unique_up_to_iso (preserves_the_product G f) (limit.is_limit _)

@[simp, reassoc]
lemma preserves_products_iso_hom_π (j) :
  (preserves_products_iso G f).hom ≫ pi.π _ j = G.map (pi.π f j) :=
is_limit.cone_point_unique_up_to_iso_hom_comp _ _ _

@[simp, reassoc]
lemma map_lift_comp_preserves_products_iso_hom (P : C) (g : Π j, P ⟶ f j) :
  G.map (pi.lift g) ≫ (preserves_products_iso G f).hom = pi.lift (λ j, G.map (g j)) :=
by { ext, simp [← G.map_comp] }

end preserve_products

namespace fork

open category_theory.limits.walking_parallel_pair

variables {X Y Z : C} {f g : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = h ≫ g)

/--
The map of a fork is a limit iff the fork consisting of the mapped morphisms
is a limit.
This essentially lets us commute `fork.of_ι` with `functor.map_cone`.
-/
def equalizer_map_cone_limit :
  is_limit (G.map_cone (fork.of_ι h w)) ≃
  is_limit (fork.of_ι (G.map h) (by simp only [←G.map_comp, w]) : fork (G.map f) (G.map g)) :=
(is_limit.postcompose_hom_equiv (diagram_iso_parallel_pair _) _).symm.trans
  (is_limit.equiv_iso_limit (fork.ext (iso.refl _) (by simp [fork.ι_eq_app_zero])))

/-- The property of preserving equalizers expressed in terms of forks. -/
def map_is_limit_of_preserves_of_is_limit [preserves_limit (parallel_pair f g) G]
  (l : is_limit (fork.of_ι h w)) :
  is_limit (fork.of_ι (G.map h) (by simp only [←G.map_comp, w]) : fork (G.map f) (G.map g)) :=
equalizer_map_cone_limit G w (preserves_limit.preserves l)

/-- The property of reflecting equalizers expressed in terms of forks. -/
def is_limit_of_reflects_of_map_is_limit [reflects_limit (parallel_pair f g) G]
  (l : is_limit (fork.of_ι (G.map h) (by simp only [←G.map_comp, w]) : fork (G.map f) (G.map g))) :
  is_limit (fork.of_ι h w) :=
reflects_limit.reflects ((equalizer_map_cone_limit G w).symm l)

variables (f g)

/--
If `G` preserves equalizers and `C` has them, then the fork constructed of the mapped morphisms of
a fork is a limit.
-/
def is_limit_of_has_equalizer_of_preserves_limit
  [has_equalizer f g] [preserves_limit (parallel_pair f g) G] :
  is_limit (fork.of_ι (G.map (equalizer.ι f g))
                      (by simp only [←G.map_comp, equalizer.condition])) :=
map_is_limit_of_preserves_of_is_limit G _ (equalizer_is_equalizer f g)

/--
The comparison morphism from the map of an equalizer to the equalizer in the target category.
This is an isomorphism if and only if `G` preserves the equalizer of `(f,g)`, shown in
`preserves_equalizer` and `preserves_equalizers_iso`.
-/
def equalizer_comparison [has_equalizer f g] [has_equalizer (G.map f) (G.map g)] :
  G.obj (equalizer f g) ⟶ equalizer (G.map f) (G.map g) :=
equalizer.lift (G.map (equalizer.ι _ _)) (by simp only [←G.map_comp, equalizer.condition])

/--
If the equalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
equalizer of `(f,g)`.
-/
def preserves_equalizer [has_equalizer f g] [has_equalizer (G.map f) (G.map g)]
  [i : is_iso (equalizer_comparison G f g)] : preserves_limit (parallel_pair f g) G :=
begin
  apply preserves_limit_of_preserves_limit_cone (equalizer_is_equalizer f g),
  apply (equalizer_map_cone_limit _ _).symm _,
  apply is_limit.of_point_iso (limit.is_limit (parallel_pair (G.map f) (G.map g))),
  apply i,
end

/--
If `G` preserves the equalizer of `(f,g)`, then the equalizer comparison map for `G` at `(f,g)` is
an isomorphism.
-/
def preserves_equalizers_iso [has_equalizer f g] [has_equalizer (G.map f) (G.map g)]
  [preserves_limit (parallel_pair f g) G] :
  G.obj (equalizer f g) ≅ equalizer (G.map f) (G.map g) :=
is_limit.cone_point_unique_up_to_iso
  (is_limit_of_has_equalizer_of_preserves_limit G f g)
  (limit.is_limit _)

lemma preserves_equalizers_iso_hom [has_equalizer f g] [has_equalizer (G.map f) (G.map g)]
  [preserves_limit (parallel_pair f g) G] :
  (preserves_equalizers_iso G f g).hom = equalizer_comparison G f g :=
rfl

end fork

namespace terminal

variables (X : C)

def terminal_map_cone_limit :
  is_limit (G.map_cone (as_empty_cone X)) ≃ is_terminal (G.obj X) :=
(is_limit.postcompose_hom_equiv (functor.empty_ext _ _) _).symm.trans
  (is_limit.equiv_iso_limit (cones.ext (iso.refl _) (by tidy)))

/-- The property of preserving terminal objects expressed in terms of `is_terminal`. -/
def map_is_limit_of_preserves_of_is_limit [preserves_limit (functor.empty C) G]
  (l : is_terminal X) :
  is_terminal (G.obj X) :=
terminal_map_cone_limit G X (preserves_limit.preserves l)

/-- The property of reflecting terminal objects expressed in terms of `is_terminal`. -/
def is_limit_of_reflects_of_map_is_limit [reflects_limit (functor.empty C) G]
  (l : is_terminal (G.obj X)) :
  is_terminal X :=
reflects_limit.reflects ((terminal_map_cone_limit G X).symm l)

/--
If `G` preserves the terminal object and `C` has a terminal object, then the image of the terminal
object is terminal.
-/
def preserves_the_terminal [has_terminal C] [preserves_limit (functor.empty C) G] :
  is_terminal (G.obj (⊤_ C)) :=
map_is_limit_of_preserves_of_is_limit G (⊤_ C) terminal_is_terminal

/--
The comparison morphism from the image of a terminal object to the terminal in the target category.
This is an isomorphism if and only if `G` preserves terminal objects, shown in `preserves_terminal`
and `preserves_terminal_iso`.
-/
def terminal_comparison [has_terminal C] [has_terminal D] :
  G.obj (⊤_ C) ⟶ ⊤_ D :=
terminal.from _

def preserves_terminal [has_terminal C] [has_terminal D]
  [i : is_iso (terminal_comparison G)] : preserves_limit (functor.empty C) G :=
begin
  apply preserves_limit_of_preserves_limit_cone terminal_is_terminal,
  apply (terminal_map_cone_limit _ _).symm _,
  apply is_limit.of_point_iso (limit.is_limit (functor.empty D)),
  apply i,
end

def preserves_terminal_iso [has_terminal C] [has_terminal D]
  [preserves_limit (functor.empty C) G] :
  G.obj (⊤_ C) ≅ ⊤_ D :=
is_limit.cone_point_unique_up_to_iso (preserves_the_terminal G) (limit.is_limit _)

lemma preserves_terminal_iso_hom [has_terminal C] [has_terminal D]
  [preserves_limit (functor.empty C) G] :
  (preserves_terminal_iso G).hom = terminal_comparison G :=
rfl

end terminal
