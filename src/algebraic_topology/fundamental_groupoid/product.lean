/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/

import category_theory.groupoid
import algebraic_topology.fundamental_groupoid.basic
import topology.category.Top.limits
import topology.homotopy.product
import category_theory.limits.preserves.shapes.products

/-!
# Fundamental groupoid preserves products
In this file, we give the following definitions/theorems:

  - `fundamental_groupoid_functor.pi_iso` An isomorphism between Π i, (π Xᵢ) and π (Πi, Xᵢ), whose
    inverse is precisely the product of the maps π (Π i, Xᵢ) → π (Xᵢ), each induced by
    the projection in `Top` Π i, Xᵢ → Xᵢ.

  - `fundamental_groupoid_functor.prod_iso` An isomorphism between πX × πY and π (X × Y), whose
    inverse is precisely the product of the maps π (X × Y) → πX and π (X × Y) → Y, each induced by
    the projections X × Y → X and X × Y → Y

  - `fundamental_groupoid_functor.preserves_product` A proof that the fundamental groupoid functor
    preserves all products.
-/

noncomputable theory

namespace fundamental_groupoid_functor

open_locale fundamental_groupoid

universes u

section pi

variables {I : Type u} (X : I → Top.{u})

/--
The projection map Π i, X i → X i induces a map π(Π i, X i) ⟶ π(X i).
-/
def proj (i : I) : πₓ (Top.of (Π i, X i)) ⥤ πₓ (X i) := πₘ ⟨_, continuous_apply i⟩

/-- The projection map is precisely path.homotopic.proj interpreted as a functor -/
@[simp] lemma proj_map (i : I) (x₀ x₁ : πₓ (Top.of (Π i, X i))) (p : x₀ ⟶ x₁) :
  (proj X i).map p = (@path.homotopic.proj _ _ _ _ _ i p) := rfl

/--
The map taking the pi product of a family of fundamental groupoids to the fundamental
groupoid of the pi product. This is actually an isomorphism (see `pi_iso`)
-/
@[simps]
def pi_to_pi_Top : (Π i, πₓ (X i)) ⥤ πₓ (Top.of (Π i, X i)) :=
{ obj := λ g, g,
  map := λ v₁ v₂ p, path.homotopic.pi p,
  map_id' :=
  begin
    intro x,
    change path.homotopic.pi (λ i, 𝟙 (x i)) = _,
    simp only [fundamental_groupoid.id_eq_path_refl, path.homotopic.pi_lift],
    refl,
  end,
  map_comp' := λ x y z f g, (path.homotopic.comp_pi_eq_pi_comp f g).symm, }

/--
Shows `pi_to_pi_Top` is an isomorphism, whose inverse is precisely the pi product
of the induced projections. This shows that `fundamental_groupoid_functor` preserves products.
-/
@[simps]
def pi_iso : category_theory.Groupoid.of (Π i : I, πₓ (X i)) ≅ πₓ (Top.of (Π i, X i)) :=
{ hom := pi_to_pi_Top X,
  inv := category_theory.functor.pi' (proj X),
  hom_inv_id' :=
  begin
    change pi_to_pi_Top X ⋙ (category_theory.functor.pi' (proj X)) = 𝟭 _,
    apply category_theory.functor.ext; intros,
    { ext, simp, }, { refl, },
  end,
  inv_hom_id' :=
  begin
    change (category_theory.functor.pi' (proj X)) ⋙ pi_to_pi_Top X = 𝟭 _,
    apply category_theory.functor.ext; intros,
    { suffices : path.homotopic.pi ((category_theory.functor.pi' (proj X)).map f) = f, { simpa, },
      change (category_theory.functor.pi' (proj X)).map f
        with λ i, (category_theory.functor.pi' (proj X)).map f i,
      simp, }, { refl, }
  end }

section preserves
open category_theory

/-- Equivalence between the categories of cones over the objects `π Xᵢ` written in two ways -/
def cone_discrete_comp : limits.cone (discrete.functor X ⋙ π) ≌
  limits.cone (discrete.functor (λ i, πₓ (X i))) :=
limits.cones.postcompose_equivalence (discrete.comp_nat_iso_discrete X π)

lemma cone_discrete_comp_obj_map_cone :
  (cone_discrete_comp X).functor.obj ((π).map_cone (Top.pi_fan.{u} X))
  = limits.fan.mk (πₓ (Top.of (Π i, X i))) (proj X) := rfl

/-- This is `pi_iso.inv` as a cone morphism (in fact, isomorphism) -/
def pi_Top_to_pi_cone : (limits.fan.mk (πₓ (Top.of (Π i, X i))) (proj X)) ⟶
  Groupoid.pi_limit_fan (λ i : I, (πₓ (X i))) := { hom := category_theory.functor.pi' (proj X) }

instance : is_iso (pi_Top_to_pi_cone X) :=
begin
  haveI : is_iso (pi_Top_to_pi_cone X).hom := (infer_instance : is_iso (pi_iso X).inv),
  exact limits.cones.cone_iso_of_hom_iso (pi_Top_to_pi_cone X),
end

/-- The fundamental groupoid functor preserves products -/
def preserves_product : limits.preserves_limit (discrete.functor X) π :=
begin
  apply limits.preserves_limit_of_preserves_limit_cone (Top.pi_fan_is_limit.{u} X),
  apply (limits.is_limit.of_cone_equiv (cone_discrete_comp X)).to_fun,
  simp only [cone_discrete_comp_obj_map_cone],
  apply limits.is_limit.of_iso_limit _ (as_iso (pi_Top_to_pi_cone X)).symm,
  exact (Groupoid.pi_limit_cone _).is_limit,
end

end preserves

end pi

section prod

variables (A B : Top.{u})

/-- The induced map of the left projection map X × Y → X -/
def proj_left : πₓ (Top.of (A × B)) ⥤ πₓ A := πₘ ⟨_, continuous_fst⟩

/-- The induced map of the right projection map X × Y → Y -/
def proj_right : πₓ (Top.of (A × B)) ⥤ πₓ B := πₘ ⟨_, continuous_snd⟩

@[simp] lemma proj_left_map (x₀ x₁ : πₓ (Top.of (A × B))) (p : x₀ ⟶ x₁) :
  (proj_left A B).map p = path.homotopic.proj_left p := rfl

@[simp] lemma proj_right_map (x₀ x₁ : πₓ (Top.of (A × B))) (p : x₀ ⟶ x₁) :
  (proj_right A B).map p = path.homotopic.proj_right p := rfl


/--
The map taking the product of two fundamental groupoids to the fundamental groupoid of the product
of the two topological spaces. This is in fact an isomorphism (see `prod_iso`).
-/
@[simps obj]
def prod_to_prod_Top : (πₓ A) × (πₓ B) ⥤ πₓ (Top.of (A × B)) :=
{ obj := λ g, g,
  map := λ x y p, match x, y, p with
    | (x₀, x₁), (y₀, y₁), (p₀, p₁) := path.homotopic.prod p₀ p₁
  end,
  map_id' :=
  begin
    rintro ⟨x₀, x₁⟩,
    simp only [category_theory.prod_id, fundamental_groupoid.id_eq_path_refl],
    unfold_aux, rw path.homotopic.prod_lift, refl,
  end,
  map_comp' := λ x y z f g, match x, y, z, f, g with
    | (x₀, x₁), (y₀, y₁), (z₀, z₁), (f₀, f₁), (g₀, g₁) :=
    (path.homotopic.comp_prod_eq_prod_comp f₀ f₁ g₀ g₁).symm
  end }

lemma prod_to_prod_Top_map {x₀ x₁ : πₓ A} {y₀ y₁ : πₓ B}
  (p₀ : x₀ ⟶ x₁) (p₁ : y₀ ⟶ y₁) :
  @category_theory.functor.map _ _ _ _
  (prod_to_prod_Top A B) (x₀, y₀) (x₁, y₁) (p₀, p₁) = path.homotopic.prod p₀ p₁ := rfl

/--
Shows `prod_to_prod_Top` is an isomorphism, whose inverse is precisely the product
of the induced left and right projections.
-/
@[simps]
def prod_iso : category_theory.Groupoid.of ((πₓ A) × (πₓ B)) ≅ (πₓ (Top.of (A × B))) :=
{ hom := prod_to_prod_Top A B,
  inv := (proj_left A B).prod' (proj_right A B),
  hom_inv_id' :=
  begin
    change prod_to_prod_Top A B ⋙ ((proj_left A B).prod' (proj_right A B)) = 𝟭 _,
    apply category_theory.functor.hext, { intros, ext; simp; refl, },
    rintros ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ ⟨f₀, f₁⟩,
    have := and.intro (path.homotopic.proj_left_prod f₀ f₁) (path.homotopic.proj_right_prod f₀ f₁),
    simpa,
  end,
  inv_hom_id' :=
  begin
    change ((proj_left A B).prod' (proj_right A B)) ⋙ prod_to_prod_Top A B = 𝟭 _,
    apply category_theory.functor.hext, { intros, ext; simp; refl, },
    rintros ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ f,
    have := path.homotopic.prod_proj_left_proj_right f,
    simpa,
  end }

end prod

end fundamental_groupoid_functor
