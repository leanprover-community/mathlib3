/-
-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
-/
import category_theory.concrete_category
import category_theory.eq_to_hom

section
universes u

end

universes v u

open category_theory

namespace category_theory

class decorated_category (V : Type (v+1)) [large_category V] [concrete_category V] :=
(obj_data : Type v → Type (v+1))
(obj_equiv [] : V ≃ Σ α, obj_data α)
(hom_data : Π {X Y : Type v} (f : X → Y) (X' : obj_data X) (Y' : obj_data Y), Type v)
(hom_equiv : Π (p q : Σ α, obj_data α), (obj_equiv.symm p ⟶ obj_equiv.symm q) ≃ Σ (f : p.1 → q.1), hom_data f p.2 q.2)
(forget_obj_eq : Π (p : Σ α, obj_data α), (forget V).obj (obj_equiv.symm p) = p.1 . obviously)
(forget_map_eq : Π {p q : Σ α, obj_data α} (f : p.1 → q.1) (d : hom_data f p.2 q.2),
  (forget V).map ((hom_equiv p q).symm ⟨f, d⟩) ≫ eq_to_hom (forget_obj_eq q) = eq_to_hom (forget_obj_eq p) ≫ f . obviously)

-- TODO state as lemmas:
-- (hom_equiv : Π v w : V, (v ⟶ w) ≃ Σ (f : (obj_equiv v).1 → (obj_equiv w).1), hom_data f (obj_equiv v).2 (obj_equiv w).2)
-- (forget_obj_eq : Π v : V, (forget V).obj v = (obj_equiv v).1 . obviously)
-- (forget_map_eq : Π {v w : V} (f : v ⟶ w), (forget V).map f ≫ (eq_to_hom (forget_obj_eq w)) = (eq_to_hom (forget_obj_eq v)) ≫ ((hom_equiv v w) f).1 . obviously)

open decorated_category

-- Make this low priority, as there may be better ones for bundled categories and induced categories.
@[priority 10]
instance (V : Type (v+1)) [large_category V] [concrete_category V] : decorated_category V :=
{ obj_data := λ X, { v : V // (forget V).obj v = X },
  obj_equiv :=
  { to_fun := λ v, ⟨(forget V).obj v, ⟨v, rfl⟩⟩,
    inv_fun := λ p, p.2.1,
    left_inv := by tidy,
    right_inv := by tidy, },
  hom_data := λ X Y f X' Y', { f' : X'.1 ⟶ Y'.1 // eq_to_hom (X'.2.symm) ≫ (forget V).map f' ≫ eq_to_hom (Y'.2) = f },
  hom_equiv := λ p q,
  { to_fun := λ f, ⟨_, ⟨f, rfl⟩⟩,
    inv_fun := λ t, t.2.1,
    left_inv := by tidy,
    right_inv := by tidy, } }

variables (V : Type (v+1)) [large_category V] [concrete_category V]
variables (C : Type u) [𝒞 : category.{v} C]
include  𝒞

open decorated_category

class enriched_over :=
(e_hom  [] : Π (X Y : C), obj_data V (X ⟶ Y))
(notation X ` ⟶[V] ` Y:10 := (@obj_equiv V _ _).inv_fun ⟨X ⟶ Y, e_hom X Y⟩)
(e_comp_left : Π {X Y : C} (f : X ⟶ Y) (Z : C), hom_data (λ g : Y ⟶ Z, f ≫ g) (e_hom Y Z) (e_hom X Z))
(e_comp_right : Π (X : C) {Y Z : C} (g : Y ⟶ Z), hom_data (λ f : X ⟶ Y, f ≫ g) (e_hom X Y) (e_hom X Z))

variable [enriched_over V C]

notation X ` ⟶[`V`] ` Y:10 := (obj_equiv V).inv_fun ⟨X ⟶ Y, enriched_over.e_hom V X Y⟩
example [enriched_over V C] (X Y : C) : V := X ⟶[V] Y

variables {C}

def comp_left {X Y : C} (f : X ⟶ Y) (Z : C) : (Y ⟶[V] Z) ⟶ (X ⟶[V] Z) :=
(hom_equiv _ _).inv_fun ⟨λ g : Y ⟶ Z, f ≫ g, enriched_over.e_comp_left f Z⟩

def comp_right (X : C) {Y Z : C} (g : Y ⟶ Z) : (X ⟶[V] Y) ⟶ (X ⟶[V] Z) :=
(hom_equiv _ _).inv_fun ⟨λ f : X ⟶ Y, f ≫ g, enriched_over.e_comp_right X g⟩

omit 𝒞

/-- We check that we can construct the trivial enrichment of `Type` in `Type`. -/
instance : enriched_over (Type u) (Type u) :=
{ e_hom := λ X Y, ⟨X ⟶ Y, rfl⟩,
  e_comp_left := λ X Y f Z, ⟨(λ (g : Y ⟶ Z), f ≫ g), rfl⟩,
  e_comp_right := λ X Y Z g, ⟨(λ (f : X ⟶ Y), f ≫ g), rfl⟩, }

-- We check that this instance has good definitional properties:
example : comp_left Type (↾(λ n : ℕ, 2 * n)) ℕ = (λ f n, f (2 * n)) := rfl

end category_theory
