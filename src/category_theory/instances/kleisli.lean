/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

The Kleisli construction on the Type category
-/
import category_theory.category

universes u v

namespace category_theory

def Kleisli (m) [monad.{u v} m] := Type u

def Kleisli.mk (m) [monad.{u v} m] (α : Type u) : Kleisli m := α

instance Kleisli.category_struct {m} [monad m] : category_struct (Kleisli m) :=
{ hom := λ α β, α → m β,
  id := λ α x, (pure x : m α),
  comp := λ X Y Z f g, f >=> g }

instance Kleisli.category {m} [monad m] [is_lawful_monad m] : category (Kleisli m) :=
by refine { hom := λ α β, α → m β,
            id := λ α x, (pure x : m α),
            comp := λ X Y Z f g, f >=> g,
            id_comp' := _, comp_id' := _, assoc' := _ };
   intros; ext; simp only [(>=>)] with functor_norm

@[simp] lemma Kleisli.id_def {m} [monad m] [is_lawful_monad m] (α : Kleisli m) :
  𝟙 α = @pure m _ α := rfl

lemma Kleisli.comp_def {m} [monad m] [is_lawful_monad m] (α β γ : Kleisli m)
  (xs : α ⟶ β) (ys : β ⟶ γ) (a : α) :
  (xs ≫ ys) a = xs a >>= ys := rfl

end category_theory
