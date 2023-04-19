import algebra.category.Mon.basic
import tactic.elementwise

open category_theory

universes w v u

@[elementwise]
lemma foo {C : Type u} [category.{v} C]
  {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) : f ≫ 𝟙 N ≫ g = h :=
by simp [w]

@[elementwise]
lemma foo' {C : Type*} [category C]
  {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) : f ≫ 𝟙 N ≫ g = h :=
by simp [w]

local attribute [instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

lemma bar {C : Type u} [category.{v} C] [concrete_category.{w} C]
  {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) : g (f x) = h x :=
by apply foo_apply w

lemma bar' {M N K : Mon.{u}} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
  g (f x) = h x :=
by exact foo_apply w x

lemma bar'' {M N K : Mon.{0}} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
  g (f x) = h x :=
by apply foo_apply w

lemma bar''' {M N K : Mon} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
  g (f x) = h x :=
by apply foo_apply w

example (M N K : Mon.{u}) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
  g (f m) = h m :=
begin
  rw elementwise_of w,
end

example (M N K : Mon.{0}) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
  g (f m) = h m :=
begin
  elementwise! w,
  apply w,
end

example {α β : Type} (f g : α ⟶ β) (w : f = g) (a : α) : f a = g a :=
begin
  elementwise! w, -- make sure this works even when there is no simplification to do
  rw w,
end

example {α β : Type} (f g : α ⟶ β) (w : f ≫ 𝟙 β = g) (a : α) : f a = g a :=
begin
  elementwise! w,
  rw w,  -- this used to not work, because we produced `w : ⇑f a = ⇑g a`.
end
