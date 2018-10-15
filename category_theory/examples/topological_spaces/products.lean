import category_theory.examples.topological_spaces
import category_theory.limits.products
import analysis.topology.continuity

universes u v w

open category_theory.limits
open category_theory.examples

def Top.pi {β : Type u} (f : β → Top.{u}) : Top :=
{ α := Π b : β, (f b), str := by apply_instance }

def Top.pi_π {β : Type u} (f : β → Top) (b : β): Top.pi f ⟶ f b :=
{ val := λ g, g b, property := continuous_apply _ }

@[simp] def Top.hom_pi
  {α : Type u} {β : α → Top} {γ : Top}
  (f : Π a : α, γ ⟶ β a) : γ ⟶ Top.pi β :=
{ val := λ x b, f b x,
  property := continuous_pi (λ a, (f a).property) }

local attribute [extensionality] subtype.eq

instance : has_products.{u+1 u} Top :=
{ fan := λ β f,
  { X := Top.pi f,
    π := Top.pi_π f },
  is_product := λ β f,
  { lift := λ s, Top.hom_pi (λ j, s.π j),
    uniq' := λ s m w, begin tidy, rw ←w, tidy, end } }.