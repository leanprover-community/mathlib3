import algebra.pi_instances
import category_theory.examples.rings
import category_theory.limits

universes u v w

namespace category_theory.examples

open category_theory
open category_theory.limits

variables {α : Type v}

def is_ring_hom_pi
  {α : Type u} {β : α → Type v} [R : Π a : α, ring (β a)]
  {γ : Type w} [ring γ]
  (f : Π a : α, γ → β a) [Rh : Π a : α, is_ring_hom (f a)] :
  is_ring_hom (λ x b, f b x) :=
begin
  tidy,
  -- gross:
  erw [is_ring_hom.map_one (f x)], refl,
  erw [is_ring_hom.map_mul (f x_1)], refl,
  erw [is_ring_hom.map_add (f x_1)], refl,
end

def CommRing.pi {β : Type u} (f : β → CommRing.{u}) : CommRing :=
{ α := Π b : β, (f b), str := by apply_instance }

def CommRing.pi_π {β : Type u} (f : β → CommRing) (b : β): CommRing.pi f ⟶ f b :=
{ val := λ g, g b, property := by tidy }

@[simp] def CommRing.hom_pi
  {α : Type u} {β : α → CommRing} {γ : CommRing}
  (f : Π a : α, γ ⟶ β a) : γ ⟶ CommRing.pi β :=
{ val := λ x b, f b x,
  property := begin convert is_ring_hom_pi (λ a, (f a).val) end }

local attribute [extensionality] subtype.eq

instance CommRing_has_products : has_products.{v+1 v} CommRing :=
{ fan := λ β f, { X := CommRing.pi f,
                  π := { app := CommRing.pi_π f } },
  is_product := λ β f, { lift := λ s, CommRing.hom_pi (λ j, s.π.app j),
                         uniq' := begin tidy, rw ←w, tidy, end } }.

end category_theory.examples