/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kenny Lau
-/

import data.equiv.algebra

/-!
# Ring antihomomorphisms, isomorphisms, antiisomorphisms and involutions

This file defines ring antihomomorphisms, antiisomorphism and involutions
and proves basic properties of them.

## Notations

All types defined in this file are given a coercion to the underlying function.

## References

* https://en.wikipedia.org/wiki/Antihomomorphism
* https://en.wikipedia.org/wiki/Involution_(mathematics)#Ring_theory

## Tags

Ring isomorphism, automorphism, antihomomorphism, antiisomorphism, antiautomorphism, involution
-/

variables {R : Type*} {F : Type*}

/- The Proposition that a function from a ring to a ring is an antihomomorphism -/
class is_ring_anti_hom [ring R] [ring F] (f : R → F) : Prop :=
(map_one : f 1 = 1)
(map_mul : ∀ {x y : R}, f (x * y) = f y * f x)
(map_add : ∀ {x y : R}, f (x + y) = f x + f y)

namespace is_ring_anti_hom

variables [ring R] [ring F] (f : R → F) [is_ring_anti_hom f]

instance : is_add_group_hom f :=
{ to_is_add_hom := ⟨λ x y, is_ring_anti_hom.map_add f⟩ }

lemma map_zero : f 0 = 0 :=
is_add_group_hom.map_zero f

lemma map_neg {x} : f (-x) = -f x :=
is_add_group_hom.map_neg f x

lemma map_sub {x y} : f (x - y) = f x - f y :=
is_add_group_hom.map_sub f x y

end is_ring_anti_hom

variables (R F)

namespace ring_equiv

open ring_equiv

variables {R F} [ring R] [ring F] (Hs : R ≃r F) (x y : R)

lemma map_add : Hs (x + y) = Hs x + Hs y :=
is_ring_hom.map_add Hs

lemma map_zero : Hs 0 = 0 :=
is_ring_hom.map_zero Hs

lemma map_neg : Hs (-x) = -Hs x :=
is_ring_hom.map_neg Hs

lemma map_sub : Hs (x - y) = Hs x - Hs y :=
is_ring_hom.map_sub Hs

lemma map_mul : Hs (x * y) = Hs x * Hs y :=
is_ring_hom.map_mul Hs

lemma map_one : Hs 1 = 1 :=
is_ring_hom.map_one Hs

lemma map_neg_one : Hs (-1) = -1 :=
Hs.map_one ▸ Hs.map_neg 1

lemma bijective : function.bijective Hs :=
Hs.to_equiv.bijective

lemma map_zero_iff {x : R} : Hs x = 0 ↔ x = 0 :=
⟨λ H, Hs.bijective.1 $ H.symm ▸ Hs.map_zero.symm,
λ H, H.symm ▸ Hs.map_zero⟩

end ring_equiv

/-- A ring antiisomorphism -/
structure ring_anti_equiv [ring R] [ring F] extends R ≃ F :=
[anti_hom : is_ring_anti_hom to_fun]

namespace ring_anti_equiv

variables {R F} [ring R] [ring F] (Hs : ring_anti_equiv R F) (x y : R)

instance : has_coe_to_fun (ring_anti_equiv R F) :=
⟨_, λ Hs, Hs.to_fun⟩

instance : is_ring_anti_hom Hs := Hs.anti_hom

lemma map_add : Hs (x + y) = Hs x + Hs y :=
is_ring_anti_hom.map_add Hs

lemma map_zero : Hs 0 = 0 :=
is_ring_anti_hom.map_zero Hs

lemma map_neg : Hs (-x) = -Hs x :=
is_ring_anti_hom.map_neg Hs

lemma map_sub : Hs (x - y) = Hs x - Hs y :=
is_ring_anti_hom.map_sub Hs

lemma map_mul : Hs (x * y) = Hs y * Hs x :=
is_ring_anti_hom.map_mul Hs

lemma map_one : Hs 1 = 1 :=
is_ring_anti_hom.map_one Hs

lemma map_neg_one : Hs (-1) = -1 :=
Hs.map_one ▸ Hs.map_neg 1

lemma bijective : function.bijective Hs := Hs.to_equiv.bijective

lemma map_zero_iff {x : R} : Hs x = 0 ↔ x = 0 :=
⟨λ H, Hs.bijective.1 $ H.symm ▸ Hs.map_zero.symm,
λ H, H.symm ▸ Hs.map_zero⟩

end ring_anti_equiv

/-- A ring involution -/
structure ring_invo [ring R] :=
(to_fun : R → R)
[anti_hom : is_ring_anti_hom to_fun]
(to_fun_to_fun : ∀ x, to_fun (to_fun x) = x)

open ring_invo

namespace ring_invo

variables {R} [ring R] (Hi : ring_invo R) (x y : R)

instance : has_coe_to_fun (ring_invo R) :=
⟨_, λ Hi, Hi.to_fun⟩

instance : is_ring_anti_hom Hi := Hi.anti_hom

def to_ring_anti_equiv : ring_anti_equiv R R :=
{ inv_fun := Hi,
  left_inv := Hi.to_fun_to_fun,
  right_inv := Hi.to_fun_to_fun,
  .. Hi }

lemma map_add : Hi (x + y) = Hi x + Hi y :=
Hi.to_ring_anti_equiv.map_add x y

lemma map_zero : Hi 0 = 0 :=
Hi.to_ring_anti_equiv.map_zero

lemma map_neg : Hi (-x) = -Hi x :=
Hi.to_ring_anti_equiv.map_neg x

lemma map_sub : Hi (x - y) = Hi x - Hi y :=
Hi.to_ring_anti_equiv.map_sub x y

lemma map_mul : Hi (x * y) = Hi y * Hi x :=
Hi.to_ring_anti_equiv.map_mul x y

lemma map_one : Hi 1 = 1 :=
Hi.to_ring_anti_equiv.map_one

lemma map_neg_one : Hi (-1) = -1 :=
Hi.to_ring_anti_equiv.map_neg_one

lemma bijective : function.bijective Hi :=
Hi.to_ring_anti_equiv.bijective

lemma map_zero_iff {x : R} : Hi x = 0 ↔ x = 0 :=
Hi.to_ring_anti_equiv.map_zero_iff

end ring_invo

section comm_ring
variables (R F) [comm_ring R] [comm_ring F]

protected def ring_invo.id : ring_invo R :=
{ anti_hom := ⟨rfl, mul_comm, λ _ _, rfl⟩,
  to_fun_to_fun := λ _, rfl,
  .. equiv.refl R }

protected def ring_anti_equiv.refl : ring_anti_equiv R R :=
(ring_invo.id R).to_ring_anti_equiv

variables {R F}

theorem comm_ring.hom_to_anti_hom (f : R → F) [is_ring_hom f] : is_ring_anti_hom f :=
{ map_add := λ _ _, is_ring_hom.map_add f,
  map_mul := λ _ _, by rw [is_ring_hom.map_mul f, mul_comm],
  map_one := is_ring_hom.map_one f }

theorem comm_ring.anti_hom_to_hom (f : R → F) [is_ring_anti_hom f] : is_ring_hom f :=
{ map_add := λ _ _, is_ring_anti_hom.map_add f,
  map_mul := λ _ _, by rw [is_ring_anti_hom.map_mul f, mul_comm],
  map_one := is_ring_anti_hom.map_one f }

def comm_ring.equiv_to_anti_equiv (Hs : R ≃r F) : ring_anti_equiv R F :=
{ anti_hom := comm_ring.hom_to_anti_hom Hs,
  .. Hs.to_equiv }

def comm_ring.anti_equiv_to_equiv (Hs : ring_anti_equiv R F) : R ≃r F :=
{ hom := comm_ring.anti_hom_to_hom Hs,
  .. Hs.to_equiv }

end comm_ring
