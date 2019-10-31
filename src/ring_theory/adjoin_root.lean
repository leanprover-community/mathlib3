/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes

Adjoining roots of polynomials
-/

import data.polynomial ring_theory.principal_ideal_domain

noncomputable theory

universes u v w

variables {α : Type u} {β : Type v} {γ : Type w}

open polynomial ideal

def adjoin_root [comm_ring α] (f : polynomial α) : Type u :=
ideal.quotient (span {f} : ideal (polynomial α))

namespace adjoin_root

section comm_ring
variables [comm_ring α] (f : polynomial α)

instance : comm_ring (adjoin_root f) := ideal.quotient.comm_ring _

instance : decidable_eq (adjoin_root f) := classical.dec_eq _

variable {f}

def mk : polynomial α → adjoin_root f := ideal.quotient.mk _

def root : adjoin_root f := mk X

def of (x : α) : adjoin_root f := mk (C x)

instance mk.is_ring_hom : is_ring_hom (mk : polynomial α → adjoin_root f) :=
ideal.quotient.is_ring_hom_mk _

instance of.is_ring_hom : is_ring_hom (of : α → adjoin_root f) :=
is_ring_hom.comp _ _

@[simp] lemma mk_self : (mk f : adjoin_root f) = 0 :=
quotient.sound' (mem_span_singleton.2 $ by simp)

lemma eval₂_root (f : polynomial α) : f.eval₂ of (root : adjoin_root f) = 0 :=
quotient.induction_on' (root : adjoin_root f)
  (λ (g : polynomial α) (hg : mk g = mk X),
    show finsupp.sum f (λ (e : ℕ) (a : α), mk (C a) * mk g ^ e) = 0,
    by simp only [hg, (is_semiring_hom.map_pow (mk : polynomial α → adjoin_root f) _ _).symm,
         (is_ring_hom.map_mul (mk : polynomial α → adjoin_root f)).symm];
      rw [finsupp.sum, finset.sum_hom (mk : polynomial α → adjoin_root f),
        show finset.sum _ _ = _, from sum_C_mul_X_eq _, mk_self])
  (show (root : adjoin_root f) = mk X, from rfl)

lemma is_root_root (f : polynomial α) : is_root (f.map of) (root : adjoin_root f) :=
by rw [is_root, eval_map, eval₂_root]

variables [comm_ring β]

def lift (i : α → β) [is_ring_hom i] (x : β) (h : f.eval₂ i x = 0) : (adjoin_root f) → β :=
ideal.quotient.lift _ (eval₂ i x) $ λ g H,
begin
  simp [mem_span_singleton] at H,
  cases H with y H,
  rw [H, eval₂_mul],
  simp [h]
end

variables {i : α → β} [is_ring_hom i] {a : β} {h : f.eval₂ i a = 0}

@[simp] lemma lift_mk {g : polynomial α} : lift i a h (mk g) = g.eval₂ i a :=
ideal.quotient.lift_mk

@[simp] lemma lift_root : lift i a h root = a := by simp [root, h]

@[simp] lemma lift_of {x : α} : lift i a h (of x) = i x :=
by show lift i a h (ideal.quotient.mk _ (C x)) = i x;
  convert ideal.quotient.lift_mk; simp

instance is_ring_hom_lift : is_ring_hom (lift i a h) :=
by unfold lift; apply_instance

end comm_ring

section field

variables [discrete_field α] {f : polynomial α} [irreducible f]

instance is_maximal_span : is_maximal (span {f} : ideal (polynomial α)) :=
principal_ideal_domain.is_maximal_of_irreducible ‹irreducible f›

noncomputable instance field : discrete_field (adjoin_root f) :=
ideal.quotient.field (span {f} : ideal (polynomial α))

instance : is_field_hom (of : α → adjoin_root f) := by apply_instance

lemma of_injective : function.injective (@of α _ f) := is_field_hom.injective _

instance lift_is_field_hom [field β] {i : α → β} [is_ring_hom i] {a : β}
  {h : f.eval₂ i a = 0} : is_field_hom (lift i a h) := by apply_instance

lemma mul_div_root_cancel (f : polynomial α) [irreducible f] :
  (X - C (root : adjoin_root f)) * (f.map of / (X - C root)) = f.map of :=
mul_div_eq_iff_is_root.2 $ is_root_root _

end field
#print not_not
section algebra

variables [comm_ring α] (f : polynomial α) [comm_ring β] [algebra α β]

instance : algebra α (adjoin_root f) :=
algebra.of_ring_hom (of ∘ algebra_map _) (is_ring_hom.comp _ _)

def amk : polynomial α →ₐ[α] adjoin_root f :=
{ commutes' := λ _, rfl, ..ring_hom.of mk }

lemma amk_eq_mk : ⇑(amk f) = mk := rfl

variables (b : β) (h : aeval α β b f = 0)

def alift : adjoin_root f →ₐ[α] β :=
{ commutes' := λ _, show lift _ b h (of _) = _, by rw [lift_of]; refl,
  ..ring_hom.of (lift (algebra_map β) b h) }

variables {b h}

@[simp] lemma alift_mk {g : polynomial α} : alift f b h (mk g) = g.eval₂ (algebra_map β) b :=
@lift_mk _ _ _ f _ _ _ b h g

@[simp] lemma alift_root : alift f b h root = b :=
@lift_root _ _ _  f _ _ _ _ h

@[simp] lemma alift_of {a : α} : alift f b h (of a) = algebra_map β a :=
by show lift (algebra_map β) b h (ideal.quotient.mk _ (C a)) = algebra_map β a;
  convert ideal.quotient.lift_mk; simp

end algebra

end adjoin_root
