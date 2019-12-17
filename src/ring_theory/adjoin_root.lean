/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes

Adjoining roots of polynomials
-/

import data.polynomial ring_theory.principal_ideal_domain

noncomputable theory

universes u v w

variables {R : Type u} {S : Type v} {γ : Type w}

open polynomial ideal

def adjoin_root [comm_ring R] (f : polynomial R) : Type u :=
ideal.quotient (span {f} : ideal (polynomial R))

namespace adjoin_root

section comm_ring
variables [comm_ring R] (f : polynomial R)

instance : comm_ring (adjoin_root f) := ideal.quotient.comm_ring _

instance : decidable_eq (adjoin_root f) := classical.dec_eq _

variable {f}


/-- The canonical homomorphism from `polynomial R` to `adjoin_root f` -/
def mk : polynomial R → adjoin_root f := ideal.quotient.mk _

/-- `root` is the `root` of `f` in `adjoin_root f` -/
def root : adjoin_root f := mk X
/-- The canonical map from `R` to `adjoin_root f`, where `f` is  a polynomial over `R` -/
def of (x : R) : adjoin_root f := mk (C x)

instance mk.is_ring_hom : is_ring_hom (mk : polynomial R → adjoin_root f) :=
ideal.quotient.is_ring_hom_mk _

instance of.is_ring_hom : is_ring_hom (of : R → adjoin_root f) :=
is_ring_hom.comp _ _

@[simp] lemma mk_self : (mk f : adjoin_root f) = 0 :=
quotient.sound' (mem_span_singleton.2 $ by simp)

lemma eval₂_root (f : polynomial R) : f.eval₂ of (root : adjoin_root f) = 0 :=
quotient.induction_on' (root : adjoin_root f)
  (λ (g : polynomial R) (hg : mk g = mk X),
    show finsupp.sum f (λ (e : ℕ) (a : R), mk (C a) * mk g ^ e) = 0,
    by simp only [hg, (is_semiring_hom.map_pow (mk : polynomial R → adjoin_root f) _ _).symm,
         (is_ring_hom.map_mul (mk : polynomial R → adjoin_root f)).symm];
      rw [finsupp.sum, finset.sum_hom (mk : polynomial R → adjoin_root f),
        show finset.sum _ _ = _, from sum_C_mul_X_eq _, mk_self])
  (show (root : adjoin_root f) = mk X, from rfl)

lemma is_root_root (f : polynomial R) : is_root (f.map of) (root : adjoin_root f) :=
by rw [is_root, eval_map, eval₂_root]

variables [comm_ring S]

def lift (i : R → S) [is_ring_hom i] (x : S) (h : f.eval₂ i x = 0) : (adjoin_root f) → S :=
ideal.quotient.lift _ (eval₂ i x) $ λ g H,
begin
  simp [mem_span_singleton] at H,
  cases H with y H,
  rw [H, eval₂_mul],
  simp [h]
end

variables {i : R → S} [is_ring_hom i] {a : S} {h : f.eval₂ i a = 0}

@[simp] lemma lift_mk {g : polynomial R} : lift i a h (mk g) = g.eval₂ i a :=
ideal.quotient.lift_mk

@[simp] lemma lift_root : lift i a h root = a := by simp [root, h]

@[simp] lemma lift_of {x : R} : lift i a h (of x) = i x :=
by show lift i a h (ideal.quotient.mk _ (C x)) = i x;
  convert ideal.quotient.lift_mk; simp

instance is_ring_hom_lift : is_ring_hom (lift i a h) :=
by unfold lift; apply_instance

end comm_ring

section field

variables [discrete_field R] {f : polynomial R} [irreducible f]

instance is_maximal_span : is_maximal (span {f} : ideal (polynomial R)) :=
principal_ideal_domain.is_maximal_of_irreducible ‹irreducible f›

noncomputable instance field : discrete_field (adjoin_root f) :=
ideal.quotient.field (span {f} : ideal (polynomial R))

lemma of_injective : function.injective (@of R _ f) := is_field_hom.injective _

instance lift_is_field_hom [field S] {i : R → S} [is_ring_hom i] {a : S}
  {h : f.eval₂ i a = 0} : is_field_hom (lift i a h) := by apply_instance

lemma mul_div_root_cancel (f : polynomial R) [irreducible f] :
  (X - C (root : adjoin_root f)) * (f.map of / (X - C root)) = f.map of :=
mul_div_eq_iff_is_root.2 $ is_root_root _

end field
section algebra

variables [comm_ring R] (f : polynomial R) [comm_ring S] [algebra R S]

instance : algebra R (adjoin_root f) :=
algebra.of_ring_hom (of ∘ algebra_map _) (is_ring_hom.comp _ _)

/-- The canonical R-algebra homomorphism from `polynomial R` to
  `adjoin_root f` -/
def amk : polynomial R →ₐ[R] adjoin_root f :=
{ commutes' := λ _, rfl, ..ring_hom.of mk }

lemma amk_eq_mk : ⇑(amk f) = mk := rfl

variables (b : S) (h : aeval R S b f = 0)

/-- Given an R-algebra `S`, `alift` is the unique R-algebra homomorphism sending
  the adjoined root to `b`, a given root of `f` in `S` -/
def alift : adjoin_root f →ₐ[R] S :=
{ commutes' := λ _, show lift _ b h (of _) = _, by rw [lift_of]; refl,
  ..ring_hom.of (lift (algebra_map S) b h) }

variables {b h}

@[simp] lemma alift_mk {g : polynomial R} : alift f b h (mk g) = aeval R S b g :=
@lift_mk _ _ _ f _ _ _ b h g

@[simp] lemma alift_root : alift f b h root = b :=
@lift_root _ _ _  f _ _ _ _ h

@[simp] lemma alift_of {a : R} : alift f b h (of a) = algebra_map S a :=
by show lift (algebra_map S) b h (ideal.quotient.mk _ (C a)) = algebra_map S a;
  convert ideal.quotient.lift_mk; simp

end algebra

end adjoin_root
