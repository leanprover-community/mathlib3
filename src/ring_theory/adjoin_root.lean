/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes

Adjoining roots of polynomials
-/
import data.polynomial.field_division
import ring_theory.adjoin
import ring_theory.principal_ideal_domain

/-!
# Adjoining roots of polynomials

This file defines the commutative ring `adjoin_root f`, the ring R[X]/(f) obtained from a
commutative ring `R` and a polynomial `f : R[X]`. If furthermore `R` is a field and `f` is
irreducible, the field structure on `adjoin_root f` is constructed.

## Main definitions and results

The main definitions are in the `adjoin_root` namespace.

*  `mk f : polynomial R →+* adjoin_root f`, the natural ring homomorphism.

*  `of f : R →+* adjoin_root f`, the natural ring homomorphism.

* `root f : adjoin_root f`, the image of X in R[X]/(f).

* `lift (i : R →+* S) (x : S) (h : f.eval₂ i x = 0) : (adjoin_root f) →+* S`, the ring
  homomorphism from R[X]/(f) to S extending `i : R →+* S` and sending `X` to `x`.

-/
noncomputable theory
open_locale big_operators

universes u v w

variables {R : Type u} {S : Type v} {K : Type w}

open polynomial ideal

/-- Adjoin a root of a polynomial `f` to a commutative ring `R`. We define the new ring
as the quotient of `R` by the principal ideal of `f`. -/
def adjoin_root [comm_ring R] (f : polynomial R) : Type u :=
ideal.quotient (span {f} : ideal (polynomial R))

namespace adjoin_root

section comm_ring
variables [comm_ring R] (f : polynomial R)

instance : comm_ring (adjoin_root f) := ideal.quotient.comm_ring _

instance : inhabited (adjoin_root f) := ⟨0⟩

instance : decidable_eq (adjoin_root f) := classical.dec_eq _

/-- Ring homomorphism from `R[x]` to `adjoin_root f` sending `X` to the `root`. -/
def mk : polynomial R →+* adjoin_root f := ideal.quotient.mk _

@[elab_as_eliminator]
theorem induction_on {C : adjoin_root f → Prop} (x : adjoin_root f)
  (ih : ∀ p : polynomial R, C (mk f p)) : C x :=
quotient.induction_on' x ih

/-- Embedding of the original ring `R` into `adjoin_root f`. -/
def of : R →+* adjoin_root f := (mk f).comp (ring_hom.of C)

instance : algebra R (adjoin_root f) := (of f).to_algebra

@[simp] lemma algebra_map_eq : algebra_map R (adjoin_root f) = of f := rfl

/-- The adjoined root. -/
def root : adjoin_root f := mk f X

variables {f}

instance adjoin_root.has_coe_t : has_coe_t R (adjoin_root f) := ⟨of f⟩

@[simp] lemma mk_self : mk f f = 0 :=
quotient.sound' (mem_span_singleton.2 $ by simp)

@[simp] lemma mk_C (x : R) : mk f (C x) = x := rfl

@[simp] lemma mk_X : mk f X = root f := rfl

@[simp] lemma aeval_eq (p : polynomial R) : aeval (root f) p = mk f p :=
polynomial.induction_on p (λ x, by { rw aeval_C, refl })
  (λ p q ihp ihq, by rw [alg_hom.map_add, ring_hom.map_add, ihp, ihq])
  (λ n x ih, by { rw [alg_hom.map_mul, aeval_C, alg_hom.map_pow, aeval_X,
    ring_hom.map_mul, mk_C, ring_hom.map_pow, mk_X], refl })

theorem adjoin_root_eq_top : algebra.adjoin R ({root f} : set (adjoin_root f)) = ⊤ :=
algebra.eq_top_iff.2 $ λ x, induction_on f x $ λ p,
(algebra.adjoin_singleton_eq_range R (root f)).symm ▸ ⟨p, aeval_eq p⟩

@[simp] lemma eval₂_root (f : polynomial R) : f.eval₂ (of f) (root f) = 0 :=
by rw [← algebra_map_eq, ← aeval_def, aeval_eq, mk_self]

lemma is_root_root (f : polynomial R) : is_root (f.map (of f)) (root f) :=
by rw [is_root, eval_map, eval₂_root]

variables [comm_ring S]

/-- Lift a ring homomorphism `i : R →+* S` to `adjoin_root f →+* S`. -/
def lift (i : R →+* S) (x : S) (h : f.eval₂ i x = 0) : (adjoin_root f) →+* S :=
begin
  apply ideal.quotient.lift _ (eval₂_ring_hom i x),
  intros g H,
  rcases mem_span_singleton.1 H with ⟨y, hy⟩,
  rw [hy, ring_hom.map_mul, coe_eval₂_ring_hom, h, zero_mul]
end

variables {i : R →+* S} {a : S} {h : f.eval₂ i a = 0}

@[simp] lemma lift_mk {g : polynomial R} : lift i a h (mk f g) = g.eval₂ i a :=
ideal.quotient.lift_mk _ _ _

@[simp] lemma lift_root : lift i a h (root f) = a := by rw [root, lift_mk, eval₂_X]

@[simp] lemma lift_of {x : R} : lift i a h x = i x :=
by rw [← mk_C x, lift_mk, eval₂_C]

@[simp] lemma lift_comp_of : (lift i a h).comp (of f) = i :=
ring_hom.ext $ λ _, @lift_of _ _ _ _ _ _ _ h _

end comm_ring

variables [field K] {f : polynomial K} [irreducible f]

instance is_maximal_span : is_maximal (span {f} : ideal (polynomial K)) :=
principal_ideal_ring.is_maximal_of_irreducible ‹irreducible f›

noncomputable instance field : field (adjoin_root f) :=
ideal.quotient.field (span {f} : ideal (polynomial K))

lemma coe_injective : function.injective (coe : K → adjoin_root f) :=
(of f).injective

variable (f)

lemma mul_div_root_cancel :
  ((X - C (root f)) * (f.map (of f) / (X - C (root f))) : polynomial (adjoin_root f)) =
    f.map (of f) :=
mul_div_eq_iff_is_root.2 $ is_root_root _

end adjoin_root
