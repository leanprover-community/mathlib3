/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/
import ring_theory.adjoin_root

/-!

# Double quotients

This file continues the work of `adjoin_root`, giving results about quotienting out
a ring by two ideals in succession.

-/
noncomputable theory
open_locale classical
open_locale big_operators polynomial

universes u v w

variables {R : Type u} {S : Type v} {K : Type w}

open polynomial ideal

open ideal double_quot polynomial

namespace adjoin_root

variables [comm_ring R] (I : ideal R) (f : R[X])

/-- The natural isomorphism `R[α]/(I[α]) ≅ R[α]/((I[x] ⊔ (f)) / (f))` for `α` a root of
`f : R[X]` and `I : ideal R`.

See `adjoin_root.quot_map_of_equiv` for the isomorphism with `(R/I)[X] / (f mod I)`. -/
def quot_map_of_equiv_quot_map_C_map_span_mk :
  adjoin_root f ⧸ I.map (of f) ≃+*
    adjoin_root f ⧸ (I.map (C : R →+* R[X])).map (span {f})^.quotient.mk :=
ideal.quot_equiv_of_eq (by rw [of, adjoin_root.mk, ideal.map_map])

@[simp]
lemma quot_map_of_equiv_quot_map_C_map_span_mk_mk (x : adjoin_root f) :
  quot_map_of_equiv_quot_map_C_map_span_mk I f (ideal.quotient.mk (I.map (of f)) x) =
    ideal.quotient.mk _ x :=
rfl

--this lemma should have the simp tag but this causes a lint issue
lemma quot_map_of_equiv_quot_map_C_map_span_mk_symm_mk (x : adjoin_root f) :
  (quot_map_of_equiv_quot_map_C_map_span_mk I f).symm
  (ideal.quotient.mk ((I.map (C : R →+* R[X])).map (span {f})^.quotient.mk) x) =
    ideal.quotient.mk (I.map (of f)) x :=
by rw [quot_map_of_equiv_quot_map_C_map_span_mk, ideal.quot_equiv_of_eq_symm, quot_equiv_of_eq_mk]

/-- The natural isomorphism `R[α]/((I[x] ⊔ (f)) / (f)) ≅ (R[x]/I[x])/((f) ⊔ I[x] / I[x])`
  for `α` a root of `f : R[X]` and `I : ideal R`-/
def quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk :
  (adjoin_root f) ⧸ (I.map (C : R →+* R[X])).map (span ({f} : set R[X]))^.quotient.mk ≃+*
    (R[X] ⧸ I.map (C : R →+* R[X])) ⧸ (span ({f} : set R[X])).map
    (I.map (C : R →+* R[X]))^.quotient.mk :=
quot_quot_equiv_comm (ideal.span ({f} : set R[X])) (I.map (C : R →+* R[X]))

@[simp]
lemma quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk_mk (p : R[X]) :
  quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk I f (ideal.quotient.mk _ (mk f p)) =
    quot_quot_mk (I.map C) (span {f}) p :=
rfl

@[simp]
lemma quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk_symm_quot_quot_mk (p : R[X]) :
  (quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk I f).symm
  (quot_quot_mk (I.map C) (span {f}) p) = (ideal.quotient.mk _ (mk f p)) :=
rfl

/-- The natural isomorphism `(R/I)[x]/(f mod I) ≅ (R[x]/I*R[x])/(f mod I[x])` where
  `f : R[X]` and `I : ideal R`-/
def polynomial.quot_quot_equiv_comm :
  (R ⧸ I)[X] ⧸ span ({f.map (I^.quotient.mk)} : set (polynomial (R ⧸ I))) ≃+*
    (R[X] ⧸ map C I) ⧸ span ({(ideal.quotient.mk (I.map C)) f} : set (R[X] ⧸ map C I)) :=
quotient_equiv (span ({f.map (I^.quotient.mk)} : set (polynomial (R ⧸ I))))
  (span {ideal.quotient.mk (I.map polynomial.C) f})
  (polynomial_quotient_equiv_quotient_polynomial I)
  (by rw [map_span, set.image_singleton, ring_equiv.coe_to_ring_hom,
    polynomial_quotient_equiv_quotient_polynomial_map_mk I f])

@[simp]
lemma polynomial.quot_quot_equiv_comm_mk (p : R[X]) :
  (polynomial.quot_quot_equiv_comm I f) (ideal.quotient.mk  _ (p.map I^.quotient.mk)) =
  (ideal.quotient.mk _ (ideal.quotient.mk _ p)) :=
by simp only [polynomial.quot_quot_equiv_comm, quotient_equiv_mk,
  polynomial_quotient_equiv_quotient_polynomial_map_mk]

@[simp]
lemma polynomial.quot_quot_equiv_comm_symm_mk_mk (p : R[X]) :
  (polynomial.quot_quot_equiv_comm I f).symm (ideal.quotient.mk _ (ideal.quotient.mk _ p)) =
    (ideal.quotient.mk  _ (p.map I^.quotient.mk)) :=
by simp only [polynomial.quot_quot_equiv_comm, quotient_equiv_symm_mk,
  polynomial_quotient_equiv_quotient_polynomial_symm_mk]

/-- The natural isomorphism `R[α]/I[α] ≅ (R/I)[X]/(f mod I)` for `α` a root of `f : R[X]`
  and `I : ideal R`.-/
def quot_adjoin_root_equiv_quot_polynomial_quot : (adjoin_root f) ⧸ (I.map (of f)) ≃+*
  (R ⧸ I)[X] ⧸ (span ({f.map (I^.quotient.mk)} : set (R ⧸ I)[X])) :=
(quot_map_of_equiv_quot_map_C_map_span_mk I f).trans
  ((quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk I f).trans
  ((ideal.quot_equiv_of_eq
  (show (span ({f} : set R[X])).map (I.map (C : R →+* R[X]))^.quotient.mk =
    span ({(ideal.quotient.mk (I.map polynomial.C)) f} : set (R[X] ⧸ map C I)),
    from by rw [map_span, set.image_singleton])).trans
  (polynomial.quot_quot_equiv_comm I f).symm))

@[simp]
lemma quot_adjoin_root_equiv_quot_polynomial_quot_mk_of (p : R[X]) :
  quot_adjoin_root_equiv_quot_polynomial_quot I f (ideal.quotient.mk (I.map (of f)) (mk f p)) =
    ideal.quotient.mk (span ({f.map (I^.quotient.mk)} : set (R ⧸ I)[X]))
    (p.map I^.quotient.mk) :=
by rw [quot_adjoin_root_equiv_quot_polynomial_quot, ring_equiv.trans_apply, ring_equiv.trans_apply,
    ring_equiv.trans_apply, quot_map_of_equiv_quot_map_C_map_span_mk_mk,
    quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk_mk, quot_quot_mk, ring_hom.comp_apply,
    quot_equiv_of_eq_mk, polynomial.quot_quot_equiv_comm_symm_mk_mk]

@[simp]
lemma quot_adjoin_root_equiv_quot_polynomial_quot_symm_mk_mk (p : R[X]) :
  (quot_adjoin_root_equiv_quot_polynomial_quot I f).symm
  (ideal.quotient.mk (span ({f.map (I^.quotient.mk)} : set (R ⧸ I)[X]))
    (p.map I^.quotient.mk)) = (ideal.quotient.mk (I.map (of f)) (mk f p)) :=
by rw [quot_adjoin_root_equiv_quot_polynomial_quot, ring_equiv.symm_trans_apply,
    ring_equiv.symm_trans_apply, ring_equiv.symm_trans_apply, ring_equiv.symm_symm,
    polynomial.quot_quot_equiv_comm_mk, ideal.quot_equiv_of_eq_symm,
    ideal.quot_equiv_of_eq_mk, ← ring_hom.comp_apply, ← double_quot.quot_quot_mk,
    quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk_symm_quot_quot_mk,
    quot_map_of_equiv_quot_map_C_map_span_mk_symm_mk]

/-- Promote `adjoin_root.quot_adjoin_root_equiv_quot_polynomial_quot` to an alg_equiv.  -/
@[simps apply symm_apply]
noncomputable def quot_equiv_quot_map (f : R[X]) (I : ideal R) :
  ((adjoin_root f) ⧸ (ideal.map (of f) I)) ≃ₐ[R]
     ((R ⧸ I) [X]) ⧸ (ideal.span ({polynomial.map I^.quotient.mk f} : set ((R ⧸ I) [X]))) :=
alg_equiv.of_ring_equiv (show ∀ x, (quot_adjoin_root_equiv_quot_polynomial_quot I f)
  (algebra_map R _ x) = algebra_map R _ x, from λ x, begin
    have : algebra_map R ((adjoin_root f) ⧸ (ideal.map (of f) I)) x = ideal.quotient.mk
      (ideal.map (adjoin_root.of f) I) ((mk f) (C x)) := rfl,
    simpa only [this, quot_adjoin_root_equiv_quot_polynomial_quot_mk_of, map_C]
  end)

@[simp]
lemma quot_equiv_quot_map_apply_mk (f g : R[X]) (I : ideal R)  :
  adjoin_root.quot_equiv_quot_map f I (ideal.quotient.mk _ (adjoin_root.mk f g)) =
    ideal.quotient.mk _ (g.map I^.quotient.mk) :=
by rw [adjoin_root.quot_equiv_quot_map_apply,
    adjoin_root.quot_adjoin_root_equiv_quot_polynomial_quot_mk_of]

@[simp]
lemma quot_equiv_quot_map_symm_apply_mk (f g : R[X]) (I : ideal R)  :
  (adjoin_root.quot_equiv_quot_map f I).symm (ideal.quotient.mk _ (map (ideal.quotient.mk I) g)) =
    ideal.quotient.mk _ (adjoin_root.mk f g) :=
by rw [adjoin_root.quot_equiv_quot_map_symm_apply,
    adjoin_root.quot_adjoin_root_equiv_quot_polynomial_quot_symm_mk_mk]

end adjoin_root

namespace power_basis

open adjoin_root alg_equiv

variables [comm_ring R] [comm_ring S] [algebra R S]

/-- Let `α` have minimal polynomial `f` over `R` and `I` be an ideal of `R`,
then `R[α] / (I) = (R[x] / (f)) / pS = (R/p)[x] / (f mod p)`. -/
@[simps apply symm_apply]
noncomputable def quotient_equiv_quotient_minpoly_map (pb : power_basis R S)
  (I : ideal R) :
  (S ⧸ I.map (algebra_map R S)) ≃ₐ[R] (polynomial (R ⧸ I)) ⧸
    (ideal.span ({(minpoly R pb.gen).map I^.quotient.mk} : set (polynomial (R ⧸ I)))) :=
(of_ring_equiv
  (show ∀ x, (ideal.quotient_equiv _ (ideal.map (adjoin_root.of (minpoly R pb.gen)) I)
    (adjoin_root.equiv' (minpoly R pb.gen) pb
    (by rw [adjoin_root.aeval_eq, adjoin_root.mk_self])
    (minpoly.aeval _ _)).symm.to_ring_equiv
    (by rw [ideal.map_map, alg_equiv.to_ring_equiv_eq_coe, ← alg_equiv.coe_ring_hom_commutes,
          ← adjoin_root.algebra_map_eq, alg_hom.comp_algebra_map]))
    (algebra_map R (S ⧸ I.map (algebra_map R S)) x) = algebra_map R _ x, from
  (λ x, by rw [← ideal.quotient.mk_algebra_map, ideal.quotient_equiv_apply,
    ring_hom.to_fun_eq_coe, ideal.quotient_map_mk, alg_equiv.to_ring_equiv_eq_coe,
    ring_equiv.coe_to_ring_hom, alg_equiv.coe_ring_equiv, alg_equiv.commutes,
    quotient.mk_algebra_map]))).trans (adjoin_root.quot_equiv_quot_map _ _)

@[simp]
lemma quotient_equiv_quotient_minpoly_map_apply_mk (pb : power_basis R S) (I : ideal R)
  (g : R[X]) : pb.quotient_equiv_quotient_minpoly_map I
  (ideal.quotient.mk _ (aeval pb.gen g)) = ideal.quotient.mk _ (g.map I^.quotient.mk) :=
by rw [power_basis.quotient_equiv_quotient_minpoly_map, alg_equiv.trans_apply,
    alg_equiv.of_ring_equiv_apply, quotient_equiv_mk, alg_equiv.coe_ring_equiv',
    adjoin_root.equiv'_symm_apply, power_basis.lift_aeval,
    adjoin_root.aeval_eq, adjoin_root.quot_equiv_quot_map_apply_mk]

@[simp]
lemma quotient_equiv_quotient_minpoly_map_symm_apply_mk (pb : power_basis R S) (I : ideal R)
  (g : R[X]) : (pb.quotient_equiv_quotient_minpoly_map I).symm
  (ideal.quotient.mk _ (g.map I^.quotient.mk)) = (ideal.quotient.mk _ (aeval pb.gen g)) :=
begin simp only [quotient_equiv_quotient_minpoly_map, to_ring_equiv_eq_coe, symm_trans_apply,
    quot_equiv_quot_map_symm_apply_mk, of_ring_equiv_symm_apply, quotient_equiv_symm_mk,
    to_ring_equiv_symm, ring_equiv.symm_symm, adjoin_root.equiv'_apply, coe_ring_equiv,
    lift_hom_mk, symm_to_ring_equiv],

end

end power_basis
