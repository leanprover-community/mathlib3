import ring_theory.adjoin_root


open ideal double_quot polynomial adjoin_root

noncomputable theory

variables {R : Type*} [comm_ring R] (p : ideal R) (f : polynomial R)

/- The isomorphism `(R[α]/(p) ≅ (R/p)[X]/(f mod p)` for `α` a root of `f` -/

lemma l₁ : (adjoin_root f) ⧸ (p.map (of f)) ≃+*
  (adjoin_root f) ⧸ (p.map (((span ({f} : set (polynomial R)))^.quotient.mk).comp (C : R →+* polynomial R)))
   := ideal.quot_equiv_of_eq (by rw [of, adjoin_root.mk])

lemma l₂ : (adjoin_root f) ⧸(p.map (((span ({f} : set (polynomial R)))^.quotient.mk).comp (C : R →+* polynomial R)))
  ≃+* (adjoin_root f) ⧸
  (((p.map (C : R →+* polynomial R))).map (span ({f} : set (polynomial R)))^.quotient.mk) :=
ideal.quot_equiv_of_eq (by rw ideal.map_map)

lemma l₃ : (adjoin_root f) ⧸ (((p.map (C : R →+* polynomial R))).map (span ({f} : set (polynomial R)))^.quotient.mk) ≃+*
    (polynomial R ⧸ map C p) ⧸ ((span ({f} : set (polynomial R))).map (p.map (C : R →+* polynomial R))^.quotient.mk)
  := quot_quot_equiv_comm (span ({f} : set (polynomial R))) (p.map (C : R →+* polynomial R))

lemma l₄ : (polynomial R ⧸ map C p) ⧸ ((span ({f} : set (polynomial R))).map
  (p.map (C : R →+* polynomial R))^.quotient.mk) ≃+*
  (polynomial R ⧸ map C p) ⧸
  (span ({(ideal.quotient.mk (p.map polynomial.C)) f} : set (polynomial R ⧸ map C p))) :=
ideal.quot_equiv_of_eq (by rw [map_span, set.image_singleton])

def l₅ : polynomial (R ⧸ p) ⧸  (span ({f.map (p^.quotient.mk)} : set (polynomial (R ⧸ p)))) ≃+*
  (polynomial R ⧸ map C p) ⧸ (span ({(ideal.quotient.mk (p.map polynomial.C)) f} : set (polynomial R ⧸ map C p))) :=
quotient_equiv (span ({f.map (p^.quotient.mk)} : set (polynomial (R ⧸ p))))
  (span {ideal.quotient.mk (p.map polynomial.C) f})
  (polynomial_quotient_equiv_quotient_polynomial p)
  (by rw [map_span, set.image_singleton, ring_equiv.coe_to_ring_hom,
    polynomial_quotient_equiv_quotient_polynomial_map_mk p f])

def quot_adjoin_root_equiv_quot_polynomial_quot : (adjoin_root f) ⧸ (p.map (of f))
  ≃+* polynomial (R ⧸ p) ⧸  (span ({f.map (p^.quotient.mk)} : set (polynomial (R ⧸ p)))) :=
(l₁ p f).trans ((l₂ p f).trans ((l₃ p f).trans ((l₄ p f).trans (l₅ p f).symm)))

lemma quot_adjoin_root_equiv_quot_polynomial_quot_mk_of (x : R) :
  quot_adjoin_root_equiv_quot_polynomial_quot p f (ideal.quotient.mk (p.map (of f)) (of f x)) =
  ideal.quotient.mk (span ({f.map (p^.quotient.mk)} : set (polynomial (R ⧸ p)))) (C (ideal.quotient.mk p x))
  := sorry
