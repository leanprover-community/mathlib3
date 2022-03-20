import ring_theory.adjoin_root


open ideal double_quot polynomial adjoin_root

noncomputable theory

variables {R : Type*} [comm_ring R] (I : ideal R) (f : polynomial R)

/- The isomorphism `R[α]/pR[α] ≅ (R/I)[X]/(f mod I)` for `α` a root of `f` -/

def quot_map_of_equiv_quot_map_C_map_span_mk : (adjoin_root f) ⧸ (I.map (of f)) ≃+*
  (adjoin_root f) ⧸ (((I.map (C : R →+* polynomial R))).map
  (span ({f} : set (polynomial R)))^.quotient.mk) :=
ideal.quot_equiv_of_eq (by rw [of, adjoin_root.mk, ideal.map_map])

lemma quot_map_of_equiv_quot_map_C_map_span_mk_mk (x : adjoin_root f) :
  quot_map_of_equiv_quot_map_C_map_span_mk I f (ideal.quotient.mk (I.map (of f)) x) =
  ideal.quotient.mk (((I.map (C : R →+* polynomial R))).map
  (span ({f} : set (polynomial R)))^.quotient.mk) x := rfl

def quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk : (adjoin_root f) ⧸
  (((I.map (C : R →+* polynomial R))).map (span ({f} : set (polynomial R)))^.quotient.mk) ≃+*
  (polynomial R ⧸ map C I) ⧸ ((span ({f} : set (polynomial R))).map
  (I.map (C : R →+* polynomial R))^.quotient.mk) :=
quot_quot_equiv_comm (span ({f} : set (polynomial R))) (I.map (C : R →+* polynomial R))

lemma quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk_mk (p : polynomial R) :
  quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk I f (ideal.quotient.mk _ (mk f p)) =
  quot_quot_mk (I.map (C : R →+* polynomial R)) (span ({f} : set (polynomial R))) p := rfl

def quot_map_C_quot_map_span_mk_equiv_quot_map_C_quot_mk_span : (polynomial R ⧸ map C I) ⧸
  ((span ({f} : set (polynomial R))).map (I.map (C : R →+* polynomial R))^.quotient.mk) ≃+*
  (polynomial R ⧸ map C I) ⧸
  (span ({(ideal.quotient.mk (I.map polynomial.C)) f} : set (polynomial R ⧸ map C I))) :=
ideal.quot_equiv_of_eq (by rw [map_span, set.image_singleton])

lemma quot_map_C_quot_map_span_mk_equiv_quot_map_C_quot_mk_span_quot_quot_mk (p : polynomial R) :
  quot_map_C_quot_map_span_mk_equiv_quot_map_C_quot_mk_span I f (quot_quot_mk _ _ p) =
  ideal.quotient.mk _ (ideal.quotient.mk _ p) := rfl

def polynomial_over_quot_quot_mk_span_equiv_quot_map_C_quot_mk_span : polynomial (R ⧸ I) ⧸
  (span ({f.map (I^.quotient.mk)} : set (polynomial (R ⧸ I)))) ≃+*
  (polynomial R ⧸ map C I) ⧸
  (span ({(ideal.quotient.mk (I.map polynomial.C)) f} : set (polynomial R ⧸ map C I))) :=
quotient_equiv (span ({f.map (I^.quotient.mk)} : set (polynomial (R ⧸ I))))
  (span {ideal.quotient.mk (I.map polynomial.C) f})
  (polynomial_quotient_equiv_quotient_polynomial I)
  (by rw [map_span, set.image_singleton, ring_equiv.coe_to_ring_hom,
    polynomial_quotient_equiv_quotient_polynomial_map_mk I f])

lemma polynomial_over_quot_quot_mk_span_equiv_quot_map_C_quot_mk_span_symm_mk_mk (p : polynomial R) :
  (polynomial_over_quot_quot_mk_span_equiv_quot_map_C_quot_mk_span I f).symm
  (ideal.quotient.mk _ (ideal.quotient.mk _ p)) = (ideal.quotient.mk
  _ (p.map I^.quotient.mk)) :=
begin
  simp only [polynomial_over_quot_quot_mk_span_equiv_quot_map_C_quot_mk_span, quotient_equiv_mk],
  rw quotient_equiv_symm_mk,
  rw polynomial_quotient_equiv_quotient_polynomial_symm_mk,
end

def quot_adjoin_root_equiv_quot_polynomial_quot : (adjoin_root f) ⧸ (I.map (of f)) ≃+*
polynomial (R ⧸ I) ⧸ (span ({f.map (I^.quotient.mk)} : set (polynomial (R ⧸ I)))) :=
(quot_map_of_equiv_quot_map_C_map_span_mk I f).trans
  ((quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk I f).trans
  ((quot_map_C_quot_map_span_mk_equiv_quot_map_C_quot_mk_span I f).trans
  (polynomial_over_quot_quot_mk_span_equiv_quot_map_C_quot_mk_span I f).symm))

lemma quot_adjoin_root_equiv_quot_polynomial_quot_mk_of (x : R) :
  quot_adjoin_root_equiv_quot_polynomial_quot I f (ideal.quotient.mk (I.map (of f)) (of f x)) =
  ideal.quotient.mk (span ({f.map (I^.quotient.mk)} : set (polynomial (R ⧸ I))))
  (C (ideal.quotient.mk I x)) := rfl
