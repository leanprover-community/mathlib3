import ring_theory.ideal.operations
import ring_theory.ideal.basic
import ring_isom
import ring_theory.dedekind_domain
import algebra.group
import data.multiset.basic
import data.polynomial.induction

open function ideal comm_ring multiset unique_factorization_monoid double_quot polynomial adjoin_root

open_locale classical noncomputable theory

universes u_1 u_2 u_3

variables {R : Type u_1} [comm_ring R] (p : ideal R) (hp : p.is_prime) (f : polynomial R)
variables {S : Type u_2} [comm_ring S] (i : R →+* S)
  (h : (p.map (ring_hom.comp (adjoin_root.mk f) polynomial.C)).quotient ≃* (map i p).quotient)

lemma map_abc (n : ℕ):  (ideal.quotient.mk (map (polynomial.C : R →+* polynomial R) p))
    (polynomial.C (f.coeff n)) * (ideal.quotient.mk (map (polynomial.C : R →+* polynomial R) p) polynomial.X^n) =
    ideal.quotient.mk (map (polynomial.C : R →+* polynomial R) p) ((polynomial.C (f.coeff n)) * polynomial.X^n) :=
begin
  rw [ring_hom.map_mul, ring_hom.map_pow],
end

lemma map_f : polynomial_quotient_equiv_quotient_polynomial p (f.map p^.quotient.mk) =
  ideal.quotient.mk (p.map polynomial.C) f :=
begin
  rw [polynomial_quotient_equiv_quotient_polynomial, ring_equiv.coe_mk, polynomial.eval₂_ring_hom,
    ring_hom.coe_mk, add_monoid_hom.to_fun_eq_coe, polynomial.eval₂_add_monoid_hom_apply,
    polynomial.eval₂_map, polynomial.eval₂_eq_sum, polynomial.sum],
  suffices : ∀ n : ℕ, (ideal.quotient.lift p ((ideal.quotient.mk (p.map (polynomial.C : R →+* polynomial R))).comp polynomial.C) quotient_map_C_eq_zero).comp (ideal.quotient.mk p)
    (f.coeff n) * (((ideal.quotient.mk (p.map (polynomial.C : R →+* polynomial R))) polynomial.X)^n) =
    (ideal.quotient.mk (p.map (polynomial.C : R →+* polynomial R))) (polynomial.C (f.coeff n) * (polynomial.X ^ n)),
  { conv_rhs {rw polynomial.as_sum_support f},
    rw ring_hom.map_sum,
    simp only [this, polynomial.monomial_eq_C_mul_X] },
  intro n,
  simp only [ring_hom.map_mul, ring_hom.map_pow, comp_app, ring_hom.coe_comp, quotient.lift_mk],
  refl,
end
--just use image of span is span of image. Can probably just be ditched at some point
lemma ideal_eq : (span ({f.map (p^.quotient.mk)} : set (polynomial p.quotient))).map (polynomial_quotient_equiv_quotient_polynomial p).to_ring_hom
  = span {ideal.quotient.mk (p.map polynomial.C) f} := sorry

def map_p : ideal (polynomial R) := (p.map (polynomial.C : R →+* polynomial R))
def ideal_f : ideal (polynomial R) := (span ({f} : set (polynomial R)))

lemma l₁ : (p.map (of f)).quotient ≃+*
  (p.map (((span ({f} : set (polynomial R)))^.quotient.mk).comp (C : R →+* polynomial R))).quotient
   := ideal.quot_equiv_of_eq (by rw [of, adjoin_root.mk])

lemma l₂ : (p.map (((span ({f} : set (polynomial R)))^.quotient.mk).comp (C : R →+* polynomial R))).quotient
  ≃+* (((p.map (C : R →+* polynomial R))).map (span ({f} : set (polynomial R)))^.quotient.mk).quotient :=
ideal.quot_equiv_of_eq (by rw ideal.map_map)

lemma l₃ : (((p.map (C : R →+* polynomial R))).map (span ({f} : set (polynomial R)))^.quotient.mk).quotient ≃+*
  ((span ({f} : set (polynomial R))).map (p.map (C : R →+* polynomial R))^.quotient.mk).quotient
  := by {exact quot_quot_equiv_comm (span ({f} : set (polynomial R))) (p.map (C : R →+* polynomial R)), }

lemma l₄ : ((span ({f} : set (polynomial R))).map (p.map (C : R →+* polynomial R))^.quotient.mk).quotient ≃+*
  (span {(ideal.quotient.mk (p.map polynomial.C)) f}).quotient := sorry

def l₅ : (span ({f.map (p^.quotient.mk)} : set (polynomial p.quotient))).quotient ≃+*
  (span {(ideal.quotient.mk (p.map polynomial.C)) f}).quotient :=
quotient_equiv (span ({f.map (p^.quotient.mk)} : set (polynomial p.quotient)))
  (span {ideal.quotient.mk (p.map polynomial.C) f})
  (polynomial_quotient_equiv_quotient_polynomial p) (ideal_eq p f).symm
