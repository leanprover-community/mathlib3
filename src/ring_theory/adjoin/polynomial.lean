/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ring_theory.adjoin.basic
import ring_theory.polynomial.basic

/-!
# Adjoining elements to form subalgebras: relation to polynomials

In this file we prove a few results representing `algebra.adjoin R s` as the range of
`mv_polynomial.aeval` or `polynomial.aeval`.

## Tags

adjoin, algebra, polynomials
-/

universes u v w

namespace algebra

open subsemiring submodule
variables (R : Type u) {A : Type v} (s : set A) [comm_semiring R] [comm_semiring A] [algebra R A]

theorem adjoin_eq_range :
  adjoin R s = (mv_polynomial.aeval (coe : s → A)).range :=
le_antisymm
  (adjoin_le $ λ x hx, ⟨mv_polynomial.X ⟨x, hx⟩, mv_polynomial.eval₂_X _ _ _⟩)
  (λ x ⟨p, (hp : mv_polynomial.aeval coe p = x)⟩, hp ▸ mv_polynomial.induction_on p
    (λ r, by { rw [mv_polynomial.aeval_def, mv_polynomial.eval₂_C],
               exact (adjoin R s).algebra_map_mem r })
    (λ p q hp hq, by rw alg_hom.map_add; exact subalgebra.add_mem _ hp hq)
    (λ p ⟨n, hn⟩ hp, by rw [alg_hom.map_mul, mv_polynomial.aeval_def _ (mv_polynomial.X _),
      mv_polynomial.eval₂_X]; exact subalgebra.mul_mem _ hp (subset_adjoin hn)))

lemma adjoin_range_eq_range_aeval {σ : Type*} (f : σ → A) :
  adjoin R (set.range f) = (mv_polynomial.aeval f).range :=
begin
  ext x,
  simp only [adjoin_eq_range, alg_hom.mem_range],
  split,
  { rintros ⟨p, rfl⟩,
    use mv_polynomial.rename (function.surj_inv (@@set.surjective_onto_range f)) p,
    rw [← alg_hom.comp_apply],
    refine congr_fun (congr_arg _ _) _,
    ext,
    simp only [mv_polynomial.rename_X, function.comp_app, mv_polynomial.aeval_X, alg_hom.coe_comp],
    simpa [subtype.ext_iff] using function.surj_inv_eq (@@set.surjective_onto_range f) i },
  { rintros ⟨p, rfl⟩,
    use mv_polynomial.rename (set.range_factorization f) p,
    rw [← alg_hom.comp_apply],
    refine congr_fun (congr_arg _ _) _,
    ext,
    simp only [mv_polynomial.rename_X, function.comp_app, mv_polynomial.aeval_X, alg_hom.coe_comp,
      set.range_factorization_coe] }
end

theorem adjoin_singleton_eq_range_aeval (x : A) : adjoin R {x} = (polynomial.aeval x).range :=
le_antisymm
  (adjoin_le $ set.singleton_subset_iff.2 ⟨polynomial.X, polynomial.eval₂_X _ _⟩)
  (λ y ⟨p, (hp : polynomial.aeval x p = y)⟩, hp ▸ polynomial.induction_on p
    (λ r, by { rw [polynomial.aeval_def, polynomial.eval₂_C],
               exact (adjoin R _).algebra_map_mem r })
    (λ p q hp hq, by rw alg_hom.map_add; exact subalgebra.add_mem _ hp hq)
    (λ n r ih, by { rw [pow_succ', ← mul_assoc, alg_hom.map_mul,
      polynomial.aeval_def _ polynomial.X, polynomial.eval₂_X],
      exact subalgebra.mul_mem _ ih (subset_adjoin rfl) }))

end algebra
