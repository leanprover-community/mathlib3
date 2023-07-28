/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import data.polynomial.splits
import ring_theory.adjoin.basic
import ring_theory.adjoin_root

/-!
# Adjoining elements to a field

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Some lemmas on the ring generating by adjoining an element to a field.

## Main statements

* `lift_of_splits`: If `K` and `L` are field extensions of `F` and we have `s : finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `algebra.adjoin F s` embeds in `L`.

-/

noncomputable theory
open_locale big_operators polynomial

section embeddings

variables (F : Type*) [field F]

/-- If `p` is the minimal polynomial of `a` over `F` then `F[a] ≃ₐ[F] F[x]/(p)` -/
def alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly
  {R : Type*} [comm_ring R] [algebra F R] (x : R) :
  algebra.adjoin F ({x} : set R) ≃ₐ[F] adjoin_root (minpoly F x) :=
alg_equiv.symm $ alg_equiv.of_bijective
  (alg_hom.cod_restrict
    (adjoin_root.lift_hom _ x $ minpoly.aeval F x) _
    (λ p, adjoin_root.induction_on _ p $ λ p,
      (algebra.adjoin_singleton_eq_range_aeval F x).symm ▸
        (polynomial.aeval _).mem_range.mpr ⟨p, rfl⟩))
  ⟨(alg_hom.injective_cod_restrict _ _ _).2 $ (injective_iff_map_eq_zero _).2 $ λ p,
    adjoin_root.induction_on _ p $ λ p hp, ideal.quotient.eq_zero_iff_mem.2 $
    ideal.mem_span_singleton.2 $ minpoly.dvd F x hp,
  λ y,
    let ⟨p, hp⟩ := (set_like.ext_iff.1
      (algebra.adjoin_singleton_eq_range_aeval F x) (y : R)).1 y.2 in
    ⟨adjoin_root.mk _ p, subtype.eq hp⟩⟩

open finset

/-- If `K` and `L` are field extensions of `F` and we have `s : finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `algebra.adjoin F s` embeds in `L`. -/
theorem lift_of_splits {F K L : Type*} [field F] [field K] [field L]
  [algebra F K] [algebra F L] (s : finset K) :
  (∀ x ∈ s, is_integral F x ∧ polynomial.splits (algebra_map F L) (minpoly F x)) →
  nonempty (algebra.adjoin F (↑s : set K) →ₐ[F] L) :=
begin
  classical,
  refine finset.induction_on s (λ H, _) (λ a s has ih H, _),
  { rw [coe_empty, algebra.adjoin_empty],
    exact ⟨(algebra.of_id F L).comp (algebra.bot_equiv F K)⟩ },
  rw forall_mem_insert at H, rcases H with ⟨⟨H1, H2⟩, H3⟩, cases ih H3 with f,
  choose H3 H4 using H3,
  rw [coe_insert, set.insert_eq, set.union_comm, algebra.adjoin_union_eq_adjoin_adjoin],
  letI := (f : algebra.adjoin F (↑s : set K) →+* L).to_algebra,
  haveI : finite_dimensional F (algebra.adjoin F (↑s : set K)) := (
    (submodule.fg_iff_finite_dimensional _).1
      (fg_adjoin_of_finite s.finite_to_set H3)).of_subalgebra_to_submodule,
  letI := field_of_finite_dimensional F (algebra.adjoin F (↑s : set K)),
  have H5 : is_integral (algebra.adjoin F (↑s : set K)) a := is_integral_of_is_scalar_tower H1,
  have H6 : (minpoly (algebra.adjoin F (↑s : set K)) a).splits
    (algebra_map (algebra.adjoin F (↑s : set K)) L),
  { refine polynomial.splits_of_splits_of_dvd _
      (polynomial.map_ne_zero $ minpoly.ne_zero H1 :
        polynomial.map (algebra_map _ _) _ ≠ 0)
      ((polynomial.splits_map_iff _ _).2 _)
      (minpoly.dvd _ _ _),
    { rw ← is_scalar_tower.algebra_map_eq, exact H2 },
    { rw [polynomial.aeval_map_algebra_map, minpoly.aeval] } },
  obtain ⟨y, hy⟩ := polynomial.exists_root_of_splits _ H6 (ne_of_lt (minpoly.degree_pos H5)).symm,
  refine ⟨subalgebra.of_restrict_scalars _ _ _⟩,
  refine (adjoin_root.lift_hom (minpoly (algebra.adjoin F (↑s : set K)) a) y hy).comp _,
  exact alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly (algebra.adjoin F (↑s : set K)) a
end

end embeddings
