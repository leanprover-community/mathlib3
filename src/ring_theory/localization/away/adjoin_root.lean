/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import ring_theory.adjoin_root
import ring_theory.localization.away.basic

/-!
The `R`-`alg_equiv` between the localization of `R` away from `r` and
`R` with an inverse of `r` adjoined.
-/

open polynomial adjoin_root localization

variables {R : Type*} [comm_ring R]

local attribute [instance] is_localization.alg_hom_subsingleton adjoin_root.alg_hom_subsingleton

/-- The `R`-`alg_equiv` between the localization of `R` away from `r` and
    `R` with an inverse of `r` adjoined. -/
noncomputable def localization.away_equiv_adjoin (r : R) : away r ≃ₐ[R] adjoin_root (C r * X - 1) :=
alg_equiv.of_alg_hom
  { commutes' := is_localization.away.away_map.lift_eq r
      (is_unit_of_mul_eq_one _ _ $ root_is_inv r), .. away_lift _ r _ }
  (lift_hom _ (is_localization.away.inv_self r) $ by simp only
    [map_sub, map_mul, aeval_C, aeval_X, is_localization.away.mul_inv_self, aeval_one, sub_self])
  (subsingleton.elim _ _)
  (subsingleton.elim _ _)

lemma is_localization.adjoin_inv (r : R) : is_localization.away r (adjoin_root $ C r * X - 1) :=
is_localization.is_localization_of_alg_equiv _ (localization.away_equiv_adjoin r)

lemma is_localization.away.finite_presentation (r : R) {S} [comm_ring S] [algebra R S]
  [is_localization.away r S] : algebra.finite_presentation R S :=
(adjoin_root.finite_presentation _).equiv $ (localization.away_equiv_adjoin r).symm.trans $
  is_localization.alg_equiv (submonoid.powers r) _ _
