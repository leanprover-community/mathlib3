/-
Copyright (c) 2022 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/

import data.rat.basic
import group_theory.exponent
import group_theory.order_of_element
import group_theory.quotient_group
import field_theory.finite.basic

/-!
# Torsion groups

This file defines torsion groups, i.e. groups where all elements have finite order.

## Main definitions

* `monoid.is_torsion` is a predicate asserting a monoid `G` is a torsion monoid, i.e. that all
  elements are of finite order. Torsion groups are also known as periodic groups.
* `add_monoid.is_torsion` the additive version of `monoid.is_torsion`.

## Future work

* Define `tor G` for the torsion subgroup of a group
* torsion-free groups
-/

universe u

variable {G : Type u}

open_locale classical

namespace monoid

variables (G) [monoid G]

/--A predicate on a monoid saying that all elements are of finite order.-/
@[to_additive "A predicate on an additive monoid saying that all elements are of finite order."]
def is_torsion := ∀ g : G, is_of_fin_order g

end monoid

open monoid

variables [group G] {N : subgroup G}

/--Subgroups of torsion groups are torsion groups. -/
@[to_additive "Subgroups of additive torsion groups are additive torsion groups."]
lemma is_torsion.subgroup (tG : is_torsion G) (H : subgroup G) : is_torsion H :=
λ h, (is_of_fin_order_iff_coe _ h).mpr $ tG h

/--Quotient groups of torsion groups are torsion groups. -/
@[to_additive "Quotient groups of additive torsion groups are additive torsion groups."]
lemma is_torsion.quotient_group [nN : N.normal] (tG : is_torsion G) : is_torsion (G ⧸ N) :=
λ h, quotient_group.induction_on' h $ λ g, (tG g).quotient N g

/--If a group exponent exists, the group is torsion. -/
@[to_additive exponent_exists.is_add_torsion]
lemma exponent_exists.is_torsion (h : exponent_exists G) : is_torsion G := begin
  obtain ⟨n, npos, hn⟩ := h,
  intro g,
  exact (is_of_fin_order_iff_pow_eq_one g).mpr ⟨n, npos, hn g⟩,
end

/--The group exponent exists for any bounded torsion group. -/
@[to_additive is_add_torsion.exponent_exists]
lemma is_torsion.exponent_exists
  (tG : is_torsion G) (bounded : (set.range (λ g : G, order_of g)).finite) :
  exponent_exists G :=
exponent_exists_iff_ne_zero.mpr $
  (exponent_ne_zero_iff_range_order_of_finite (λ g, order_of_pos' (tG g))).mpr bounded

/--Finite groups are torsion groups.-/
@[to_additive is_add_torsion_of_fintype]
lemma is_torsion_of_fintype [fintype G] : is_torsion G :=
exponent_exists.is_torsion $ exponent_exists_iff_ne_zero.mpr exponent_ne_zero_of_fintype

section infinite_torsion_groups

/-- The group ℚ ⧸ ℤ. -/
@[reducible] def qmodz := ℚ ⧸ (algebra.linear_map ℤ ℚ).range

namespace qmodz

open rat

/-- ℚ ⧸ ℤ is a torsion group -/
lemma is_torsion : add_monoid.is_torsion qmodz :=
λ q, begin
  induction q using quotient.induction_on',
  simp_rw [is_of_fin_add_order_iff_nsmul_eq_zero, submodule.quotient.mk'_eq_mk,
    ←submodule.quotient.mk_smul, submodule.quotient.mk_eq_zero, linear_map.mem_range,
    algebra.linear_map_apply, algebra_map_int_eq, ring_hom.eq_int_cast, nsmul_eq_mul, mul_comm],
  exact ⟨q.denom, q.pos, q.num, mul_denom_eq_num.symm⟩,
end

end qmodz

namespace polynomial

open_locale polynomial

variables {Fq : Type*} [field Fq] [fintype Fq]

/-- Fq[X] is a torsion group -/
lemma is_torsion : add_monoid.is_torsion Fq[X] :=
λ f, begin
  rw is_of_fin_add_order_iff_nsmul_eq_zero,
  refine ⟨fintype.card Fq, fintype.card_pos, _⟩,
  rw [nsmul_eq_smul_cast Fq _ f, finite_field.cast_card_eq_zero, zero_smul],
end

end polynomial

end infinite_torsion_groups
