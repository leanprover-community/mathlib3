/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard
-/

import algebra.direct_sum.module
import tactic.fin_cases

/-!
# Not all complementary decompositions of a module over a semiring make up a direct sum

This shows that while `ℤ≤0` and `ℤ≥0` are complementary `ℕ`-submodules of `ℤ`, which in turn
implies as a collection they are `complete_lattice.independent` and that they span all of `ℤ`, they
do not form a decomposition into a direct sum.

This file demonstrates why `direct_sum.submodule_is_internal_of_independent_of_supr_eq_top` must
take `ring R` and not `semiring R`.
-/

lemma units_int.one_ne_neg_one : (1 : units ℤ) ≠ -1 := dec_trivial

/-- Submodules of positive and negative integers, keyed by sign. -/
def with_sign (i : units ℤ) : submodule ℕ ℤ :=
add_submonoid.to_nat_submodule $ show add_submonoid ℤ, from
  { carrier := {z | 0 ≤ i • z},
    zero_mem' := show 0 ≤ i • (0 : ℤ), from (smul_zero _).ge,
    add_mem' := λ x y (hx : 0 ≤ i • x) (hy : 0 ≤ i • y), show _ ≤ _, begin
      rw smul_add,
      exact add_nonneg hx hy
    end }

local notation `ℤ≥0` := with_sign 1
local notation `ℤ≤0` := with_sign (-1)

lemma mem_with_sign_one {x : ℤ} : x ∈ ℤ≥0 ↔ 0 ≤ x :=
show _ ≤ _ ↔ _, by rw one_smul

lemma mem_with_sign_neg_one {x : ℤ} : x ∈ ℤ≤0 ↔ x ≤ 0 :=
show _ ≤ _ ↔ _, by rw [units.neg_smul, le_neg, one_smul, neg_zero]

/-- The two submodules are complements. -/
lemma with_sign.is_compl : is_compl (ℤ≥0) (ℤ≤0) :=
begin
  split,
  { apply submodule.disjoint_def.2,
    intros x hx hx',
    exact le_antisymm (mem_with_sign_neg_one.mp hx') (mem_with_sign_one.mp hx), },
  { intros x hx,
    obtain hp | hn := (le_refl (0 : ℤ)).le_or_le x,
    exact submodule.mem_sup_left (mem_with_sign_one.mpr hp),
    exact submodule.mem_sup_right (mem_with_sign_neg_one.mpr hn), }
end

def with_sign.independent : complete_lattice.independent with_sign :=
begin
  intros i,
  rw [←finset.sup_univ_eq_supr, units_int.univ, finset.sup_insert, finset.sup_singleton],
  fin_cases i,
  { convert with_sign.is_compl.disjoint,
    convert bot_sup_eq,
    { exact supr_neg (not_not_intro rfl), },
    { rw supr_pos units_int.one_ne_neg_one.symm } },
  { convert with_sign.is_compl.disjoint.symm,
    convert sup_bot_eq,
    { exact supr_neg (not_not_intro rfl), },
    { rw supr_pos units_int.one_ne_neg_one } },
end

lemma with_sign.supr : supr with_sign = ⊤ :=
begin
  rw [←finset.sup_univ_eq_supr, units_int.univ, finset.sup_insert, finset.sup_singleton],
  exact with_sign.is_compl.sup_eq_top,
end

/-- But there is no embedding into `ℤ` from the direct sum. -/
lemma with_sign.not_injective :
  ¬function.injective (direct_sum.to_module ℕ (units ℤ) ℤ (λ i, (with_sign i).subtype)) :=
begin
  intro hinj,
  let p1 : ℤ≥0 := ⟨1, mem_with_sign_one.2 zero_le_one⟩,
  let n1 : ℤ≤0 := ⟨-1, mem_with_sign_neg_one.2 $ neg_nonpos.2 zero_le_one⟩,
  let z := direct_sum.lof ℕ _ (λ i, with_sign i) 1 p1 +
           direct_sum.lof ℕ _ (λ i, with_sign i) (-1) n1,
  have : z ≠ 0,
  { intro h,
    dsimp [z, direct_sum.lof_eq_of, direct_sum.of] at h,
    replace h := dfinsupp.ext_iff.mp h 1,
    rw [dfinsupp.zero_apply, dfinsupp.add_apply, dfinsupp.single_eq_same,
      dfinsupp.single_eq_of_ne (units_int.one_ne_neg_one.symm), add_zero, subtype.ext_iff,
      submodule.coe_zero] at h,
    apply zero_ne_one h.symm, },
  apply hinj.ne this,
  rw [linear_map.map_zero, linear_map.map_add, direct_sum.to_module_lof, direct_sum.to_module_lof],
  simp,
end

/-- And so they do not represent an internal direct sum. -/
lemma with_sign.not_internal : ¬direct_sum.submodule_is_internal with_sign :=
with_sign.not_injective ∘ and.elim_left
