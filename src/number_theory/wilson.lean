/-
Copyright (c) 2022 John Nicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicol
-/
import field_theory.finite.basic

/-!
# Wilson's theorem.

This file contains a proof of Wilson's theorem.

The heavy lifting is mostly done by the previous `wilsons_lemma`,
but here we also prove the other logical direction.

This could be generalized to similar results about finite abelian groups.

## References

* [Wilson's Theorem](https://en.wikipedia.org/wiki/Wilson%27s_theorem)

-/

open finset nat finite_field zmod
open_locale big_operators nat

namespace zmod

variables (p : ℕ) [fact p.prime]

/-- **Wilson's Lemma**: the product of `1`, ..., `p-1` is `-1` modulo `p`. -/
@[simp] lemma wilsons_lemma : ((p - 1)! : zmod p) = -1 :=
begin
  refine
  calc ((p - 1)! : zmod p) = (∏ x in Ico 1 (succ (p - 1)), x) :
    by rw [← finset.prod_Ico_id_eq_factorial, prod_nat_cast]
                               ... = (∏ x : (zmod p)ˣ, x) : _
                               ... = -1 : by simp_rw [← units.coe_hom_apply,
    ← (units.coe_hom (zmod p)).map_prod, prod_univ_units_id_eq_neg_one, units.coe_hom_apply,
    units.coe_neg, units.coe_one],
  have hp : 0 < p := (fact.out p.prime).pos,
  symmetry,
  refine prod_bij (λ a _, (a : zmod p).val) _ _ _ _,
  { intros a ha,
    rw [mem_Ico, ← nat.succ_sub hp, nat.succ_sub_one],
    split,
    { apply nat.pos_of_ne_zero, rw ← @val_zero p,
      assume h, apply units.ne_zero a (val_injective p h) },
    { exact val_lt _ } },
  { intros a ha, simp only [cast_id, nat_cast_val], },
  { intros _ _ _ _ h, rw units.ext_iff, exact val_injective p h },
  { intros b hb,
    rw [mem_Ico, nat.succ_le_iff, ← succ_sub hp, succ_sub_one, pos_iff_ne_zero] at hb,
    refine ⟨units.mk0 b _, finset.mem_univ _, _⟩,
    { assume h, apply hb.1, apply_fun val at h,
      simpa only [val_cast_of_lt hb.right, val_zero] using h },
    { simp only [val_cast_of_lt hb.right, units.coe_mk0], } }
end

@[simp] lemma prod_Ico_one_prime : (∏ x in Ico 1 p, (x : zmod p)) = -1 :=
begin
  conv in (Ico 1 p) { rw [← succ_sub_one p, succ_sub (fact.out p.prime).pos] },
  rw [← prod_nat_cast, finset.prod_Ico_id_eq_factorial, wilsons_lemma]
end

end zmod

namespace nat
variable {n : ℕ}

/-- For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` only if n is prime. -/
lemma prime_of_fac_equiv_neg_one
  (h : ((n - 1)! : zmod n) = -1) (h1 : n ≠ 1) : prime n :=
begin
  rcases eq_or_ne n 0 with rfl | h0,
  { norm_num at h },
  replace h1 : 1 < n := n.two_le_iff.mpr ⟨h0, h1⟩,
  by_contradiction h2,
  obtain ⟨m, hm1, hm2 : 1 < m, hm3⟩ := exists_dvd_of_not_prime2 h1 h2,
  have hm : m ∣ (n - 1)! := nat.dvd_factorial (pos_of_gt hm2) (le_pred_of_lt hm3),
  refine hm2.ne' (nat.dvd_one.mp ((nat.dvd_add_right hm).mp (hm1.trans _))),
  rw [←zmod.nat_coe_zmod_eq_zero_iff_dvd, cast_add, cast_one, h, add_left_neg],
end

/-- **Wilson's Theorem**: For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` iff n is prime. -/
theorem prime_iff_fac_equiv_neg_one (h : n ≠ 1) :
  prime n ↔ ((n - 1)! : zmod n) = -1 :=
begin
  refine ⟨λ h1, _, λ h2, prime_of_fac_equiv_neg_one h2 h⟩,
  haveI := fact.mk h1,
  exact zmod.wilsons_lemma n,
end

end nat
