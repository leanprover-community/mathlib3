/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import algebra.squarefree
import data.zmod.basic
import ring_theory.int.basic

/-!
# Ring theoretic facts about `zmod n`

## Main statements

* `zmod.is_reduced` - `zmod n` is reduced for all squarefree `n`.

-/

instance {n : ℕ} [fact $ squarefree n] : is_reduced (zmod n) :=
⟨begin
  casesI n,
  { exact (not_squarefree_zero (fact.out _ : squarefree 0)).elim, },
  rintro ⟨x, hx⟩ ⟨_ | m, h⟩,
  { rw [pow_zero, fin.one_eq_zero_iff] at h,
    rw [h, nat.lt_one_iff] at hx,
    simp only [hx, fin.mk_zero], },
  { have : ((⟨x, hx⟩ : zmod n.succ) = (x : zmod n.succ)),
    { ext,
      simp only [fin.coe_mk, fin.coe_of_nat_eq_mod],
      exact (nat.mod_eq_of_lt hx).symm, },
    rw this at h ⊢,
    norm_cast at h,
    rw zmod.nat_coe_zmod_eq_zero_iff_dvd at h ⊢,
    exact (unique_factorization_monoid.dvd_pow_iff_dvd_of_squarefree
      (fact.out _) (ne_zero.ne _)).mp h, }
end⟩
