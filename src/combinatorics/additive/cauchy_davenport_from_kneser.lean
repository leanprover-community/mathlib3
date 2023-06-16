/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.additive.kneser

/-!
# The Cauchy-Davenport theorem as a corollary of Kneser's theorem

This file proves the Cauchy-Davenport theorem as a corollary of Kneser's theorem.

## Main declarations

* `zmod.min_le_card_add`: The Cauchy-Davenport theorem.

## Tags

additive combinatorics, number theory, sumset, cauchy-davenport
-/

open finset
open_locale pointwise

/-- The **Cauchy-Davenport Theorem**. -/
lemma zmod.min_le_card_add {p : ℕ} (hp : p.prime) {s t : finset (zmod p)} (hs : s.nonempty)
  (ht : t.nonempty) : min p (s.card + t.card - 1) ≤ (s + t).card :=
begin
  haveI : fact p.prime := ⟨hp⟩,
  cases eq_bot_or_eq_top (add_action.stabilizer (zmod p) (s + t)),
  { refine min_le_of_right_le _,
    rw [←add_subgroup.coe_eq_zero, ←coe_add_stab (hs.add ht), coe_eq_zero] at h,
    simpa [*] using add_kneser s t },
  { rw [←add_subgroup.coe_eq_univ, ←coe_add_stab (hs.add ht), coe_eq_univ] at h,
    refine card_add_stab_le_card.trans' _,
    simp [*, card_univ] }
end
