/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import algebra.associated

/-- Prime `p` divides the product of a list `L` iff it divides some `a ∈ L` -/
lemma prime.dvd_prod_iff {M : Type*} [comm_monoid_with_zero M] {p : M} {L : list M} (pp : prime p) :
p ∣ L.prod ↔ ∃ a ∈ L, p ∣ a :=
begin
  split,
  { intros h,
    induction L,
    { simp only [list.prod_nil] at h, exact absurd h (prime.not_dvd_one pp) },
    { rw list.prod_cons at h,
      cases (prime.dvd_or_dvd pp) h, { use L_hd, simp [h_1] },
      { rcases L_ih h_1 with ⟨x, hx1, hx2⟩, use x, simp [list.mem_cons_iff, hx1, hx2] } } },
  { exact λ ⟨a, ha1, ha2⟩, dvd_trans ha2 (list.dvd_prod ha1) },
end
