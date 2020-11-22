/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import data.finset
import data.fintype.basic
import order.antichain

/-!
# Antichains
Investigating the structure of the lattice of subsets of a finite set
Basic definitions for finite sets which are useful for combinatorics.
We define antichains, and a proposition asserting that a set is a set of r-sets.
## Main definitions
* `all_sized` is a finset of finsets of size r
*
-/

open finset

variable {α : Type*}
variable {r : ℕ}

lemma antichain_of_all_sized {𝒜 : finset (finset α)} {r : ℕ} (a : all_sized 𝒜 r) :
  antichain 𝒜 :=
begin
  intros A h1 B h2 h3,
  have h4 : card A = card B,
  { rw a A h1,
    rw a B h2 },
  convert eq_of_subset_of_card_le h3 _,
  rw h4,
end
