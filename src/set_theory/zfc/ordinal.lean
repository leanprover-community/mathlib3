/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal.basic
import set_theory.zfc.basic

/-!
### Von Neumann ordinals


-/

namespace pSet

/-- The set of von Neumann ordinals is defined as the set of pre-sets such that all their elements
are subsets. -/
def is_ordinal : set pSet := λ p, ∀ x ∈ p, x ⊆ p

theorem is_ordinal.subset_of_mem {p q : pSet} (hp : p.is_ordinal) : q ∈ p → q ⊆ p := hp q

theorem empty_is_ordinal : is_ordinal ∅ := λ x hx, (mem_empty x hx).elim

theorem is_ordinal_of_mem {p q : pSet} (hp : p.is_ordinal) (hq : q ∈ p) : q.is_ordinal :=
begin
  intros r hr s,
  have := hp.subset_of_mem hq,
end

end pSet

namespace ordinal

/-- The von Neumann construction for ordinals, where every ordinal -/
noncomputable! def to_pSet : ordinal → pSet
| o := ⟨o.out.α, λ i, let wf := typein_lt_self i in (typein (<) i).to_pSet⟩
using_well_founded { dec_tac := `[assumption] }

end ordinal
