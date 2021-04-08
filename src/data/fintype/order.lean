/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/

import order.lattice
import data.fintype.basic

/-!
# Order structures on finite sets

This file provides instances showing that a `semilattice_sup_bot` on a `fintype` gives a
`complete_lattice`, and that a `linear_order` on a nonempty `fintype` gives a
`complete_linear_order`. The latter applies in particular to `fin (n+1)`. The instances are
noncomputable because the definitions of `Sup` and `Inf` require passing from `set` to `finset`.
-/

open_locale classical

variables {α : Type*}

@[priority 100] noncomputable instance fintype.has_Sup [fintype α] [semilattice_sup_bot α] :
  complete_semilattice_Sup α :=
{ Sup := λ s, s.to_finset.sup id,
  le_Sup := λ _ _ ha, finset.le_sup (set.mem_to_finset.mpr ha),
  Sup_le := λ _ _ ha, finset.sup_le (λ b hb, ha _ (by rwa set.mem_to_finset at hb)),
  ..(infer_instance : semilattice_sup_bot α) }

@[priority 100] noncomputable instance fintype.complete_lattice_of_semilattice_sup_bot
[fintype α] [semilattice_sup_bot α]:
  complete_lattice α :=
complete_lattice_of_complete_semilattice_Sup _

@[priority 100] noncomputable instance fintype.semilattice_sup_bot_of_linear_order
[fintype α] [nonempty α] [linear_order α] :
  semilattice_sup_bot α :=
{ bot := classical.some (fintype.exists_min id),
  bot_le := classical.some_spec (fintype.exists_min id),
  sup := max,
  le_sup_left := le_max_left,
  le_sup_right := le_max_right,
  sup_le := λ _ _ _ h h', max_le h h',
  ..(infer_instance : linear_order α) }

@[priority 100] noncomputable instance fintype.complete_linear_order_of_linear_order
[fintype α] [nonempty α] [linear_order α] :
  complete_linear_order α :=
{ ..fintype.complete_lattice_of_semilattice_sup_bot,
  ..(infer_instance : linear_order α) }
