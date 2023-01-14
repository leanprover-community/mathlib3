/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import linear_algebra.affine_space.affine_subspace

/-!
# To move
-/

open set

variables (k : Type*) {V P : Type*} [ring k] [add_comm_group V] [module k V] [add_torsor V P]
  {s : set P}
include V

protected lemma set.nonempty.affine_span : s.nonempty → (affine_span k s : set P).nonempty :=
(affine_span_nonempty _ _).2

@[simp] lemma bot_lt_affine_span : ⊥ < affine_span k s ↔ s.nonempty :=
by { rw [bot_lt_iff_ne_bot, nonempty_iff_ne_empty], exact (affine_span_eq_bot _).not }
