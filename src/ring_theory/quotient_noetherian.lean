/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import ring_theory.noetherian
import ring_theory.quotient_nilpotent

/-!
# Noetherian quotient rings and quotient modules
-/

instance ideal.quotient.is_noetherian_ring {R : Type*} [comm_ring R] [h : is_noetherian_ring R]
  (I : ideal R) : is_noetherian_ring (R ⧸ I) :=
is_noetherian_ring_iff.mpr $ is_noetherian_of_tower R $ submodule.quotient.is_noetherian _
