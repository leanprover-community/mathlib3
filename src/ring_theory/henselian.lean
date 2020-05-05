/-
Copyright (c) 2020 Ashwin Iyengar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashwin Iyengar
-/

import ring_theory.ideals
import ring_theory.polynomial

universe u

open polynomial
open local_ring

class henselian (R : Type u) extends local_ring R :=
(is_henselian : ∀ p : polynomial R, monic p → ∀ a₀ : residue_field R, is_root (map (residue R) p) a₀ ∧ eval a₀ (derivative (map (residue R) p)) ≠ 0 → ∃ a : R, eval a p = 0 ∧ residue R a = a₀)
