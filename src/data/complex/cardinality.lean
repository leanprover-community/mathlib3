/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import data.complex.basic
import data.real.cardinality

/-!
# The cardinality of the complex numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file shows that the complex numbers have cardinality continuum, i.e. `#ℂ = 𝔠`.
-/

open cardinal set

open_locale cardinal

/-- The cardinality of the complex numbers, as a type. -/
@[simp] theorem mk_complex : #ℂ = 𝔠 :=
by rw [mk_congr complex.equiv_real_prod, mk_prod, lift_id, mk_real, continuum_mul_self]

/-- The cardinality of the complex numbers, as a set. -/
@[simp] lemma mk_univ_complex : #(set.univ : set ℂ) = 𝔠 :=
by rw [mk_univ, mk_complex]

/-- The complex numbers are not countable. -/
lemma not_countable_complex : ¬ (set.univ : set ℂ).countable :=
by { rw [← le_aleph_0_iff_set_countable, not_le, mk_univ_complex], apply cantor }
