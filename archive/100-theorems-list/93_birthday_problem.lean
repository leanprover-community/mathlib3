/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fintype.card_embedding

/-!
# Birthday Problem

This file proves Theorem 93 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

As of writing, probability is not implemented in Lean, so we instead state the birthday problem
in terms of injective functions. The general result about `fintype.card (α ↪ β)` which this proof
uses is `fintype.card_embedding`.
-/

local notation `‖` x `‖` := fintype.card x

theorem birthday :
  2 * ‖fin 23 ↪ fin 365‖ < ‖fin 23 → fin 365‖ ∧ 2 * ‖fin 22 ↪ fin 365‖ > ‖fin 22 → fin 365‖ :=
by split; norm_num [nat.desc_fac]
