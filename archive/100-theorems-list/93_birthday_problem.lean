/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fintype.card_inj

/-!
# Birthday Problem

This file proves Theorem 93 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

As of writing, probability is not implemented in Lean, so we instead state the birthday problem
in terms of injective functions. We instead prove a general result about ‖α ↪ β‖.
-/

local notation `‖` x `‖` := fintype.card x

theorem birthday : 2 * ‖fin 23 ↪ fin 365‖ < ‖fin 23 → fin 365‖ := by norm_num [nat.desc_fac]

lemma birthday' : 2 * ‖fin 22 ↪ fin 365‖ > ‖fin 22 → fin 365‖ := by norm_num [nat.desc_fac]
