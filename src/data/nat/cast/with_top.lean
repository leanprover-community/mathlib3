/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.order.monoid.with_top
import data.nat.basic

/-!
# Lemma about the coercion `ℕ → with_bot ℕ`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An orphaned lemma about casting from `ℕ` to `with_bot ℕ`,
exiled here to minimize imports to `data.rat.order` for porting purposes.
-/

theorem nat.cast_with_top (n : ℕ) :
  @coe ℕ (with_top ℕ) (@coe_to_lift _ _ nat.cast_coe) n = n := rfl

theorem nat.cast_with_bot (n : ℕ) :
  @coe ℕ (with_bot ℕ) (@coe_to_lift _ _ nat.cast_coe) n = n := rfl
