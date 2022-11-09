/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.nat.cast.basic
import algebra.order.monoid.with_top

/-!
# Lemma about the coercion `ℕ → with_bot ℕ`.

An orphaned lemma about casting from `ℕ` to `with_bot ℕ`,
exiled here to minimize imports to `data.rat.order` for porting purposes.
-/

@[simp] theorem nat.cast_with_top (n : ℕ) :
  @coe ℕ (with_top ℕ) (@coe_to_lift _ _ nat.cast_coe) n = n := rfl

@[simp] theorem nat.cast_with_bot (n : ℕ) :
  @coe ℕ (with_bot ℕ) (@coe_to_lift _ _ nat.cast_coe) n = n := rfl
