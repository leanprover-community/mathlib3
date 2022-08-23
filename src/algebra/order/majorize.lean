/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.order
import data.multiset.sort

/-!
# Majorization
-/

open_locale big_operators

variables {ι α : Type*} [fintype ι] [linear_ordered_add_comm_group α] {a b c : ι → α}

-- Why do I need this?
instance linear_ordered_add_comm_group.to_decidable_le : @decidable_rel α (≤) :=
linear_order.decidable_le

def weak_majorize (a b : ι → α) : Prop := ∀ n,
(((finset.univ.1.map a).sort (≤)).inits.inth n).sum ≤
  (((finset.univ.1.map b).sort (≤)).inits.inth n).sum

infix ` ≺ʷ `:50 := weak_majorize

def majorize (a b : ι → α) : Prop := a ≺ʷ b ∧ ∑ i, a i = ∑ i, b i

infix ` ≺ᵐ `:50 := majorize

protected lemma majorize.weak_majorize : a ≺ᵐ b → a ≺ʷ b := and.left

lemma weak_majorize.trans (hab : a ≺ʷ b) (hbc : b ≺ʷ c) : a ≺ʷ c := λ n, (hab _).trans $ hbc _

lemma majorize.trans (hab : a ≺ᵐ b) (hbc : b ≺ᵐ c) : a ≺ᵐ c :=
⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
