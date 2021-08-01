/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import order.conditionally_complete_lattice
import data.int.least_greatest

/-!
## `ℤ` forms a conditionally complete linear order

The integers form a conditionally complete linear order.
-/

open int
open_locale classical
noncomputable theory

namespace int

instance : conditionally_complete_linear_order ℤ :=
{ .. int.linear_order,
  .. conditionally_complete_lattice_of_is_lub_of_rel_iso
    (λ s h₁ h₂, (exists_greatest_of_bdd h₂ h₁).imp $ λ a, is_greatest.is_lub) 0 order_iso.neg }

lemma cSup_eq_greatest_of_bdd {s : set ℤ} [decidable_pred (∈ s)]
  (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b) (Hinh : ∃ z : ℤ, z ∈ s) :
  Sup s = greatest_of_bdd b Hb Hinh :=
is_greatest.cSup_eq (greatest_of_bdd b Hb Hinh).2

@[simp] lemma cSup_empty : Sup (∅ : set ℤ) = 0 := dif_neg (by simp)

lemma cSup_of_not_bdd_above {s : set ℤ} (h : ¬ bdd_above s) : Sup s = 0 := dif_neg (by simp [h])

lemma cInf_eq_least_of_bdd {s : set ℤ} [decidable_pred (∈ s)]
  (b : ℤ) (Hb : ∀ z ∈ s, b ≤ z) (Hinh : ∃ z : ℤ, z ∈ s) :
  Inf s = least_of_bdd b Hb Hinh :=
is_least.cInf_eq (least_of_bdd b Hb Hinh).2

lemma Inf_def (s : set ℤ) : Inf s = -Sup (-s) := rfl

@[simp] lemma cInf_empty : Inf (∅ : set ℤ) = 0 := by simp [Inf_def]

lemma cInf_of_not_bdd_below {s : set ℤ} (h : ¬ bdd_below s) : Inf s = 0 :=
have ¬ bdd_above (-s), from mt (order_iso.neg : ℤ ≃o _).bdd_above_preimage.1 h,
by simp [Inf_def, cSup_of_not_bdd_above this]

lemma Sup_mem {s : set ℤ} (h1 : s.nonempty) (h2 : bdd_above s) : Sup s ∈ s :=
let ⟨a, ha⟩ := exists_greatest_of_bdd h2 h1 in is_greatest.Sup_mem ha

lemma cInf_mem {s : set ℤ} (h1 : s.nonempty) (h2 : bdd_below s) : Inf s ∈ s :=
let ⟨a, ha⟩ := exists_least_of_bdd h2 h1 in is_least.Inf_mem ha

end int
