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
  .. conditionally_complete_lattice_of_exists_is_glb
    (λ s h₁ h₂, (exists_least_of_bdd h₂ h₁).imp $ λ a, is_least.is_glb) 0 }

lemma Sup_eq_greatest_of_bdd {s : set ℤ} [decidable_pred (∈ s)]
  (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b) (Hinh : ∃ z : ℤ, z ∈ s) :
  Sup s = greatest_of_bdd b Hb Hinh :=
is_greatest.cSup_eq (greatest_of_bdd b Hb Hinh).2

lemma Inf_eq_least_of_bdd {s : set ℤ} [decidable_pred (∈ s)]
  (b : ℤ) (Hb : ∀ z ∈ s, b ≤ z) (Hinh : ∃ z : ℤ, z ∈ s) :
  Inf s = least_of_bdd b Hb Hinh :=
is_least.cInf_eq (least_of_bdd b Hb Hinh).2

lemma Sup_mem {s : set ℤ} (h1 : s.nonempty) (h2 : bdd_above s) : Sup s ∈ s :=
let ⟨a, ha⟩ := exists_greatest_of_bdd h2 h1 in is_greatest.Sup_mem ha

lemma Inf_mem {s : set ℤ} (h1 : s.nonempty) (h2 : bdd_below s) : Inf s ∈ s :=
let ⟨a, ha⟩ := exists_least_of_bdd h2 h1 in is_least.Inf_mem ha

end int
