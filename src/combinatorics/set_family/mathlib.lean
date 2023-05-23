/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.upper_lower.basic
import tactic.by_contra

section linear_order
variables {α : Type*} [linear_order α] {s t : set α}

lemma is_lower_set.total (hs : is_lower_set s) (ht : is_lower_set t) : s ⊆ t ∨ t ⊆ s :=
begin
  by_contra' h,
  simp_rw set.not_subset at h,
  obtain ⟨⟨a, has, hat⟩, b, hbt, hbs⟩ := h,
  obtain hab | hba := le_total a b,
  { exact hat (ht hab hbt) },
  { exact hbs (hs hba has) }
end

lemma is_upper_set.total (hs : is_upper_set s) (ht : is_upper_set t) : s ⊆ t ∨ t ⊆ s :=
begin
  by_contra' h,
  simp_rw set.not_subset at h,
  obtain ⟨⟨a, has, hat⟩, b, hbt, hbs⟩ := h,
  obtain hab | hba := le_total a b,
  { exact hbs (hs hab has) },
  { exact hat (ht hba hbt) }
end

end linear_order

namespace upper_set
variables {α : Type*} [linear_order α]

--TODO: Remove globally
local attribute [-instance] set_like.partial_order

instance is_total_le : is_total (upper_set α) (≤) := ⟨λ s t, t.upper.total s.upper⟩

noncomputable instance : complete_linear_order (upper_set α) :=
{ le_total := is_total.total,
  decidable_le := classical.dec_rel _,
  decidable_eq := classical.dec_rel _,
  decidable_lt := classical.dec_rel _,
  max_def := by classical; exact sup_eq_max_default,
  min_def := by classical; exact inf_eq_min_default,
  ..upper_set.complete_distrib_lattice }

end upper_set

namespace lower_set
variables {α : Type*} [linear_order α]

instance is_total_le : is_total (lower_set α) (≤) := ⟨λ s t, s.lower.total t.lower⟩

noncomputable instance : complete_linear_order (lower_set α) :=
{ le_total := is_total.total,
  decidable_le := classical.dec_rel _,
  decidable_eq := classical.dec_rel _,
  decidable_lt := classical.dec_rel _,
  max_def := by classical; exact sup_eq_max_default,
  min_def := by classical; exact inf_eq_min_default,
  ..lower_set.complete_distrib_lattice }

end lower_set
