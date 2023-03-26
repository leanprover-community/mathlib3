/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.additive.e_transform
import combinatorics.additive.mathlib
import data.nat.lattice

/-!
# Impact function

-/

open function
open_locale pointwise

namespace finset
variables {α β : Type*} [decidable_eq α] [decidable_eq β]

section has_mul
variables [has_mul α] {n : ℕ}

/-- The multiplicative impact function of a finset. -/
@[to_additive]
noncomputable def mul_impact (s : finset α) (n : ℕ) : ℕ :=
⨅ t : {t : finset α // t.card = n}, (s * t).card

@[simp, to_additive] lemma mul_impact_empty (n : ℕ) : (∅ : finset α).mul_impact n = 0 :=
by simp [mul_impact]

end has_mul

section group
variables [group α] {n : ℕ}

@[simp, to_additive] lemma mul_impact_singleton [infinite α] (a : α) (n : ℕ) :
  ({a} : finset α).mul_impact n = n :=
begin
  simp only [mul_impact, singleton_mul', card_smul_finset],
  haveI : nonempty {t : finset α // t.card = n} := nonempty_subtype.2 (exists_card _),
  exact eq.trans (infi_congr subtype.prop) cinfi_const,
end

variables [fintype α]

@[to_additive] lemma exists_mul_impact_add_mul_impact (s : finset α) (hn : 2 ≤ n)
  (hnα : n < fintype.card α) (hnα' : ¬ n ∣ fintype.card α) :
  ∃ k, 0 < k ∧ k < n ∧ s.mul_impact (n - k) + s.mul_impact (n + k) ≤ 2 * s.mul_impact n := sorry

end group

section comm_group
variables [comm_group α] [comm_group β] {n : ℕ}

@[to_additive] lemma mul_impact_map_of_infinite [infinite α] (s : finset α) (f : α →* β)
  (hf : injective f) :
  mul_impact (s.map ⟨f, hf⟩) n = mul_impact s n :=
begin
  haveI : infinite β := sorry,
  haveI : nonempty {t : finset α // t.card = n} := nonempty_subtype.2 (exists_card _),
  haveI : nonempty {t : finset β // t.card = n} := nonempty_subtype.2 (exists_card _),
  refine le_antisymm _ _,
  { refine le_cinfi (λ t, _),
    sorry },
  { refine le_cinfi (λ t, _),
    sorry }
end

@[to_additive] lemma mul_impact_map_of_fintype [fintype α] (s : finset α) (f : α →* β)
  (hf : injective f) :
  mul_impact (s.map ⟨f, hf⟩) n = mul_impact s (fintype.card α * (n / fintype.card α)) :=
sorry

end comm_group
end finset
