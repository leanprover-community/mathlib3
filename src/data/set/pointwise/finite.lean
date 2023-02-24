/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import data.set.finite
import data.set.pointwise.smul

/-! # Finiteness lemmas for pointwise operations on sets 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

open_locale pointwise

variables {F α β γ : Type*}

namespace set

section has_involutive_inv
variables [has_involutive_inv α] {s : set α}

@[to_additive] lemma finite.inv (hs : s.finite) : s⁻¹.finite :=
hs.preimage $ inv_injective.inj_on _

end has_involutive_inv

section has_mul
variables [has_mul α] {s t : set α}

@[to_additive] lemma finite.mul : s.finite → t.finite → (s * t).finite := finite.image2 _

/-- Multiplication preserves finiteness. -/
@[to_additive "Addition preserves finiteness."]
def fintype_mul [decidable_eq α] (s t : set α) [fintype s] [fintype t] : fintype (s * t : set α) :=
set.fintype_image2 _ _ _

end has_mul

section monoid
variables [monoid α] {s t : set α}

@[to_additive]
instance decidable_mem_mul [fintype α] [decidable_eq α] [decidable_pred (∈ s)]
  [decidable_pred (∈ t)] :
  decidable_pred (∈ s * t) :=
λ _, decidable_of_iff _ mem_mul.symm

@[to_additive]
instance decidable_mem_pow [fintype α] [decidable_eq α] [decidable_pred (∈ s)] (n : ℕ) :
  decidable_pred (∈ (s ^ n)) :=
begin
  induction n with n ih,
  { simp_rw [pow_zero, mem_one], apply_instance },
  { letI := ih, rw pow_succ, apply_instance }
end

end monoid

section has_smul
variables [has_smul α β] {s : set α} {t : set β}

@[to_additive] lemma finite.smul : s.finite → t.finite → (s • t).finite := finite.image2 _

end has_smul

section has_smul_set
variables [has_smul α β] {s : set β} {a : α}

@[to_additive] lemma finite.smul_set : s.finite → (a • s).finite := finite.image _

end has_smul_set

section vsub
variables [has_vsub α β] {s t : set β}
include α

lemma finite.vsub (hs : s.finite) (ht : t.finite) : set.finite (s -ᵥ t) := hs.image2 _ ht

end vsub

end set

open set

namespace group

variables {G : Type*} [group G] [fintype G] (S : set G)

@[to_additive]
lemma card_pow_eq_card_pow_card_univ [∀ (k : ℕ), decidable_pred (∈ (S ^ k))] :
  ∀ k, fintype.card G ≤ k → fintype.card ↥(S ^ k) = fintype.card ↥(S ^ (fintype.card G)) :=
begin
  have hG : 0 < fintype.card G := fintype.card_pos_iff.mpr ⟨1⟩,
  by_cases hS : S = ∅,
  { refine λ k hk, fintype.card_congr _,
    rw [hS, empty_pow (ne_of_gt (lt_of_lt_of_le hG hk)), empty_pow (ne_of_gt hG)] },
  obtain ⟨a, ha⟩ := set.nonempty_iff_ne_empty.2 hS,
  classical!,
  have key : ∀ a (s t : set G), (∀ b : G, b ∈ s → a * b ∈ t) → fintype.card s ≤ fintype.card t,
  { refine λ a s t h, fintype.card_le_of_injective (λ ⟨b, hb⟩, ⟨a * b, h b hb⟩) _,
    rintro ⟨b, hb⟩ ⟨c, hc⟩ hbc,
    exact subtype.ext (mul_left_cancel (subtype.ext_iff.mp hbc)) },
  have mono : monotone (λ n, fintype.card ↥(S ^ n) : ℕ → ℕ) :=
  monotone_nat_of_le_succ (λ n, key a _ _ (λ b hb, set.mul_mem_mul ha hb)),
  convert card_pow_eq_card_pow_card_univ_aux mono (λ n, set_fintype_card_le_univ (S ^ n))
    (λ n h, le_antisymm (mono (n + 1).le_succ) (key a⁻¹ _ _ _)),
  { simp only [finset.filter_congr_decidable, fintype.card_of_finset] },
  replace h : {a} * S ^ n = S ^ (n + 1),
  { refine set.eq_of_subset_of_card_le _ (le_trans (ge_of_eq h) _),
    { exact mul_subset_mul (set.singleton_subset_iff.mpr ha) set.subset.rfl },
    { convert key a (S ^ n) ({a} * S ^ n) (λ b hb, set.mul_mem_mul (set.mem_singleton a) hb) } },
  rw [pow_succ', ←h, mul_assoc, ←pow_succ', h],
  rintro _ ⟨b, c, hb, hc, rfl⟩,
  rwa [set.mem_singleton_iff.mp hb, inv_mul_cancel_left],
end

end group
