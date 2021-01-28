/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import tactic.norm_cast
import data.set.basic

set_option old_structure_cmd true

/-- Base type for bundled sets -/
class {u v} is_bundled_set (S : Type u) :=
(mem_type : Type v)
(set_coe' : S → set mem_type)
(set_coe_inj' : function.injective set_coe')

attribute [reducible] is_bundled_set.mem_type

namespace is_bundled_set

variables {S : Type*} [is_bundled_set S]

local notation `α` := mem_type S

instance : has_coe S (set α) := ⟨set_coe'⟩

instance : has_mem α S := ⟨λ m s, m ∈ (s : set α)⟩

instance : has_coe_to_sort S := ⟨Type*, λ S, {x : α // x ∈ S}⟩

@[simp, norm_cast]
lemma mem_coe {s : S} {m : α} : m ∈ (s : set α) ↔ m ∈ s := iff.rfl

@[simp, norm_cast]
lemma coe_coe (s : S) : ↥(s : set α) = s := rfl

protected lemma «exists» {s : S} {p : s → Prop} :
  (∃ x : s, p x) ↔ ∃ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.exists

protected lemma «forall» {s : S} {p : s → Prop} :
  (∀ x : s, p x) ↔ ∀ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.forall

/-- Two bundled_sets are equal if the underlying subsets are equal. -/
theorem ext' ⦃a b : S⦄ (h : (a : set α) = b) : a = b :=
set_coe_inj' h

/-- Two bundled_sets are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {a b : S} : a = b ↔ (a : set α) = b :=
⟨λ h, h ▸ rfl, λ h, ext' h⟩

/-- Two bundled_sets are equal if they have the same elements. -/
theorem ext {a b : S}
  (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := ext' $ set.ext h

variable {s : S}

lemma coe_injective : function.injective (coe : s → α) := subtype.val_injective

@[norm_cast, simp] lemma coe_eq_coe (x y : s) : (x : α) = y ↔ x = y := set_coe.ext_iff

instance : has_le S := ⟨λ a b, ∀ ⦃x⦄, x ∈ a → x ∈ b⟩

lemma le_def {a b : S} : a ≤ b ↔ ∀ ⦃x : α⦄, x ∈ a → x ∈ b := iff.rfl

@[simp, norm_cast]
lemma coe_subset_coe {a b : S} : (a : set α) ⊆ b ↔ a ≤ b := iff.rfl

instance : partial_order S :=
{ le := λ a b, ∀ ⦃x⦄, x ∈ a → x ∈ b,
  .. partial_order.lift (coe : S → set α) ext' }

@[simp, norm_cast]
lemma coe_ssubset_coe {a b : S} : (a : set α) ⊂ b ↔ a < b := iff.rfl

end is_bundled_set
