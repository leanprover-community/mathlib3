/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.set.basic

/-!
# Typeclass for a type `A` with an injective map to `set B`

This is implemented by subobjects.

A typical subobject should be declared as:
```
structure my_subobject (X : Type*) :=
(carrier : set X)
(op_mem : ∀ {x : X}, x ∈ carrier → sorry ∈ carrier)

namespace my_subobject

instance : set_like (my_subobject R) M :=
⟨sub_mul_action.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp] lemma mem_carrier {p : my_subobject R} : x ∈ p.carrier ↔ x ∈ (p : set M) := iff.rfl

@[ext] theorem ext {p q : my_subobject R} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := set_like.ext h

end my_subobject
```

This file will then provide a `coe_sort`, a `coe` to set, a `partial_order`, and various
extensionality and simp lemmas.

-/
set_option old_structure_cmd true

@[protect_proj]
class set_like (A : Type*) (B : out_param $ Type*) :=
(coe : A → set B)
(coe_injective' : function.injective coe)

namespace set_like

variables {A : Type*} {B : Type*} [i : set_like A B]

include i

instance : has_coe_t A (set B) := ⟨set_like.coe⟩
instance : has_mem B A := ⟨λ x p, x ∈ (p : set B)⟩
instance : has_coe_to_sort A := ⟨_, λ p, {x : B // x ∈ p}⟩

variables (p q : A)

@[simp, norm_cast] theorem coe_sort_coe : ↥(p : set B) = p := rfl

variables {p q}

protected theorem «exists» {q : p → Prop} :
  (∃ x, q x) ↔ (∃ x ∈ p, q ⟨x, ‹_›⟩) := set_coe.exists

protected theorem «forall» {q : p → Prop} :
  (∀ x, q x) ↔ (∀ x ∈ p, q ⟨x, ‹_›⟩) := set_coe.forall

theorem coe_injective : function.injective (coe : A → set B) :=
λ x y h, set_like.coe_injective' h

@[simp, norm_cast] theorem coe_set_eq : (p : set B) = q ↔ p = q := coe_injective.eq_iff

theorem ext'_iff : p = q ↔ (p : set B) = q := coe_set_eq.symm

/-- Note: implementers of `set_like` must copy this lemma. -/
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := coe_injective $ set.ext h

@[simp] theorem mem_coe {x : B} : x ∈ (p : set B) ↔ x ∈ p := iff.rfl

@[simp, norm_cast] lemma coe_eq_coe {x y : p} : (x : B) = y ↔ x = y := subtype.ext_iff_val.symm

@[simp, norm_cast] lemma coe_mk (x : B) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : B) = x := rfl
@[simp] lemma coe_mem (x : p) : (x : B) ∈ p := x.2

@[simp] protected lemma eta (x : p) (hx : (x : B) ∈ p) : (⟨x, hx⟩ : p) = x := subtype.eta x hx

instance : partial_order A :=
{ le := λ H K, ∀ ⦃x⦄, x ∈ H → x ∈ K,
  .. partial_order.lift (coe : A → set B) coe_injective }

lemma le_def {S T : A} : S ≤ T ↔ ∀ ⦃x : B⦄, x ∈ S → x ∈ T := iff.rfl

@[simp, norm_cast]
lemma coe_subset_coe {S T : A} : (S : set B) ⊆ T ↔ S ≤ T := iff.rfl

@[simp, norm_cast]
lemma coe_ssubset_coe {S T : A} : (S : set B) ⊂ T ↔ S < T := iff.rfl

end set_like
