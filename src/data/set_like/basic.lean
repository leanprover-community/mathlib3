/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.set.basic
import tactic.monotonicity.basic

/-!
# Typeclass for types with a set-like extensionality property

The `has_mem` typeclass is used to let terms of a type have elements.
Many instances of `has_mem` have a set-like extensionality property:
things are equal iff they have the same elements.  The `set_like`
typeclass provides a unified interface to define a `has_mem` that is
extensional in this way.

The main use of `set_like` is for algebraic subobjects (such as
`submonoid` and `submodule`), whose non-proof data consists only of a
carrier set.  In such a situation, the projection to the carrier set
is injective.

In general, a type `A` is `set_like` with elements of type `B` if it
has an injective map to `set B`.  This module provides standard
boilerplate for every `set_like`: a `coe_sort`, a `coe` to set, a
`partial_order`, and various extensionality and simp lemmas.

A typical subobject should be declared as:
```
structure my_subobject (X : Type*) :=
(carrier : set X)
(op_mem : ∀ {x : X}, x ∈ carrier → sorry ∈ carrier)

namespace my_subobject

variables (X : Type*)

instance : set_like (my_subobject X) X :=
⟨sub_mul_action.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp] lemma mem_carrier {p : my_subobject X} : x ∈ p.carrier ↔ x ∈ (p : set X) := iff.rfl

@[ext] theorem ext {p q : my_subobject X} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := set_like.ext h

/-- Copy of a `my_subobject` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. See Note [range copy pattern]. -/
protected def copy (p : my_subobject X) (s : set X) (hs : s = ↑p) : my_subobject X :=
{ carrier := s,
  op_mem' := hs.symm ▸ p.op_mem' }

@[simp] lemma coe_copy (p : my_subobject X) (s : set X) (hs : s = ↑p) :
  (p.copy s hs : set X) = s := rfl

lemma copy_eq (p : my_subobject X) (s : set X) (hs : s = ↑p) : p.copy s hs = p :=
set_like.coe_injective hs

end my_subobject
```

An alternative to `set_like` could have been an extensional `has_mem` typeclass:
```
class has_ext_mem (α : out_param $ Type u) (β : Type v) extends has_mem α β :=
(ext_iff : ∀ {s t : β}, s = t ↔ ∀ (x : α), x ∈ s ↔ x ∈ t)
```
While this is equivalent, `set_like` conveniently uses a carrier set projection directly.

## Tags

subobjects
-/

/-- A class to indicate that there is a canonical injection between `A` and `set B`.

This has the effect of giving terms of `A` elements of type `B` (through a `has_mem`
instance) and a compatible coercion to `Type*` as a subtype.

Note: if `set_like.coe` is a projection, implementers should create a simp lemma such as
```
@[simp] lemma mem_carrier {p : my_subobject X} : x ∈ p.carrier ↔ x ∈ (p : set X) := iff.rfl
```
to normalize terms.
-/
@[protect_proj]
class set_like (A : Type*) (B : out_param $ Type*) :=
(coe : A → set B)
(coe_injective' : function.injective coe)

namespace set_like

variables {A : Type*} {B : Type*} [i : set_like A B]

include i

instance : has_coe_t A (set B) := ⟨set_like.coe⟩

@[priority 100]
instance : has_mem B A := ⟨λ x p, x ∈ (p : set B)⟩

-- `dangerous_instance` does not know that `B` is used only as an `out_param`
@[nolint dangerous_instance, priority 100]
instance : has_coe_to_sort A Type* := ⟨λ p, {x : B // x ∈ p}⟩

variables (p q : A)

@[simp, norm_cast] theorem coe_sort_coe : ((p : set B) : Type*) = p := rfl

variables {p q}

protected theorem «exists» {q : p → Prop} :
  (∃ x, q x) ↔ (∃ x ∈ p, q ⟨x, ‹_›⟩) := set_coe.exists

protected theorem «forall» {q : p → Prop} :
  (∀ x, q x) ↔ (∀ x ∈ p, q ⟨x, ‹_›⟩) := set_coe.forall

theorem coe_injective : function.injective (coe : A → set B) :=
λ x y h, set_like.coe_injective' h

@[simp, norm_cast] theorem coe_set_eq : (p : set B) = q ↔ p = q := coe_injective.eq_iff

theorem ext' (h : (p : set B) = q) : p = q := coe_injective h

theorem ext'_iff : p = q ↔ (p : set B) = q := coe_set_eq.symm

/-- Note: implementers of `set_like` must copy this lemma in order to tag it with `@[ext]`. -/
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := coe_injective $ set.ext h

theorem ext_iff : p = q ↔ (∀ x, x ∈ p ↔ x ∈ q) := coe_injective.eq_iff.symm.trans set.ext_iff

@[simp] theorem mem_coe {x : B} : x ∈ (p : set B) ↔ x ∈ p := iff.rfl

@[simp, norm_cast] lemma coe_eq_coe {x y : p} : (x : B) = y ↔ x = y := subtype.ext_iff_val.symm

@[simp, norm_cast] lemma coe_mk (x : B) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : B) = x := rfl
@[simp] lemma coe_mem (x : p) : (x : B) ∈ p := x.2

@[simp] protected lemma eta (x : p) (hx : (x : B) ∈ p) : (⟨x, hx⟩ : p) = x := subtype.eta x hx

-- `dangerous_instance` does not know that `B` is used only as an `out_param`
@[nolint dangerous_instance, priority 100]
instance : partial_order A :=
{ le := λ H K, ∀ ⦃x⦄, x ∈ H → x ∈ K,
  .. partial_order.lift (coe : A → set B) coe_injective }

lemma le_def {S T : A} : S ≤ T ↔ ∀ ⦃x : B⦄, x ∈ S → x ∈ T := iff.rfl

@[simp, norm_cast]
lemma coe_subset_coe {S T : A} : (S : set B) ⊆ T ↔ S ≤ T := iff.rfl

@[mono] lemma coe_mono : monotone (coe : A → set B) := λ a b, coe_subset_coe.mpr

@[simp, norm_cast]
lemma coe_ssubset_coe {S T : A} : (S : set B) ⊂ T ↔ S < T := iff.rfl

@[mono] lemma coe_strict_mono : strict_mono (coe : A → set B) := λ a b, coe_ssubset_coe.mpr

lemma not_le_iff_exists : ¬(p ≤ q) ↔ ∃ x ∈ p, x ∉ q := set.not_subset

lemma exists_of_lt : p < q → ∃ x ∈ q, x ∉ p := set.exists_of_ssubset

lemma lt_iff_le_and_exists : p < q ↔ p ≤ q ∧ ∃ x ∈ q, x ∉ p :=
by rw [lt_iff_le_not_le, not_le_iff_exists]

end set_like
