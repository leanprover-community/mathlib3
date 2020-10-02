/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import field_theory.subfield
import ring_theory.algebra_tower

/-!
# Intermediate fields

Let `L / K` be a field extension, given as an instance `algebra K L`.
This file defines the type of fields in between `K` and `L`, `intermediate_field K L`.
An `intermediate_field K L` is a subfield of `L` which contains (the image of) `K`,
i.e. it is a `subfield L` and a `subalgebra K L`.

## Main definitions

 * `intermediate_field K L` : the type of intermediate fields between `K` and `L`.

 * `subalgebra.to_intermediate_field`: turns a subalgebra closed under `⁻¹`
   into an intermediate field

 * `subfield.to_intermediate_field`: turns a subfield containing the image of `K`
   into an intermediate field

* `intermediate_field.map`: map an intermediate field along an `alg_hom`

## Implementation notes

Intermediate fields are defined with a structure extending `subfield` and `subalgebra`.
A `subalgebra` is closed under all operations except `⁻¹`,

## TODO

 * `field.adjoin` currently returns a `subalgebra`, this should become an
   `intermediate_field`. The lattice structure on `intermediate_field` will
   follow from the adjunction given by `field.adjoin`.

## Tags
intermediate field, field extension
-/

open_locale big_operators

variables (K L : Type*) [field K] [field L] [algebra K L]

section
set_option old_structure_cmd true

/-- `S : intermediate_field K L` is a subset of `L` such that there is a field
tower `L / S / K`. -/
structure intermediate_field extends subalgebra K L, subfield L

/-- Reinterpret an `intermediate_field` as a `subalgebra`. -/
add_decl_doc intermediate_field.to_subalgebra

/-- Reinterpret an `intermediate_field` as a `subfield`. -/
add_decl_doc intermediate_field.to_subfield

end

variables {K L} (S : intermediate_field K L)

namespace intermediate_field

instance : has_coe (intermediate_field K L) (set L) :=
⟨intermediate_field.carrier⟩

@[simp] lemma coe_to_subalgebra : (S.to_subalgebra : set L) = S := rfl

@[simp] lemma coe_to_subfield : (S.to_subfield : set L) = S := rfl

instance : has_coe_to_sort (intermediate_field K L) := ⟨Type*, λ S, S.carrier⟩

instance : has_mem L (intermediate_field K L) := ⟨λ m S, m ∈ (S : set L)⟩

@[simp] lemma mem_mk (s : set L) (hK : ∀ x, algebra_map K L x ∈ s)
  (ho hm hz ha hn hi) (x : L) :
  x ∈ intermediate_field.mk s ho hm hz ha hK hn hi ↔ x ∈ s := iff.rfl

@[simp] lemma mem_coe (x : L) : x ∈ (S : set L) ↔ x ∈ S := iff.rfl

@[simp] lemma mem_to_subalgebra (s : intermediate_field K L) (x : L) :
  x ∈ s.to_subalgebra ↔ x ∈ s := iff.rfl

@[simp] lemma mem_to_subfield (s : intermediate_field K L) (x : L) :
  x ∈ s.to_subfield ↔ x ∈ s := iff.rfl

/-- Two intermediate fields are equal if the underlying subsets are equal. -/
theorem ext' ⦃s t : intermediate_field K L⦄ (h : (s : set L) = t) : s = t :=
by { cases s, cases t, congr' }

/-- Two intermediate fields are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {s t : intermediate_field K L} : s = t ↔ (s : set L) = t :=
⟨λ h, h ▸ rfl, λ h, ext' h⟩

/-- Two intermediate fields are equal if they have the same elements. -/
@[ext] theorem ext {S T : intermediate_field K L} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
ext' $ set.ext h

/-- An intermediate field contains the image of the smaller field. -/
theorem algebra_map_mem (x : K) : algebra_map K L x ∈ S :=
S.algebra_map_mem' x

/-- An intermediate field contains the ring's 1. -/
theorem one_mem : (1 : L) ∈ S := S.one_mem'

/-- An intermediate field contains the ring's 0. -/
theorem zero_mem : (0 : L) ∈ S := S.zero_mem'

/-- An intermediate field is closed under multiplication. -/
theorem mul_mem : ∀ {x y : L}, x ∈ S → y ∈ S → x * y ∈ S := S.mul_mem'

/-- An intermediate field is closed under scalar multiplication. -/
theorem smul_mem {y : L} : y ∈ S → ∀ {x : K}, x • y ∈ S := S.to_subalgebra.smul_mem

/-- An intermediate field is closed under addition. -/
theorem add_mem : ∀ {x y : L}, x ∈ S → y ∈ S → x + y ∈ S := S.add_mem'

/-- An intermediate field is closed under subtraction -/
theorem sub_mem {x y : L} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
S.to_subfield.sub_mem hx hy

/-- An intermediate field is closed under negation. -/
theorem neg_mem : ∀ {x : L}, x ∈ S → -x ∈ S := S.neg_mem'

/-- An intermediate field is closed under inverses. -/
theorem inv_mem : ∀ {x : L}, x ∈ S → x⁻¹ ∈ S := S.inv_mem'

/-- An intermediate field is closed under division. -/
theorem div_mem {x y : L} (hx : x ∈ S) (hy : y ∈ S) : x / y ∈ S :=
S.to_subfield.div_mem hx hy

/-- Product of a list of elements in an intermediate_field is in the intermediate_field. -/
lemma list_prod_mem {l : list L} : (∀ x ∈ l, x ∈ S) → l.prod ∈ S :=
S.to_subfield.list_prod_mem

/-- Sum of a list of elements in an intermediate field is in the intermediate_field. -/
lemma list_sum_mem {l : list L} : (∀ x ∈ l, x ∈ S) → l.sum ∈ S :=
S.to_subfield.list_sum_mem

/-- Product of a multiset of elements in an intermediate field is in the intermediate_field. -/
lemma multiset_prod_mem (m : multiset L) :
  (∀ a ∈ m, a ∈ S) → m.prod ∈ S :=
S.to_subfield.multiset_prod_mem m

/-- Sum of a multiset of elements in a `intermediate_field` is in the `intermediate_field`. -/
lemma multiset_sum_mem (m : multiset L) :
  (∀ a ∈ m, a ∈ S) → m.sum ∈ S :=
S.to_subfield.multiset_sum_mem m

/-- Product of elements of an intermediate field indexed by a `finset` is in the intermediate_field. -/
lemma prod_mem {ι : Type*} {t : finset ι} {f : ι → L} (h : ∀ c ∈ t, f c ∈ S) :
  ∏ i in t, f i ∈ S :=
S.to_subfield.prod_mem h

/-- Sum of elements in a `intermediate_field` indexed by a `finset` is in the `intermediate_field`. -/
lemma sum_mem {ι : Type*} {t : finset ι} {f : ι → L} (h : ∀ c ∈ t, f c ∈ S) :
  ∑ i in t, f i ∈ S :=
S.to_subfield.sum_mem h

lemma pow_mem {x : L} (hx : x ∈ S) (n : ℕ) : x^n ∈ S := S.to_subfield.pow_mem hx n

lemma gsmul_mem {x : L} (hx : x ∈ S) (n : ℤ) :
  n •ℤ x ∈ S := S.to_subfield.gsmul_mem hx n

lemma coe_int_mem (n : ℤ) : (n : L) ∈ S :=
by simp only [← gsmul_one, gsmul_mem, one_mem]

instance : inhabited (intermediate_field K L) :=
⟨{ neg_mem' := λ x hx, (⊤ : subalgebra K L).neg_mem hx,
   inv_mem' := λ x hx, algebra.mem_top,
   ..(⊤ : subalgebra K L) }⟩

end intermediate_field

/-- Turn a subalgebra closed under inverses into an intermediate field -/
def subalgebra.to_intermediate_field (S : subalgebra K L) (inv_mem : ∀ x ∈ S, x⁻¹ ∈ S) :
  intermediate_field K L :=
{ neg_mem' := λ x, S.neg_mem,
  inv_mem' := inv_mem,
  .. S }

/-- Turn a subfield of `L` containing the image of `K` into an intermediate field -/
def subfield.to_intermediate_field (S : subfield L)
  (algebra_map_mem : ∀ x, algebra_map K L x ∈ S) :
  intermediate_field K L :=
{ algebra_map_mem' := algebra_map_mem,
  .. S }

namespace intermediate_field

/-- An intermediate field inherits a field structure -/
instance to_field : field S :=
S.to_subfield.to_field

@[simp, norm_cast] lemma coe_add (x y : S) : (↑(x + y) : L) = ↑x + ↑y := rfl
@[simp, norm_cast] lemma coe_neg (x : S) : (↑(-x) : L) = -↑x := rfl
@[simp, norm_cast] lemma coe_mul (x y : S) : (↑(x * y) : L) = ↑x * ↑y := rfl
@[simp, norm_cast] lemma coe_inv (x : S) : (↑(x⁻¹) : L) = (↑x)⁻¹ := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : S) : L) = 0 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : S) : L) = 1 := rfl

instance algebra : algebra K S :=
S.to_subalgebra.algebra

instance to_algebra : algebra S L :=
S.to_subalgebra.to_algebra

instance : is_scalar_tower K S L :=
is_scalar_tower.subalgebra' _ _ _ S.to_subalgebra

variables {L' : Type*} [field L'] [algebra K L']

/-- If `f : L →+* L'` fixes `K`, `S.map f` is the intermediate field between `L'` and `K`
such that `x ∈ S ↔ f x ∈ S.map f`. -/
def map (f : L →ₐ[K] L') : intermediate_field K L' :=
{ inv_mem' := by { rintros _ ⟨x, hx, rfl⟩, exact ⟨x⁻¹, S.inv_mem hx, f.map_inv x⟩ },
  neg_mem' := λ x hx, (S.to_subalgebra.map f).neg_mem hx,
  .. S.to_subalgebra.map f}

/-- The embedding from an intermediate field of `L / K` to `L`. -/
def val : S →ₐ[K] L :=
S.to_subalgebra.val

@[simp] theorem coe_val : ⇑S.val = coe := rfl

@[simp] lemma val_mk {x : L} (hx : x ∈ S) : S.val ⟨x, hx⟩ = x := rfl

variables {S}

lemma to_subalgebra_injective {S S' : intermediate_field K L}
  (h : S.to_subalgebra = S'.to_subalgebra) : S = S' :=
by { ext, rw [← mem_to_subalgebra, ← mem_to_subalgebra, h] }

instance : partial_order (intermediate_field K L) :=
{ le := λ S T, (S : set L) ⊆ T,
  le_refl := λ S, set.subset.refl S,
  le_trans := λ _ _ _, set.subset.trans,
  le_antisymm := λ S T hst hts, ext $ λ x, ⟨@hst x, @hts x⟩ }

variables (S)

lemma set_range_subset : set.range (algebra_map K L) ⊆ S :=
S.to_subalgebra.range_subset

lemma field_range_le : (algebra_map K L).field_range ≤ S.to_subfield :=
λ x hx, S.to_subalgebra.range_subset (by rwa [set.mem_range, ← ring_hom.mem_field_range])

variables {S}

end intermediate_field
