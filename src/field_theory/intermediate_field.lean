/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import field_theory.subfield
import field_theory.tower
import ring_theory.algebraic

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

## Tags
intermediate field, field extension
-/

open finite_dimensional
open_locale big_operators

variables (K L : Type*) [field K] [field L] [algebra K L]

/-- `S : intermediate_field K L` is a subset of `L` such that there is a field
tower `L / S / K`. -/
structure intermediate_field extends subalgebra K L :=
(neg_mem' : ∀ x ∈ carrier, -x ∈ carrier)
(inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier)

/-- Reinterpret an `intermediate_field` as a `subalgebra`. -/
add_decl_doc intermediate_field.to_subalgebra

variables {K L} (S : intermediate_field K L)

namespace intermediate_field

/-- Reinterpret an `intermediate_field` as a `subfield`. -/
def to_subfield : subfield L := { ..S.to_subalgebra, ..S }

instance : set_like (intermediate_field K L) L :=
⟨λ S, S.to_subalgebra.carrier, by { rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨h⟩, congr, }⟩

@[simp]
lemma mem_carrier {s : intermediate_field K L} {x : L} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

/-- Two intermediate fields are equal if they have the same elements. -/
@[ext] theorem ext {S T : intermediate_field K L} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
set_like.ext h

@[simp] lemma coe_to_subalgebra : (S.to_subalgebra : set L) = S := rfl

@[simp] lemma coe_to_subfield : (S.to_subfield : set L) = S := rfl

@[simp] lemma mem_mk (s : set L) (hK : ∀ x, algebra_map K L x ∈ s)
  (ho hm hz ha hn hi) (x : L) :
  x ∈ intermediate_field.mk (subalgebra.mk s ho hm hz ha hK) hn hi ↔ x ∈ s := iff.rfl

@[simp] lemma mem_to_subalgebra (s : intermediate_field K L) (x : L) :
  x ∈ s.to_subalgebra ↔ x ∈ s := iff.rfl

@[simp] lemma mem_to_subfield (s : intermediate_field K L) (x : L) :
  x ∈ s.to_subfield ↔ x ∈ s := iff.rfl

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

/-- Product of elements of an intermediate field indexed by a `finset` is in the intermediate_field.
-/
lemma prod_mem {ι : Type*} {t : finset ι} {f : ι → L} (h : ∀ c ∈ t, f c ∈ S) :
  ∏ i in t, f i ∈ S :=
S.to_subfield.prod_mem h

/-- Sum of elements in a `intermediate_field` indexed by a `finset` is in the `intermediate_field`.
-/
lemma sum_mem {ι : Type*} {t : finset ι} {f : ι → L} (h : ∀ c ∈ t, f c ∈ S) :
  ∑ i in t, f i ∈ S :=
S.to_subfield.sum_mem h

lemma pow_mem {x : L} (hx : x ∈ S) : ∀ (n : ℤ), x^n ∈ S
| (n : ℕ) := by { rw zpow_coe_nat, exact S.to_subfield.pow_mem hx _, }
| -[1+ n] := by { rw [zpow_neg_succ_of_nat],
    exact S.to_subfield.inv_mem (S.to_subfield.pow_mem hx _) }

lemma zsmul_mem {x : L} (hx : x ∈ S) (n : ℤ) :
  n • x ∈ S := S.to_subfield.zsmul_mem hx n

lemma coe_int_mem (n : ℤ) : (n : L) ∈ S :=
by simp only [← zsmul_one, zsmul_mem, one_mem]

end intermediate_field

/-- Turn a subalgebra closed under inverses into an intermediate field -/
def subalgebra.to_intermediate_field (S : subalgebra K L) (inv_mem : ∀ x ∈ S, x⁻¹ ∈ S) :
  intermediate_field K L :=
{ neg_mem' := λ x, S.neg_mem,
  inv_mem' := inv_mem,
  .. S }

@[simp] lemma to_subalgebra_to_intermediate_field
  (S : subalgebra K L) (inv_mem : ∀ x ∈ S, x⁻¹ ∈ S) :
  (S.to_intermediate_field inv_mem).to_subalgebra = S :=
by { ext, refl }

@[simp] lemma to_intermediate_field_to_subalgebra
  (S : intermediate_field K L) (inv_mem : ∀ x ∈ S.to_subalgebra, x⁻¹ ∈ S) :
  S.to_subalgebra.to_intermediate_field inv_mem = S :=
by { ext, refl }


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
@[simp, norm_cast] lemma coe_pow (x : S) (n : ℕ) : (↑(x ^ n) : L) = ↑x ^ n :=
begin
  induction n with n ih,
  { simp },
  { simp [pow_succ, ih] }
end

/-! `intermediate_field`s inherit structure from their `subalgebra` coercions. -/

instance module' {R} [semiring R] [has_scalar R K] [module R L] [is_scalar_tower R K L] :
  module R S :=
S.to_subalgebra.module'
instance module : module K S := S.to_subalgebra.module

instance is_scalar_tower {R} [semiring R] [has_scalar R K] [module R L]
  [is_scalar_tower R K L] :
  is_scalar_tower R K S :=
S.to_subalgebra.is_scalar_tower

@[simp] lemma coe_smul {R} [semiring R] [has_scalar R K] [module R L] [is_scalar_tower R K L]
  (r : R) (x : S) :
  ↑(r • x) = (r • x : L) := rfl

instance algebra' {K'} [comm_semiring K'] [has_scalar K' K] [algebra K' L]
  [is_scalar_tower K' K L] :
  algebra K' S :=
S.to_subalgebra.algebra'
instance algebra : algebra K S := S.to_subalgebra.algebra

instance to_algebra {R : Type*} [semiring R] [algebra L R] : algebra S R :=
S.to_subalgebra.to_algebra

instance is_scalar_tower_bot {R : Type*} [semiring R] [algebra L R] :
  is_scalar_tower S L R :=
is_scalar_tower.subalgebra _ _ _ S.to_subalgebra

instance is_scalar_tower_mid {R : Type*} [semiring R] [algebra L R] [algebra K R]
  [is_scalar_tower K L R] : is_scalar_tower K S R :=
is_scalar_tower.subalgebra' _ _ _ S.to_subalgebra

/-- Specialize `is_scalar_tower_mid` to the common case where the top field is `L` -/
instance is_scalar_tower_mid' : is_scalar_tower K S L :=
S.is_scalar_tower_mid

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

variables (S)

lemma set_range_subset : set.range (algebra_map K L) ⊆ S :=
S.to_subalgebra.range_subset

lemma field_range_le : (algebra_map K L).field_range ≤ S.to_subfield :=
λ x hx, S.to_subalgebra.range_subset (by rwa [set.mem_range, ← ring_hom.mem_field_range])

@[simp] lemma to_subalgebra_le_to_subalgebra {S S' : intermediate_field K L} :
  S.to_subalgebra ≤ S'.to_subalgebra ↔ S ≤ S' := iff.rfl

@[simp] lemma to_subalgebra_lt_to_subalgebra {S S' : intermediate_field K L} :
  S.to_subalgebra < S'.to_subalgebra ↔ S < S' := iff.rfl

variables {S}

section tower

/-- Lift an intermediate_field of an intermediate_field -/
def lift1 {F : intermediate_field K L} (E : intermediate_field K F) : intermediate_field K L :=
  map E (val F)

/-- Lift an intermediate_field of an intermediate_field -/
def lift2 {F : intermediate_field K L} (E : intermediate_field F L) : intermediate_field K L :=
{ carrier := E.carrier,
  zero_mem' := zero_mem E,
  add_mem' := λ x y, add_mem E,
  neg_mem' := λ x, neg_mem E,
  one_mem' := one_mem E,
  mul_mem' := λ x y, mul_mem E,
  inv_mem' := λ x, inv_mem E,
  algebra_map_mem' := λ x, algebra_map_mem E (algebra_map K F x) }

instance has_lift1 {F : intermediate_field K L} :
  has_lift_t (intermediate_field K F) (intermediate_field K L) := ⟨lift1⟩

instance has_lift2 {F : intermediate_field K L} :
  has_lift_t (intermediate_field F L) (intermediate_field K L) := ⟨lift2⟩

@[simp] lemma mem_lift2 {F : intermediate_field K L} {E : intermediate_field F L} {x : L} :
  x ∈ (↑E : intermediate_field K L) ↔ x ∈ E := iff.rfl

/-- This was formerly an instance called `lift2_alg`, but an instance above already provides it. -/
example {F : intermediate_field K L} {E : intermediate_field F L} : algebra K E :=
by apply_instance

lemma lift2_algebra_map {F : intermediate_field K L} {E : intermediate_field F L} :
  algebra_map K E = (algebra_map F E).comp (algebra_map K F) := rfl

instance lift2_tower {F : intermediate_field K L} {E : intermediate_field F L} :
  is_scalar_tower K F E :=
E.is_scalar_tower

/-- `lift2` is isomorphic to the original `intermediate_field`. -/
def lift2_alg_equiv {F : intermediate_field K L} (E : intermediate_field F L) :
  (↑E : intermediate_field K L) ≃ₐ[K] E :=
alg_equiv.refl

end tower

section finite_dimensional

variables (F E : intermediate_field K L)

instance finite_dimensional_left [finite_dimensional K L] : finite_dimensional K F :=
finite_dimensional.finite_dimensional_submodule F.to_subalgebra.to_submodule

instance finite_dimensional_right [finite_dimensional K L] : finite_dimensional F L :=
right K F L

@[simp] lemma dim_eq_dim_subalgebra :
  module.rank K F.to_subalgebra = module.rank K F := rfl

@[simp] lemma finrank_eq_finrank_subalgebra :
  finrank K F.to_subalgebra = finrank K F := rfl

variables {F} {E}

@[simp] lemma to_subalgebra_eq_iff : F.to_subalgebra = E.to_subalgebra ↔ F = E :=
by { rw [set_like.ext_iff, set_like.ext'_iff, set.ext_iff], refl }

lemma eq_of_le_of_finrank_le [finite_dimensional K L] (h_le : F ≤ E)
  (h_finrank : finrank K E ≤ finrank K F) : F = E :=
to_subalgebra_injective $ subalgebra.to_submodule_injective $ eq_of_le_of_finrank_le h_le h_finrank

lemma eq_of_le_of_finrank_eq [finite_dimensional K L] (h_le : F ≤ E)
  (h_finrank : finrank K F = finrank K E) : F = E :=
eq_of_le_of_finrank_le h_le h_finrank.ge

lemma eq_of_le_of_finrank_le' [finite_dimensional K L] (h_le : F ≤ E)
  (h_finrank : finrank F L ≤ finrank E L) : F = E :=
begin
  apply eq_of_le_of_finrank_le h_le,
  have h1 := finrank_mul_finrank K F L,
  have h2 := finrank_mul_finrank K E L,
  have h3 : 0 < finrank E L := finrank_pos,
  nlinarith,
end

lemma eq_of_le_of_finrank_eq' [finite_dimensional K L] (h_le : F ≤ E)
  (h_finrank : finrank F L = finrank E L) : F = E :=
eq_of_le_of_finrank_le' h_le h_finrank.le

end finite_dimensional

end intermediate_field

/-- If `L/K` is algebraic, the `K`-subalgebras of `L` are all fields.  -/
def subalgebra_equiv_intermediate_field (alg : algebra.is_algebraic K L) :
  subalgebra K L ≃o intermediate_field K L :=
{ to_fun := λ S, S.to_intermediate_field (λ x hx, S.inv_mem_of_algebraic (alg (⟨x, hx⟩ : S))),
  inv_fun := λ S, S.to_subalgebra,
  left_inv := λ S, to_subalgebra_to_intermediate_field _ _,
  right_inv := λ S, to_intermediate_field_to_subalgebra _ _,
  map_rel_iff' := λ S S', iff.rfl }

@[simp] lemma mem_subalgebra_equiv_intermediate_field (alg : algebra.is_algebraic K L)
  {S : subalgebra K L} {x : L} :
  x ∈ subalgebra_equiv_intermediate_field alg S ↔ x ∈ S :=
iff.rfl

@[simp] lemma mem_subalgebra_equiv_intermediate_field_symm (alg : algebra.is_algebraic K L)
  {S : intermediate_field K L} {x : L} :
  x ∈ (subalgebra_equiv_intermediate_field alg).symm S ↔ x ∈ S :=
iff.rfl
