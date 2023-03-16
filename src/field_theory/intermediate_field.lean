/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import field_theory.minpoly.field
import field_theory.subfield
import field_theory.tower

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
* `intermediate_field.restrict_scalars`: restrict the scalars of an intermediate field to a smaller
  field in a tower of fields.

## Implementation notes

Intermediate fields are defined with a structure extending `subfield` and `subalgebra`.
A `subalgebra` is closed under all operations except `⁻¹`,

## Tags
intermediate field, field extension
-/

open finite_dimensional polynomial
open_locale big_operators polynomial

variables (K L L' : Type*) [field K] [field L] [field L'] [algebra K L] [algebra K L']

/-- `S : intermediate_field K L` is a subset of `L` such that there is a field
tower `L / S / K`. -/
structure intermediate_field extends subalgebra K L :=
(neg_mem' : ∀ x ∈ carrier, -x ∈ carrier)
(inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier)

/-- Reinterpret an `intermediate_field` as a `subalgebra`. -/
add_decl_doc intermediate_field.to_subalgebra

variables {K L L'} (S : intermediate_field K L)

namespace intermediate_field

/-- Reinterpret an `intermediate_field` as a `subfield`. -/
def to_subfield : subfield L := { ..S.to_subalgebra, ..S }

instance : set_like (intermediate_field K L) L :=
⟨λ S, S.to_subalgebra.carrier, by { rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨h⟩, congr, }⟩

instance : subfield_class (intermediate_field K L) L :=
{ add_mem := λ s _ _, s.add_mem',
  zero_mem := λ s, s.zero_mem',
  neg_mem := neg_mem',
  mul_mem := λ s _ _, s.mul_mem',
  one_mem := λ s, s.one_mem',
  inv_mem := inv_mem' }

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

/-- Copy of an intermediate field with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (S : intermediate_field K L) (s : set L) (hs : s = ↑S) :
  intermediate_field K L :=
{ to_subalgebra := S.to_subalgebra.copy s (hs : s = (S.to_subalgebra).carrier),
  neg_mem' :=
    have hs' : (S.to_subalgebra.copy s hs).carrier = (S.to_subalgebra).carrier := hs,
    hs'.symm ▸ S.neg_mem',
  inv_mem' :=
    have hs' : (S.to_subalgebra.copy s hs).carrier = (S.to_subalgebra).carrier := hs,
    hs'.symm ▸ S.inv_mem' }

@[simp] lemma coe_copy (S : intermediate_field K L) (s : set L) (hs : s = ↑S) :
  (S.copy s hs : set L) = s := rfl

lemma copy_eq (S : intermediate_field K L) (s : set L) (hs : s = ↑S) : S.copy s hs = S :=
set_like.coe_injective hs

section inherited_lemmas

/-! ### Lemmas inherited from more general structures

The declarations in this section derive from the fact that an `intermediate_field` is also a
subalgebra or subfield. Their use should be replaceable with the corresponding lemma from a
subobject class.
-/

/-- An intermediate field contains the image of the smaller field. -/
theorem algebra_map_mem (x : K) : algebra_map K L x ∈ S :=
S.algebra_map_mem' x

/-- An intermediate field is closed under scalar multiplication. -/
theorem smul_mem {y : L} : y ∈ S → ∀ {x : K}, x • y ∈ S := S.to_subalgebra.smul_mem

/-- An intermediate field contains the ring's 1. -/
protected theorem one_mem : (1 : L) ∈ S := one_mem S
/-- An intermediate field contains the ring's 0. -/
protected theorem zero_mem : (0 : L) ∈ S := zero_mem S
/-- An intermediate field is closed under multiplication. -/
protected theorem mul_mem {x y : L} : x ∈ S → y ∈ S → x * y ∈ S := mul_mem
/-- An intermediate field is closed under addition. -/
protected theorem add_mem {x y : L} : x ∈ S → y ∈ S → x + y ∈ S := add_mem
/-- An intermediate field is closed under subtraction -/
protected theorem sub_mem {x y : L} : x ∈ S → y ∈ S → x - y ∈ S := sub_mem
/-- An intermediate field is closed under negation. -/
protected theorem neg_mem {x : L} : x ∈ S → -x ∈ S := neg_mem
/-- An intermediate field is closed under inverses. -/
protected theorem inv_mem {x : L} : x ∈ S → x⁻¹ ∈ S := inv_mem
/-- An intermediate field is closed under division. -/
protected theorem div_mem {x y : L} : x ∈ S → y ∈ S → x / y ∈ S := div_mem

/-- Product of a list of elements in an intermediate_field is in the intermediate_field. -/
protected lemma list_prod_mem {l : list L} : (∀ x ∈ l, x ∈ S) → l.prod ∈ S := list_prod_mem
/-- Sum of a list of elements in an intermediate field is in the intermediate_field. -/
protected lemma list_sum_mem {l : list L} : (∀ x ∈ l, x ∈ S) → l.sum ∈ S := list_sum_mem
/-- Product of a multiset of elements in an intermediate field is in the intermediate_field. -/
protected lemma multiset_prod_mem (m : multiset L) : (∀ a ∈ m, a ∈ S) → m.prod ∈ S :=
multiset_prod_mem m
/-- Sum of a multiset of elements in a `intermediate_field` is in the `intermediate_field`. -/
protected lemma multiset_sum_mem (m : multiset L) : (∀ a ∈ m, a ∈ S) → m.sum ∈ S :=
multiset_sum_mem m

/-- Product of elements of an intermediate field indexed by a `finset` is in the intermediate_field.
-/
protected lemma prod_mem {ι : Type*} {t : finset ι} {f : ι → L} (h : ∀ c ∈ t, f c ∈ S) :
  ∏ i in t, f i ∈ S := prod_mem h
/-- Sum of elements in a `intermediate_field` indexed by a `finset` is in the `intermediate_field`.
-/
protected lemma sum_mem {ι : Type*} {t : finset ι} {f : ι → L} (h : ∀ c ∈ t, f c ∈ S) :
  ∑ i in t, f i ∈ S := sum_mem h
protected lemma pow_mem {x : L} (hx : x ∈ S) (n : ℤ) : x^n ∈ S := zpow_mem hx n
protected lemma zsmul_mem {x : L} (hx : x ∈ S) (n : ℤ) : n • x ∈ S := zsmul_mem hx n
protected lemma coe_int_mem (n : ℤ) : (n : L) ∈ S := coe_int_mem S n

protected lemma coe_add (x y : S) : (↑(x + y) : L) = ↑x + ↑y := rfl
protected lemma coe_neg (x : S) : (↑(-x) : L) = -↑x := rfl
protected lemma coe_mul (x y : S) : (↑(x * y) : L) = ↑x * ↑y := rfl
protected lemma coe_inv (x : S) : (↑(x⁻¹) : L) = (↑x)⁻¹ := rfl
protected lemma coe_zero : ((0 : S) : L) = 0 := rfl
protected lemma coe_one : ((1 : S) : L) = 1 := rfl
protected lemma coe_pow (x : S) (n : ℕ) : (↑(x ^ n) : L) = ↑x ^ n := submonoid_class.coe_pow x n

end inherited_lemmas

lemma coe_nat_mem (n : ℕ) : (n : L) ∈ S :=
by simpa using coe_int_mem S n

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

@[simp] lemma to_intermediate_field_to_subalgebra (S : intermediate_field K L) :
  S.to_subalgebra.to_intermediate_field (λ x, S.inv_mem) = S :=
by { ext, refl }

/-- Turn a subalgebra satisfying `is_field` into an intermediate_field -/
def subalgebra.to_intermediate_field' (S : subalgebra K L) (hS : is_field S) :
  intermediate_field K L :=
S.to_intermediate_field $ λ x hx, begin
  by_cases hx0 : x = 0,
  { rw [hx0, inv_zero],
    exact S.zero_mem },
  letI hS' := hS.to_field,
  obtain ⟨y, hy⟩ := hS.mul_inv_cancel (show (⟨x, hx⟩ : S) ≠ 0, from subtype.ne_of_val_ne hx0),
  rw [subtype.ext_iff, S.coe_mul, S.coe_one, subtype.coe_mk, mul_eq_one_iff_inv_eq₀ hx0] at hy,
  exact hy.symm ▸ y.2,
end

@[simp] lemma to_subalgebra_to_intermediate_field' (S : subalgebra K L) (hS : is_field S) :
  (S.to_intermediate_field' hS).to_subalgebra = S :=
by { ext, refl }

@[simp] lemma to_intermediate_field'_to_subalgebra (S : intermediate_field K L) :
  S.to_subalgebra.to_intermediate_field' (field.to_is_field S) = S :=
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

@[simp, norm_cast]
lemma coe_sum {ι : Type*} [fintype ι] (f : ι → S) : (↑∑ i, f i : L) = ∑ i, (f i : L) :=
begin
  classical,
  induction finset.univ using finset.induction_on with i s hi H,
  { simp },
  { rw [finset.sum_insert hi, add_mem_class.coe_add, H, finset.sum_insert hi] }
end

@[simp, norm_cast]
lemma coe_prod {ι : Type*} [fintype ι] (f : ι → S) : (↑∏ i, f i : L) = ∏ i, (f i : L) :=
begin
  classical,
  induction finset.univ using finset.induction_on with i s hi H,
  { simp },
  { rw [finset.prod_insert hi, mul_mem_class.coe_mul, H, finset.prod_insert hi] }
end

/-! `intermediate_field`s inherit structure from their `subalgebra` coercions. -/

instance module' {R} [semiring R] [has_smul R K] [module R L] [is_scalar_tower R K L] :
  module R S :=
S.to_subalgebra.module'
instance module : module K S := S.to_subalgebra.module

instance is_scalar_tower {R} [semiring R] [has_smul R K] [module R L]
  [is_scalar_tower R K L] :
  is_scalar_tower R K S :=
S.to_subalgebra.is_scalar_tower

@[simp] lemma coe_smul {R} [semiring R] [has_smul R K] [module R L] [is_scalar_tower R K L]
  (r : R) (x : S) :
  ↑(r • x) = (r • x : L) := rfl

instance algebra' {K'} [comm_semiring K'] [has_smul K' K] [algebra K' L]
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

/-- If `f : L →+* L'` fixes `K`, `S.map f` is the intermediate field between `L'` and `K`
such that `x ∈ S ↔ f x ∈ S.map f`. -/
def map (f : L →ₐ[K] L') (S : intermediate_field K L) : intermediate_field K L' :=
{ inv_mem' := by { rintros _ ⟨x, hx, rfl⟩, exact ⟨x⁻¹, S.inv_mem hx, map_inv₀ f x⟩ },
  neg_mem' := λ x hx, (S.to_subalgebra.map f).neg_mem hx,
  .. S.to_subalgebra.map f}

@[simp] lemma coe_map (f : L →ₐ[K] L') : (S.map f : set L') = f '' S := rfl

lemma map_map {K L₁ L₂ L₃ : Type*} [field K] [field L₁] [algebra K L₁]
  [field L₂] [algebra K L₂] [field L₃] [algebra K L₃]
  (E : intermediate_field K L₁) (f : L₁ →ₐ[K] L₂) (g : L₂ →ₐ[K] L₃) :
  (E.map f).map g = E.map (g.comp f) :=
set_like.coe_injective $ set.image_image _ _ _

/-- Given an equivalence `e : L ≃ₐ[K] L'` of `K`-field extensions and an intermediate
field `E` of `L/K`, `intermediate_field_equiv_map e E` is the induced equivalence
between `E` and `E.map e` -/
def intermediate_field_map (e : L ≃ₐ[K] L') (E : intermediate_field K L) :
  E ≃ₐ[K] (E.map e.to_alg_hom) :=
e.subalgebra_map E.to_subalgebra

/- We manually add these two simp lemmas because `@[simps]` before `intermediate_field_map`
  led to a timeout. -/
@[simp] lemma intermediate_field_map_apply_coe (e : L ≃ₐ[K] L') (E : intermediate_field K L)
  (a : E) : ↑(intermediate_field_map e E a) = e a := rfl

@[simp] lemma intermediate_field_map_symm_apply_coe (e : L ≃ₐ[K] L') (E : intermediate_field K L)
  (a : E.map e.to_alg_hom) : ↑((intermediate_field_map e E).symm a) = e.symm a := rfl

end intermediate_field

namespace alg_hom

variables (f : L →ₐ[K] L')

/-- The range of an algebra homomorphism, as an intermediate field. -/
@[simps to_subalgebra]
def field_range : intermediate_field K L' :=
{ .. f.range,
  .. (f : L →+* L').field_range }

@[simp] lemma coe_field_range : ↑f.field_range = set.range f := rfl

@[simp] lemma field_range_to_subfield :
  f.field_range.to_subfield = (f : L →+* L').field_range := rfl

variables {f}

@[simp] lemma mem_field_range {y : L'} : y ∈ f.field_range ↔ ∃ x, f x = y := iff.rfl

end alg_hom

namespace intermediate_field

/-- The embedding from an intermediate field of `L / K` to `L`. -/
def val : S →ₐ[K] L :=
S.to_subalgebra.val

@[simp] theorem coe_val : ⇑S.val = coe := rfl

@[simp] lemma val_mk {x : L} (hx : x ∈ S) : S.val ⟨x, hx⟩ = x := rfl

lemma range_val : S.val.range = S.to_subalgebra :=
S.to_subalgebra.range_val

lemma aeval_coe {R : Type*} [comm_ring R] [algebra R K] [algebra R L]
  [is_scalar_tower R K L] (x : S) (P : R[X]) : aeval (x : L) P = aeval x P :=
begin
  refine polynomial.induction_on' P (λ f g hf hg, _) (λ n r, _),
  { rw [aeval_add, aeval_add, add_mem_class.coe_add, hf, hg] },
  { simp only [mul_mem_class.coe_mul, aeval_monomial, submonoid_class.coe_pow,
               mul_eq_mul_right_iff],
    left, refl }
end

lemma coe_is_integral_iff {R : Type*} [comm_ring R] [algebra R K] [algebra R L]
  [is_scalar_tower R K L] {x : S} : is_integral R (x : L) ↔ is_integral R x :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨P, hPmo, hProot⟩ := h,
    refine ⟨P, hPmo, (injective_iff_map_eq_zero _).1 (algebra_map ↥S L).injective _ _⟩,
    letI : is_scalar_tower R S L := is_scalar_tower.of_algebra_map_eq (congr_fun rfl),
    rwa [eval₂_eq_eval_map, ← eval₂_at_apply, eval₂_eq_eval_map, polynomial.map_map,
      ← is_scalar_tower.algebra_map_eq, ← eval₂_eq_eval_map] },
  { obtain ⟨P, hPmo, hProot⟩ := h,
    refine ⟨P, hPmo, _⟩,
    rw [← aeval_def, aeval_coe, aeval_def, hProot, zero_mem_class.coe_zero] },
end

/-- The map `E → F` when `E` is an intermediate field contained in the intermediate field `F`.

This is the intermediate field version of `subalgebra.inclusion`. -/
def inclusion {E F : intermediate_field K L} (hEF : E ≤ F) : E →ₐ[K] F :=
subalgebra.inclusion hEF

lemma inclusion_injective {E F : intermediate_field K L} (hEF : E ≤ F) :
  function.injective (inclusion hEF) :=
subalgebra.inclusion_injective hEF

@[simp] lemma inclusion_self {E : intermediate_field K L}:
  inclusion (le_refl E) = alg_hom.id K E :=
subalgebra.inclusion_self

@[simp] lemma inclusion_inclusion {E F G : intermediate_field K L} (hEF : E ≤ F) (hFG : F ≤ G)
  (x : E) : inclusion hFG (inclusion hEF x) = inclusion (le_trans hEF hFG) x :=
subalgebra.inclusion_inclusion hEF hFG x

@[simp] lemma coe_inclusion {E F : intermediate_field K L} (hEF : E ≤ F) (e : E) :
  (inclusion hEF e : L) = e := rfl

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
def lift {F : intermediate_field K L} (E : intermediate_field K F) : intermediate_field K L :=
E.map (val F)

instance has_lift {F : intermediate_field K L} :
  has_lift_t (intermediate_field K F) (intermediate_field K L) := ⟨lift⟩

section restrict_scalars
variables (K) [algebra L' L] [is_scalar_tower K L' L]

/-- Given a tower `L / ↥E / L' / K` of field extensions, where `E` is an `L'`-intermediate field of
`L`, reinterpret `E` as a `K`-intermediate field of `L`. -/
def restrict_scalars (E : intermediate_field L' L) :
  intermediate_field K L :=
{ carrier := E.carrier,
  ..E.to_subfield,
  ..E.to_subalgebra.restrict_scalars K }

@[simp] lemma coe_restrict_scalars {E : intermediate_field L' L} :
  (restrict_scalars K E : set L) = (E : set L) := rfl

@[simp] lemma restrict_scalars_to_subalgebra {E : intermediate_field L' L} :
  (E.restrict_scalars K).to_subalgebra = E.to_subalgebra.restrict_scalars K :=
set_like.coe_injective rfl

@[simp] lemma restrict_scalars_to_subfield {E : intermediate_field L' L} :
  (E.restrict_scalars K).to_subfield = E.to_subfield :=
set_like.coe_injective rfl

@[simp] lemma mem_restrict_scalars {E : intermediate_field L' L} {x : L} :
  x ∈ restrict_scalars K E ↔ x ∈ E := iff.rfl

lemma restrict_scalars_injective :
  function.injective (restrict_scalars K : intermediate_field L' L → intermediate_field K L) :=
λ U V H, ext $ λ x, by rw [← mem_restrict_scalars K, H, mem_restrict_scalars]

end restrict_scalars

/-- This was formerly an instance called `lift2_alg`, but an instance above already provides it. -/
example {F : intermediate_field K L} {E : intermediate_field F L} : algebra K E :=
by apply_instance

end tower

section finite_dimensional

variables (F E : intermediate_field K L)

instance finite_dimensional_left [finite_dimensional K L] : finite_dimensional K F :=
left K F L

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
to_subalgebra_injective $ subalgebra.to_submodule.injective $ eq_of_le_of_finrank_le h_le h_finrank

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

lemma is_algebraic_iff {x : S} : is_algebraic K x ↔ is_algebraic K (x : L) :=
(is_algebraic_algebra_map_iff (algebra_map S L).injective).symm

lemma is_integral_iff {x : S} : is_integral K x ↔ is_integral K (x : L) :=
by rw [←is_algebraic_iff_is_integral, is_algebraic_iff, is_algebraic_iff_is_integral]

lemma minpoly_eq (x : S) : minpoly K x = minpoly K (x : L) :=
begin
  by_cases hx : is_integral K x,
  { exact minpoly.eq_of_algebra_map_eq (algebra_map S L).injective hx rfl },
  { exact (minpoly.eq_zero hx).trans (minpoly.eq_zero (mt is_integral_iff.mpr hx)).symm },
end

end intermediate_field

/-- If `L/K` is algebraic, the `K`-subalgebras of `L` are all fields.  -/
def subalgebra_equiv_intermediate_field (alg : algebra.is_algebraic K L) :
  subalgebra K L ≃o intermediate_field K L :=
{ to_fun := λ S, S.to_intermediate_field (λ x hx, S.inv_mem_of_algebraic (alg (⟨x, hx⟩ : S))),
  inv_fun := λ S, S.to_subalgebra,
  left_inv := λ S, to_subalgebra_to_intermediate_field _ _,
  right_inv := to_intermediate_field_to_subalgebra,
  map_rel_iff' := λ S S', iff.rfl }

@[simp] lemma mem_subalgebra_equiv_intermediate_field (alg : algebra.is_algebraic K L)
  {S : subalgebra K L} {x : L} :
  x ∈ subalgebra_equiv_intermediate_field alg S ↔ x ∈ S :=
iff.rfl

@[simp] lemma mem_subalgebra_equiv_intermediate_field_symm (alg : algebra.is_algebraic K L)
  {S : intermediate_field K L} {x : L} :
  x ∈ (subalgebra_equiv_intermediate_field alg).symm S ↔ x ∈ S :=
iff.rfl
