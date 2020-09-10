/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import field_theory.subfield
import ring_theory.algebra_tower

variables (K L : Type*) [field K] [field L] [algebra K L]

/-- `S : intermediate_field K L` is a subset of `L` such that there is a field
tower `L / S / K`. -/
structure intermediate_field extends subalgebra K L :=
(inv_mem : ∀ {a}, a ∈ carrier → a⁻¹ ∈ carrier)

variables {K L} (S : intermediate_field K L)

namespace intermediate_field

instance : has_coe (intermediate_field K L) (subalgebra K L) :=
⟨intermediate_field.to_subalgebra⟩

instance : has_coe_to_sort (intermediate_field K L) :=
{ S := _,
  coe := λ S, ↥(S : set L) }

instance : field S :=
{ inv := λ x, ⟨x⁻¹, S.inv_mem x.2⟩,
  inv_zero := submodule.coe_eq_zero.mp inv_zero,
  mul_inv_cancel := λ x hx, subtype.coe_injective (mul_inv_cancel (mt submodule.coe_eq_zero.mp hx)),
  .. subalgebra.integral_domain (S : subalgebra K L) }

instance : is_subfield (S : set L) :=
{ add_mem := λ a b ha hb, subalgebra.add_mem S ha hb,
  zero_mem := subalgebra.zero_mem S,
  neg_mem := λ a ha, subalgebra.neg_mem S ha,
  mul_mem := λ a b ha hb, subalgebra.mul_mem S ha hb,
  one_mem := subalgebra.one_mem S,
  inv_mem := S.inv_mem }

instance : has_mem L (intermediate_field K L) := ⟨λ x S, x ∈ (S : subalgebra K L)⟩

@[simp] lemma mem_coe_subalgebra {x : L} {S : intermediate_field K L} :
  x ∈ (S : subalgebra K L) ↔ x ∈ S := iff.rfl

instance algebra : algebra K S :=
subalgebra.algebra _

instance to_algebra : algebra S L :=
subalgebra.to_algebra _

instance : is_scalar_tower K S L :=
is_scalar_tower.subalgebra _ _ _

variables {L' : Type*} [field L'] [algebra K L']

def map (f : L →ₐ[K] L') : intermediate_field K L' :=
{ inv_mem := by { rintros _ ⟨x, hx, rfl⟩, exact ⟨x⁻¹, S.inv_mem hx, f.map_inv x⟩ },
  .. subalgebra.map (S : subalgebra K L) f}

lemma add_mem {x y} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S :=
subalgebra.add_mem (S : subalgebra K L) hx hy

lemma mul_mem {x y} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S :=
subalgebra.mul_mem (S : subalgebra K L) hx hy

lemma neg_mem {x} (hx : x ∈ S) : -x ∈ S :=
subalgebra.neg_mem (S : subalgebra K L) hx

lemma zero_mem : (0 : L) ∈ S := subalgebra.zero_mem (S : subalgebra K L)

lemma one_mem : (1 : L) ∈ S := subalgebra.one_mem (S : subalgebra K L)

variables {S}

@[ext]
lemma ext {S' : intermediate_field K L} (h : ∀ x, x ∈ S ↔ x ∈ S') : S = S' :=
by { cases S, cases S', congr, exact subalgebra.ext h }

lemma coe_subalgebra_injective {S S' : intermediate_field K L} (h : (S : subalgebra K L) = S') : S = S' :=
by { ext, rw [← mem_coe_subalgebra, ← mem_coe_subalgebra, h] }

instance : partial_order (intermediate_field K L) :=
{ le := λ S T, (S : set L) ⊆ T,
  le_refl := λ S, set.subset.refl S,
  le_trans := λ _ _ _, set.subset.trans,
  le_antisymm := λ S T hst hts, ext $ λ x, ⟨@hst x, @hts x⟩ }

variables (S)

lemma range_le : set.range (algebra_map K L) ≤ S :=
subalgebra.range_subset S

def val : S →ₐ[K] L := subalgebra.val (S : subalgebra K L)

variables {S}

@[simp] lemma val_mk {x : L} (hx : x ∈ S) : S.val ⟨x, hx⟩ = x := rfl

end intermediate_field
