/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/

variables {F : Type*} [field F] (s : set F)

class is_subfield extends is_subring s :=
(inv_mem : ∀ {x : F}, x ∈ s → x⁻¹ ∈ s)

open is_subfield 

instance subset.field [is_subfield s] : field s :=
{ inv := λ (a : s), ⟨a.val⁻¹, inv_mem a.property⟩,   
  zero_ne_one := (iff_false_right (@zero_ne_one F _)).mp subtype.mk_eq_mk,
  mul_inv_cancel := assume ⟨a, _⟩, λ h, subtype.eq (mul_inv_cancel ((iff_false_left (not_not_intro h)).mp (begin dunfold ne, rw auto.not_not_eq, apply subtype.ext, end))),
  inv_mul_cancel := assume ⟨a, _⟩, λ h, subtype.eq (inv_mul_cancel ((iff_false_left (not_not_intro h)).mp (begin dunfold ne, rw auto.not_not_eq, apply subtype.ext, end))),
  .. subset.comm_ring,}

instance subtype.field [is_subfield s] : field (subtype s) := subset.field s
