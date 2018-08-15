/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/

import ring_theory.subring

variables {F : Type*} [field F] (s : set F)

class is_subfield extends is_subring s :=
(inv_mem : ∀ {x : F}, x ∈ s → x⁻¹ ∈ s)

open is_subfield is_submonoid is_add_submonoid

instance subtype.field [is_subfield s] : field s :=
{ add := λ (a b : s), ⟨a.val + b.val, add_mem a.property b.property⟩, 
  add_assoc := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (add_assoc a b c),
  zero := ⟨0, zero_mem s⟩, 
  zero_add := assume ⟨a, _⟩, subtype.eq (zero_add a), 
  add_zero := assume ⟨a, _⟩, subtype.eq (add_zero a),
  neg := λ (a : s), ⟨ -a.val, is_add_subgroup.neg_mem a.property⟩ ,
  add_left_neg := assume ⟨a, _⟩, subtype.eq (add_left_neg a),
  add_comm := assume ⟨a, _⟩ ⟨b, _⟩, subtype.eq (add_comm a b),
  mul := λ (a b : s), ⟨a.val * b.val, mul_mem a.property b.property⟩,
  mul_assoc := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (mul_assoc a b c),   
  one := ⟨1, one_mem s⟩,
  one_mul := assume ⟨a, _⟩, subtype.eq (one_mul a), 
  mul_one := assume ⟨a, _⟩, subtype.eq (mul_one a),
  left_distrib := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (left_distrib a b c),
  right_distrib := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (right_distrib a b c),
  inv := λ (a : s), ⟨a.val⁻¹, inv_mem a.property⟩,   
  zero_ne_one := begin apply (iff_false_left zero_ne_one).mp, simp, exact F, apply_instance, end,
  mul_inv_cancel := assume ⟨a, _⟩, λ h, subtype.eq (mul_inv_cancel ((iff_false_left (not_not_intro h)).mp (begin dunfold ne, rw auto.not_not_eq, apply subtype.ext, end))),
  inv_mul_cancel := assume ⟨a, _⟩, λ h, subtype.eq (inv_mul_cancel ((iff_false_left (not_not_intro h)).mp (begin dunfold ne, rw auto.not_not_eq, apply subtype.ext, end))),
  mul_comm := assume ⟨a, _⟩ ⟨b, _⟩, subtype.eq (mul_comm a b),}

instance is_subfield.is_ring_hom [is_subring s] : is_ring_hom (@subtype.val F s) :=
{ map_add := λ _ _, rfl,
  map_mul := λ _ _, rfl,
  map_one := rfl }
