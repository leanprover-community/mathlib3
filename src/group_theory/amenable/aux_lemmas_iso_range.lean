/-
Copyright (c) 2022 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold.
-/
import topology.category.Top
import topology.algebra.monoid



/-!
# Some lemma about injective group homomorphisms


## Main Statement

- `iso_range_of_injective` : For an injective group homomorphism,
    the domain is iśomorphic to its range.

## Implementation Notes

TODO : These statements are probably already in the mathlib
(probably in some more general form). These lemmas may be
replaced by / moved to different parts of the mathlib.

## Tags

-/

lemma iso_range_of_injective_inverse_ex
  {G H:Type*} [group G] [group H]
  (i : H →* G)
  : ∀ (x: i.range), ∃ h : H, i h = x
:= begin
  assume x,
  rw ← monoid_hom.mem_range,
  by refine set_like.coe_mem x,
end

noncomputable def iso_range_of_injective_inverse
  {G H:Type*} [group G] [group H]
  (i : H →* G)
  : i.range → H
:= (λ x, classical.some (iso_range_of_injective_inverse_ex i x))

@[simp]
lemma iso_range_of_injective_inverse_spec
  {G H:Type*} [group G] [group H]
  (i : H →* G)
  : ∀ x, i (iso_range_of_injective_inverse i x) = x
:= begin
  assume x,
  unfold iso_range_of_injective_inverse,
  exact classical.some_spec (iso_range_of_injective_inverse_ex i x),
end

@[simp]
lemma iso_range_of_injective_inverse_spec'
  {G H:Type*} [group G] [group H]
  (i : H →* G)
  : ∀ x, i.range_restrict (iso_range_of_injective_inverse i x) = x
:= begin
  assume x,
  rw ← set_like.coe_eq_coe,
  exact  iso_range_of_injective_inverse_spec i x,
end

/-- If G → H is a monoid homomorphism between groups,
    then G is isomorphic (as monoid) to the range-/
noncomputable lemma iso_range_of_injective
  {G H:Type*} [group G] [group H]
  {i : H →* G}
  (i_inj : function.injective i)
  : H ≃* i.range
:= mul_equiv.mk i.range_restrict (iso_range_of_injective_inverse i)
  (begin
    unfold function.left_inverse,
    assume x,
    apply i_inj,
    rw iso_range_of_injective_inverse_spec,
    simp,
  end)
  (begin
    unfold function.right_inverse,
    unfold function.left_inverse,
    assume x,
    simp,
  end )
  (begin
    assume x y,
    simp,
  end)

  noncomputable lemma iso_range_of_injective'
  {G H:Type*} [group G] [group H]
  {i : H →* G}
  (i_inj : function.injective i)
  : i.range ≃* H
:= (iso_range_of_injective i_inj).symm
