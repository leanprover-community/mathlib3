/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/

import field_theory.subfield
import linear_algebra.finite_dimensional

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, algebra.adjoin K {x} might not include x⁻¹.

## Main results

(This is just a start, We've got more to add, including a proof of the Primitive Element Theorem)

- `adjoin_twice`: adjoining S and then T is the same as adjoining S ∪ T.

## Notation

 - `F[α]` : Adjoin a single element α to F.
-/

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

/--
`adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`.
-/
def adjoin : subalgebra F E := {
  carrier := {
    carrier := field.closure (set.range (algebra_map F E) ∪ S),
    one_mem' := is_submonoid.one_mem,
    mul_mem' := λ x y, is_submonoid.mul_mem,
    zero_mem' := is_add_submonoid.zero_mem,
    add_mem' := λ x y, is_add_submonoid.add_mem,
  },
  algebra_map_mem' := λ x, field.mem_closure (or.inl (set.mem_range.mpr ⟨x,rfl⟩)),
}

lemma adjoin.field_mem (x : F) : algebra_map F E x ∈ adjoin F S :=
field.mem_closure (or.inl (set.mem_range_self x))

lemma adjoin.field_subset : set.range (algebra_map F E) ⊆ adjoin F S :=
begin
  intros x hx,
  cases hx with f hf,
  rw ←hf,
  exact adjoin.field_mem F S f,
end

instance adjoin.field_coe : has_coe_t F (adjoin F S) :=
{coe := λ x, ⟨algebra_map F E x, adjoin.field_mem F S x⟩}

lemma adjoin.set_mem (x : S) : ↑x ∈ adjoin F S :=
field.mem_closure (or.inr (subtype.mem x))

lemma adjoin.set_subset : S ⊆ adjoin F S :=
λ x hx, adjoin.set_mem F S ⟨x,hx⟩

instance adjoin.set_coe : has_coe_t S (adjoin F S) :=
{coe := λ x, ⟨↑x, adjoin.set_mem F S x⟩}

lemma adjoin.mono (T : set E) (h : S ⊆ T) : (adjoin F S : set E) ⊆ adjoin F T :=
field.closure_mono (set.union_subset (set.subset_union_left _ _) (set.subset_union_of_subset_right h _))

instance adjoin.is_subfield : is_subfield (adjoin F S : set E) := field.closure.is_subfield

lemma adjoin_contains_field_as_subfield (F : set E) {HF : is_subfield F} : F ⊆ adjoin F S :=
λ x hx, adjoin.field_mem F S ⟨x, hx⟩

lemma adjoin_contains_subset {T : set E} {H : T ⊆ S} : T ⊆ adjoin F S :=
begin
  intros x hx,
  exact adjoin.set_mem F S ⟨x,H hx⟩,
end

/-- If F ⊆ T and S ⊆ T then F[S] ⊆ F[T] -/
lemma adjoin_subset {T : set E} [is_subfield T] (HF : set.range (algebra_map F E) ⊆ T)
(HS : S ⊆ T) : (adjoin F S : set E) ⊆ T :=
begin
  apply field.closure_subset,
  rw set.union_subset_iff,
  exact ⟨HF,HS⟩,
end

/-- If S ⊆ F[T] then F[S] ⊆ F[T] -/
lemma adjoin_subset' {T : set E} (HT : S ⊆ adjoin F T) : (adjoin F S : set E) ⊆ adjoin F T :=
adjoin_subset F S (adjoin.field_subset F T) HT

lemma set_range_subset {T₁ T₂ : set E} [is_subfield T₁] {hyp : T₁ ⊆ T₂} :
set.range (algebra_map T₁ E) ⊆ T₂ :=
begin
  intros x hx,
  cases hx with f hf,
  rw ←hf,
  cases f with t ht,
  exact hyp ht,
end

lemma adjoin_contains_field_subset {F : set E} {HF : is_subfield F} {T : set E} {HT : T ⊆ F} :
T ⊆ adjoin F S :=
λ x hx, adjoin.field_mem F S ⟨x,HT hx⟩

/-- F[S][T] = F[S ∪ T] -/
lemma adjoin_twice (T : set E) : (adjoin (adjoin F S : set E) T : set E) = adjoin F (S ∪ T) :=
begin
  apply set.eq_of_subset_of_subset,
  { apply adjoin_subset,
    { apply set_range_subset,
      apply adjoin_subset,
      { apply adjoin.field_subset },
      { apply adjoin_contains_subset,
        apply set.subset_union_left} },
    { apply adjoin_contains_subset,
      apply set.subset_union_right } },
  { apply adjoin_subset,
    { transitivity (adjoin F S : set E),
      { apply adjoin.field_subset},
      { apply adjoin_subset,
        { apply adjoin_contains_field_subset,
          apply adjoin.field_subset },
        { apply adjoin_contains_field_subset,
          apply adjoin.set_subset} } },
    { apply set.union_subset,
      { apply adjoin_contains_field_subset,
        apply adjoin.set_subset },
      { apply adjoin.set_subset } } }
end

lemma adjoin.composition :
(algebra_map F E) = (algebra_map (adjoin F S) E).comp (algebra_map F (adjoin F S)) := by ext;refl

variables (α : E)

notation K`[`:std.prec.max_plus l:(foldr `, ` (h t, set.insert h t) ∅) `]` := adjoin K l

--unfortunately this lemma is not definitionally true
lemma adjoin_singleton : F[α] = adjoin F {α} :=
begin
  change adjoin F (insert α ∅) = adjoin F {α},
  rw insert_emptyc_eq α,
  exact set.is_lawful_singleton,
end

lemma mem_adjoin_simple_self : α ∈ F[α] :=
begin
  rw adjoin_singleton,
  exact adjoin.set_mem F {α} (⟨α,set.mem_singleton α⟩ : ({α} : set E)),
end

/-- generator of F(α) -/
def adjoin_simple.gen : F[α] := ⟨α, mem_adjoin_simple_self F α⟩

lemma adjoin_simple.algebra_map_gen : algebra_map F[α] E (adjoin_simple.gen F α) = α := rfl

lemma adjoin_simple_adjoin_simple (β : E) : F[α,β] = adjoin F {α,β} :=
begin
  change adjoin F (insert α (insert β ∅)) = adjoin F _,
  simp only [insert_emptyc_eq],
end
