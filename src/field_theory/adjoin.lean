/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/

import field_theory.subfield
import field_theory.tower

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `algebra.adjoin K {x}` might not include `x⁻¹`.

## Main results

(This is just a start; we've got more to add, including a proof of the Primitive Element Theorem.)

- `adjoin_adjoin_left`: adjoining S and then T is the same as adjoining S ∪ T.

## Notation

 - `F⟮α⟯`: adjoin a single element `α` to `F`.
-/

namespace field
variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

/--
`adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`.
-/
def adjoin : subalgebra F E :=
{ carrier :=
  { carrier := field.closure (set.range (algebra_map F E) ∪ S),
    one_mem' := is_submonoid.one_mem,
    mul_mem' := λ x y, is_submonoid.mul_mem,
    zero_mem' := is_add_submonoid.zero_mem,
    add_mem' := λ x y, is_add_submonoid.add_mem },
  algebra_map_mem' := λ x, field.mem_closure (or.inl (set.mem_range.mpr ⟨x,rfl⟩)) }

lemma adjoin.algebra_map_mem (x : F) : algebra_map F E x ∈ adjoin F S :=
field.mem_closure (or.inl (set.mem_range_self x))

lemma subset_adjoin_of_subset_left {F : set E} {HF : is_subfield F} {T : set E} (HT : T ⊆ F) :
  T ⊆ adjoin F S :=
λ x hx, adjoin.algebra_map_mem F S ⟨x, HT hx⟩

lemma adjoin.range_algebra_map_subset : set.range (algebra_map F E) ⊆ adjoin F S :=
begin
  intros x hx,
  cases hx with f hf,
  rw ← hf,
  exact adjoin.algebra_map_mem F S f,
end

instance adjoin.field_coe : has_coe_t F (adjoin F S) :=
{coe := λ x, ⟨algebra_map F E x, adjoin.algebra_map_mem F S x⟩}

lemma subset_adjoin : S ⊆ adjoin F S :=
λ x hx, field.mem_closure (or.inr hx)

instance adjoin.set_coe : has_coe_t S (adjoin F S) :=
{coe := λ x, ⟨x,subset_adjoin F S (subtype.mem x)⟩}

lemma adjoin.mono (T : set E) (h : S ⊆ T) : (adjoin F S : set E) ⊆ adjoin F T :=
field.closure_mono (set.union_subset (set.subset_union_left _ _) (set.subset_union_of_subset_right h _))

instance adjoin.is_subfield : is_subfield (adjoin F S : set E) := field.closure.is_subfield

--Lean has trouble figuring this out on its own
instance adjoin.is_field : field (adjoin F S) := @is_subfield.field E _ ((adjoin F S) : set E) _

lemma adjoin_contains_field_as_subfield (F : set E) {HF : is_subfield F} : F ⊆ adjoin F S :=
λ x hx, adjoin.algebra_map_mem F S ⟨x, hx⟩

lemma subset_adjoin_of_subset_right {T : set E} (H : T ⊆ S) : T ⊆ adjoin F S :=
begin
  intros x hx,
  exact subset_adjoin F S (H hx),
end

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ⊆ K`. -/
lemma adjoin_subset_subfield {K : set E} [is_subfield K] (HF : set.range (algebra_map F E) ⊆ K)
  (HS : S ⊆ K) : (adjoin F S : set E) ⊆ K :=
begin
  apply field.closure_subset,
  rw set.union_subset_iff,
  exact ⟨HF, HS⟩,
end

/-- `S ⊆ adjoin F T` if and only if `adjoin F S ⊆ adjoin F T`. -/
lemma adjoin_subset_iff {T : set E} : S ⊆ adjoin F T ↔ (adjoin F S : set E) ⊆ adjoin F T :=
⟨λ h, adjoin_subset_subfield F S (adjoin.range_algebra_map_subset F T) h,
  λ h, set.subset.trans (subset_adjoin F S) h⟩

lemma subfield_subset_adjoin_self {F : set E} {HF : is_subfield F} {T : set E} {HT : T ⊆ F} :
  T ⊆ adjoin F S :=
λ x hx, adjoin.algebra_map_mem F S ⟨x,HT hx⟩

lemma adjoin_subset_adjoin_iff {F' : Type*} [field F'] [algebra F' E]
  {S S' : set E} : (adjoin F S : set E) ⊆ adjoin F' S' ↔
  set.range (algebra_map F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
⟨λ h, ⟨trans (adjoin.range_algebra_map_subset _ _) h, trans (subset_adjoin _ _) h⟩,
  λ ⟨hF, hS⟩, field.closure_subset (set.union_subset hF hS)⟩

/-- `F[S][T] = F[S ∪ T]` -/
lemma adjoin_adjoin_left (T : set E) : (adjoin (adjoin F S : set E) T : set E) = adjoin F (S ∪ T) :=
begin
  apply set.eq_of_subset_of_subset; rw adjoin_subset_adjoin_iff; split,
  { exact algebra.set_range_subset (adjoin.mono _ _ _ (set.subset_union_left _ _)) },
  { exact subset_adjoin_of_subset_right _ _ (set.subset_union_right _ _) },
  { exact subset_adjoin_of_subset_left _ (adjoin.range_algebra_map_subset _ _) },
  { exact set.union_subset
            (subset_adjoin_of_subset_left _ (subset_adjoin _ _))
            (subset_adjoin _ _) },
end

--this definition of notation is courtesy of Kyle Miller on zulip
class fancy_insert {α : Type*} (s : set α) :=
(insert : α → set α)

@[priority 1000]
instance fancy_insert_empty {α : Type*} : fancy_insert (∅ : set α) :=
{ insert := λ x, @singleton _ _ set.has_singleton x }

@[priority 900]
instance fancy_insert_nonempty {α : Type*} (s : set α) : fancy_insert s :=
{ insert := λ x, set.insert x s }

notation K`⟮`:std.prec.max_plus l:(foldr `, ` (h t, fancy_insert.insert t h) ∅) `⟯` := adjoin K l

variables (α : E)

lemma mem_adjoin_simple_self : α ∈ F⟮α⟯ :=
 subset_adjoin F {α} (set.mem_singleton α)

/-- generator of `F⟮α⟯` -/
def adjoin_simple.gen : F⟮α⟯ := ⟨α, mem_adjoin_simple_self F α⟩

lemma adjoin_simple.algebra_map_gen : algebra_map F⟮α⟯ E (adjoin_simple.gen F α) = α := rfl

lemma adjoin_simple_adjoin_simple (β : E) : (F⟮α⟯⟮β⟯ : set E) = (F⟮α, β⟯ : set E) :=
begin
  apply adjoin_adjoin_left,
end

section
open finite_dimensional

instance adjoin_findim_of_findim_base [F_findim : finite_dimensional F E] (α : E) :
    finite_dimensional F F⟮α⟯ :=
finite_dimensional.finite_dimensional_submodule (F⟮α⟯ : submodule F E)

lemma findim_one_implies_equal (E_dim : findim F E = 1) : set.range(algebra_map F E) = ⊤ :=
begin
  ext1,
  symmetry,
  apply iff_of_true,
  tauto,
  set s : set E := {1} with hs,
  have : fintype s := unique.fintype,
  have s_lin_ind : linear_independent F (coe : s → E) := linear_independent_singleton one_ne_zero,
  have s_card : s.to_finset.card = findim F E := by change s.to_finset.card with 1; rw E_dim,
  obtain ⟨_, s_spans⟩ := set_is_basis_of_linear_independent_of_card_eq_findim s_lin_ind s_card,
  have x_in_span_one : x ∈ submodule.span F s :=
  begin
    rw subtype.range_coe at s_spans,
    rw s_spans,
    exact submodule.mem_top,
  end,
  obtain ⟨a, ha⟩ := submodule.mem_span_singleton.mp x_in_span_one,
  exact ⟨a, by rw [← ha, algebra.smul_def, mul_one]⟩,
end

lemma adjoin.findim_one (hdim : findim F F⟮α⟯ = 1) : α ∈ set.range(algebra_map F E) :=
begin
  have h := (set.ext_iff.mp (findim_one_implies_equal F hdim) (adjoin_simple.gen F α)).mpr (by tauto),
  rw set.mem_range at h,
  cases h with x hx,
  rw set.mem_range,
  use x,
  rw ←adjoin_simple.algebra_map_gen F α,
  rw ←hx,
  refl,
end

end

end field
