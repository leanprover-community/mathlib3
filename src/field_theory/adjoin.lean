/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/

import field_theory.intermediate_field
import field_theory.subfield
import linear_algebra.finite_dimensional

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
def adjoin : intermediate_field F E :=
{ algebra_map_mem' := λ x, subfield.subset_closure (or.inl (set.mem_range.mpr ⟨x,rfl⟩)),
  ..subfield.closure (set.range (algebra_map F E) ∪ S) }

lemma subset_adjoin_of_subset_left {F : subfield E} {T : set E} (HT : T ⊆ F) :
  T ⊆ adjoin F S :=
λ x hx, (adjoin F S).algebra_map_mem ⟨x, HT hx⟩

lemma adjoin.range_algebra_map_subset : set.range (algebra_map F E) ⊆ adjoin F S :=
begin
  intros x hx,
  cases hx with f hf,
  rw ← hf,
  exact (adjoin F S).algebra_map_mem f,
end

instance adjoin.field_coe : has_coe_t F (adjoin F S) :=
{coe := λ x, ⟨algebra_map F E x, (adjoin F S).algebra_map_mem x⟩}

lemma subset_adjoin : S ⊆ adjoin F S :=
λ x hx, subfield.subset_closure (or.inr hx)

instance adjoin.set_coe : has_coe_t S (adjoin F S) :=
{coe := λ x, ⟨x,subset_adjoin F S (subtype.mem x)⟩}

lemma adjoin.mono (T : set E) (h : S ⊆ T) : (adjoin F S : set E) ⊆ adjoin F T :=
subfield.closure_mono (set.union_subset
  (set.subset_union_left _ _)
  (set.subset_union_of_subset_right h _))

lemma le_adjoin_to_subfield (F : subfield E) : F ≤ (adjoin F S).to_subfield :=
λ x hx, (adjoin F S).algebra_map_mem ⟨x, hx⟩

lemma subset_adjoin_of_subset_right {T : set E} (H : T ⊆ S) : T ⊆ adjoin F S :=
begin
  intros x hx,
  exact subset_adjoin F S (H hx),
end

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ⊆ K`. -/
lemma adjoin_le_subfield {K : subfield E} (HF : set.range (algebra_map F E) ⊆ K)
  (HS : S ⊆ K) : (adjoin F S).to_subfield ≤ K :=
begin
  apply subfield.closure_le.mpr,
  rw set.union_subset_iff,
  exact ⟨HF, HS⟩,
end

/-- `adjoin F S ≤ K` if `K` is an intermediate field that contains `S`. -/
lemma adjoin_le {K : intermediate_field F E} (HS : S ⊆ K) :
  adjoin F S ≤ K :=
show (adjoin F S).to_subfield ≤ K.to_subfield,
from adjoin_le_subfield _ S K.set_range_subset HS

lemma adjoin_le_algebra_adjoin (inv_mem : ∀ x ∈ algebra.adjoin F S, x⁻¹ ∈ algebra.adjoin F S) :
  (field.adjoin F S).to_subalgebra ≤ algebra.adjoin F S :=
show field.adjoin F S ≤
  { neg_mem' := λ x, (algebra.adjoin F S).neg_mem, inv_mem' := inv_mem, .. algebra.adjoin F S},
from adjoin_le _ _ algebra.subset_adjoin

@[elab_as_eliminator]
lemma adjoin_induction {s : set E} {p : E → Prop} {x} (h : x ∈ adjoin F s)
  (Hs : ∀ x ∈ s, p x) (Hmap : ∀ x, p (algebra_map F E x))
  (Hadd : ∀ x y, p x → p y → p (x + y))
  (Hneg : ∀ x, p x → p (-x))
  (Hinv : ∀ x, p x → p x⁻¹)
  (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
subfield.closure_induction h (λ x hx, or.cases_on hx (λ ⟨x, hx⟩, hx ▸ Hmap x) (Hs x))
  ((algebra_map F E).map_one ▸ Hmap 1)
  Hadd Hneg Hinv Hmul

/-- `S ⊆ adjoin F T` if and only if `adjoin F S ⊆ adjoin F T`. -/
lemma subset_adjoin_iff {T : set E} : S ≤ adjoin F T ↔ adjoin F S ≤ adjoin F T :=
⟨λ h, adjoin_le_subfield F S (adjoin.range_algebra_map_subset F T) h,
 λ h, set.subset.trans (subset_adjoin F S) h⟩

lemma subfield_subset_adjoin_self {F : subfield E} {T : set E} {HT : T ⊆ F} :
  T ⊆ adjoin F S :=
λ x hx, (adjoin F S).algebra_map_mem ⟨x, HT hx⟩

lemma adjoin_subset_adjoin_iff {F' : Type*} [field F'] [algebra F' E]
  {S S' : set E} : (adjoin F S : set E) ⊆ adjoin F' S' ↔
  set.range (algebra_map F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
⟨λ h, ⟨trans (adjoin.range_algebra_map_subset _ _) h, trans (subset_adjoin _ _) h⟩,
  λ ⟨hF, hS⟩, subfield.closure_le.mpr (set.union_subset hF hS)⟩

/-- `F[S][T] = F[S ∪ T]` -/
lemma adjoin_adjoin_left (T : set E) : (adjoin (adjoin F S) T : set E) = adjoin F (S ∪ T) :=
begin
  apply set.eq_of_subset_of_subset; rw adjoin_subset_adjoin_iff; split,
  { rintros _ ⟨⟨x, hx⟩, rfl⟩, exact adjoin.mono _ _ _ (set.subset_union_left _ _) hx },
  { exact subset_adjoin_of_subset_right _ _ (set.subset_union_right _ _) },
  { exact subset_adjoin_of_subset_left _ (adjoin.range_algebra_map_subset _ _) },
  { exact set.union_subset
            (subset_adjoin_of_subset_left _ (subset_adjoin _ _))
            (subset_adjoin _ _) },
end

lemma adjoin_map {E' : Type*} [field E'] [algebra F E'] (f : E →ₐ[F] E') :
  (adjoin F S).map f = adjoin F (f '' S) :=
begin
  ext x,

  show x ∈ (subfield.closure (set.range (algebra_map F E) ∪ S)).map (f : E →+* E') ↔
       x ∈ subfield.closure (set.range (algebra_map F E') ∪ f '' S),
  rw [ring_hom.map_field_closure, set.image_union, ← set.range_comp, ← ring_hom.coe_comp,
      f.comp_algebra_map],
  refl
end

variables (α : E)

notation K`⟮`:std.prec.max_plus l:(foldr `, ` (h t, set.insert h t) ∅) `⟯` := adjoin K l

--unfortunately this lemma is not definitionally true
lemma adjoin_singleton : F⟮α⟯ = adjoin F {α} :=
begin
  change adjoin F (insert α ∅) = adjoin F {α},
  rw insert_emptyc_eq α,
  exact set.is_lawful_singleton,
end

lemma mem_adjoin_simple_self : α ∈ F⟮α⟯ :=
begin
  rw adjoin_singleton,
  exact subset_adjoin F {α} (set.mem_singleton α),
end

/-- generator of `F⟮α⟯` -/
def adjoin_simple.gen : F⟮α⟯ := ⟨α, mem_adjoin_simple_self F α⟩

lemma adjoin_simple.algebra_map_gen : algebra_map F⟮α⟯ E (adjoin_simple.gen F α) = α := rfl

lemma adjoin_simple_adjoin_simple (β : E) : F⟮α,β⟯ = adjoin F {α,β} :=
begin
  change adjoin F (insert α (insert β ∅)) = adjoin F _,
  simp only [insert_emptyc_eq],
end

end field
