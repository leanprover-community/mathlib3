/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/

import field_theory.intermediate_field
import ring_theory.adjoin
>>>>>>> mathlib/master

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `algebra.adjoin K {x}` might not include `x⁻¹`.

## Main results

- `adjoin_adjoin_left`: adjoining S and then T is the same as adjoining S ∪ T.
- `bot_eq_top_of_dim_adjoin_eq_one`: if `F⟮x⟯` has dimension `1` over `F` for every `x`
  in `E` then `F = E`

## Notation

 - `F⟮α⟯`: adjoin a single element `α` to `F`.
-/

namespace field

section adjoin_def
variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

/--
`adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`.
-/
def adjoin : intermediate_field F E :=
{ algebra_map_mem' := λ x, subfield.subset_closure (or.inl (set.mem_range.mpr ⟨x,rfl⟩)),
  ..subfield.closure (set.range (algebra_map F E) ∪ S) }

lemma adjoin_eq_range_algebra_map_adjoin :
  (adjoin F S : set E) = set.range (algebra_map (adjoin F S) E) := (subtype.range_coe).symm

lemma adjoin.algebra_map_mem (x : F) : algebra_map F E x ∈ adjoin F S :=
subfield.subset_closure (or.inl (set.mem_range_self x))

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

lemma algebra_adjoin_le_adjoin :
  algebra.adjoin F S ≤ (field.adjoin F S).to_subalgebra :=
algebra.adjoin_le (subset_adjoin _ _)

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
/-- `F[S][T] = F[T][S]` -/
lemma adjoin_adjoin_comm (T : set E) :
  (adjoin (adjoin F S : set E) T : set E) = (adjoin (adjoin F T : set E) S : set E) :=
by rw [adjoin_adjoin_left, adjoin_adjoin_left, set.union_comm]

/--
Variation on `set.insert` to enable good notation for adjoining elements to fields.
Used to preferentially use `singleton` rather than `insert` when adjoining one element.
-/
--this definition of notation is courtesy of Kyle Miller on zulip
class insert {α : Type*} (s : set α) :=
(insert : α → set α)

@[priority 1000]
instance insert_empty {α : Type*} : insert (∅ : set α) :=
{ insert := λ x, @singleton _ _ set.has_singleton x }

@[priority 900]
instance insert_nonempty {α : Type*} (s : set α) : insert s :=
{ insert := λ x, set.insert x s }

notation K`⟮`:std.prec.max_plus l:(foldr `, ` (h t, insert.insert t h) ∅) `⟯` := adjoin K l

section adjoin_simple
variables (α : E)

lemma mem_adjoin_simple_self : α ∈ F⟮α⟯ :=
subset_adjoin F {α} (set.mem_singleton α)

/-- generator of `F⟮α⟯` -/
def adjoin_simple.gen : F⟮α⟯ := ⟨α, mem_adjoin_simple_self F α⟩

@[simp] lemma adjoin_simple.algebra_map_gen : algebra_map F⟮α⟯ E (adjoin_simple.gen F α) = α := rfl

lemma adjoin_simple_adjoin_simple (β : E) : (F⟮α⟯⟮β⟯ : set E) = (F⟮α, β⟯ : set E) :=
adjoin_adjoin_left _ _ _

lemma adjoin_simple_comm (β : E) : (F⟮α⟯⟮β⟯ : set E) = (F⟮β⟯⟮α⟯ : set E) :=
adjoin_adjoin_comm _ _ _

end adjoin_simple
end adjoin_def

section adjoin_subalgebra_lattice
variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E] {α : E} {S : set E}

lemma adjoin_eq_bot (h : S ⊆ (⊥ : subalgebra F E)) : adjoin F S = ⊥ :=
begin
  rw eq_bot_iff,
  intros x,
  rw [subalgebra.mem_coe, subalgebra.mem_coe, algebra.mem_bot],
  rw algebra.coe_bot at h,
  apply adjoin_subset_subfield _ _ set.subset.rfl h,
end

lemma adjoin_simple_eq_bot (hα : α ∈ ((⊥ : subalgebra F E) : set E)) : F⟮α⟯ = (⊥ : subalgebra F E) :=
adjoin_eq_bot (set.singleton_subset_iff.mpr hα)

lemma adjoin_zero : F⟮0⟯ = (⊥ : subalgebra F E) :=
adjoin_simple_eq_bot (algebra.mem_bot.mpr (is_add_submonoid.zero_mem))

lemma adjoin_one : F⟮1⟯ = (⊥ : subalgebra F E) :=
adjoin_simple_eq_bot (algebra.mem_bot.mpr (is_submonoid.one_mem))

lemma sub_bot_of_adjoin_sub_bot (h : adjoin F S = ⊥) : S ⊆ (⊥ : subalgebra F E) :=
calc S ⊆ adjoin F S : subset_adjoin _ _
  ... = (⊥ : subalgebra F E) : congr_arg coe h

lemma mem_bot_of_adjoin_simple_sub_bot (h : F⟮α⟯ = ⊥) : α ∈ ((⊥ : subalgebra F E) : set E) :=
set.singleton_subset_iff.mp (sub_bot_of_adjoin_sub_bot h)

lemma adjoin_eq_bot_iff : S ⊆ (⊥ : subalgebra F E) ↔ adjoin F S = ⊥ :=
⟨adjoin_eq_bot, sub_bot_of_adjoin_sub_bot⟩

lemma adjoin_simple_eq_bot_iff : α ∈ (⊥ : subalgebra F E) ↔ F⟮α⟯ = ⊥ :=
⟨adjoin_simple_eq_bot, mem_bot_of_adjoin_simple_sub_bot⟩

section adjoin_dim
open finite_dimensional vector_space

lemma sub_bot_of_adjoin_dim_eq_one (h : dim F (adjoin F S) = 1) : S ⊆ (⊥ : subalgebra F E) :=
by rwa [adjoin_eq_bot_iff, ← subalgebra.dim_eq_one_iff]

lemma mem_bot_of_adjoin_simple_dim_eq_one (h : dim F F⟮α⟯ = 1) : α ∈ ((⊥ : subalgebra F E) : set E) :=
set.singleton_subset_iff.mp (sub_bot_of_adjoin_dim_eq_one h)

lemma adjoin_dim_eq_one_of_sub_bot (h : S ⊆ (⊥ : subalgebra F E)) : dim F (adjoin F S) = 1 :=
by { rw adjoin_eq_bot h, exact subalgebra.dim_bot }

lemma adjoin_simple_dim_eq_one_of_mem_bot (h : α ∈ ((⊥ : subalgebra F E) : set E)) : dim F F⟮α⟯ = 1 :=
adjoin_dim_eq_one_of_sub_bot (set.singleton_subset_iff.mpr h)

lemma adjoin_dim_eq_one_iff : dim F (adjoin F S) = 1 ↔ S ⊆ (⊥ : subalgebra F E) :=
⟨sub_bot_of_adjoin_dim_eq_one, adjoin_dim_eq_one_of_sub_bot⟩

lemma adjoin_simple_dim_eq_one_iff : dim F F⟮α⟯ = 1 ↔ α ∈ (⊥ : subalgebra F E) :=
⟨mem_bot_of_adjoin_simple_dim_eq_one, adjoin_simple_dim_eq_one_of_mem_bot⟩

lemma adjoin_findim_eq_one_iff : findim F (adjoin F S) = 1 ↔ S ⊆ (⊥ : subalgebra F E) :=
by rw [← adjoin_dim_eq_one_iff, subalgebra.dim_eq_one_iff, subalgebra.findim_eq_one_iff]

lemma adjoin_simple_findim_eq_one_iff : findim F F⟮α⟯ = 1 ↔ α ∈ (⊥ : subalgebra F E) :=
by rw [← adjoin_simple_dim_eq_one_iff, subalgebra.dim_eq_one_iff, subalgebra.findim_eq_one_iff]

/-- If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
lemma bot_eq_top_of_dim_adjoin_eq_one (h : ∀ x : E, dim F F⟮x⟯ = 1) : (⊥ : subalgebra F E) = ⊤ :=
by simp [subalgebra.ext_iff, algebra.mem_top, ← adjoin_simple_dim_eq_one_iff, h]

lemma bot_eq_top_of_findim_adjoin_eq_one (h : ∀ x : E, findim F F⟮x⟯ = 1) :
  (⊥ : subalgebra F E) = ⊤ :=
by simp [subalgebra.ext_iff, algebra.mem_top, ← adjoin_simple_findim_eq_one_iff, h]

/-- If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/
lemma bot_eq_top_of_findim_adjoin_le_one [finite_dimensional F E]
  (h : ∀ x : E, findim F F⟮x⟯ ≤ 1) : (⊥ : subalgebra F E) = ⊤ :=
begin
  have : ∀ x : E, findim F F⟮x⟯ = 1 := λ x, by linarith [h x, show 0 < findim F F⟮x⟯, from findim_pos],
  exact bot_eq_top_of_findim_adjoin_eq_one this,
end

end adjoin_dim
end adjoin_subalgebra_lattice

end field
