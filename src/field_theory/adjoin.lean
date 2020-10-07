/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/

import field_theory.tower
import field_theory.intermediate_field

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

namespace intermediate_field

section adjoin_def
variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
def adjoin : intermediate_field F E :=
{ algebra_map_mem' := λ x, subfield.subset_closure (or.inl (set.mem_range_self x)),
  ..subfield.closure (set.range (algebra_map F E) ∪ S) }

@[simp] lemma adjoin_le_iff {T : intermediate_field F E} : adjoin F S ≤ T ↔ S ≤ T :=
⟨λ H, le_trans (le_trans (set.subset_union_right _ _) subfield.subset_closure) H,
  λ H, (@subfield.closure_le E _ (set.range (algebra_map F E) ∪ S) T.to_subfield).mpr
  (set.union_subset (intermediate_field.set_range_subset T) H)⟩

end adjoin_def

section lattice
variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

lemma gc : galois_connection (adjoin F : set E → intermediate_field F E) coe := adjoin_le_iff F

/-- Galois insertion between `adjoin` and `coe`. -/
def gi : galois_insertion (adjoin F : set E → intermediate_field F E) coe :=
{ choice := λ S _, adjoin F S,
  gc := intermediate_field.gc,
  le_l_u := λ S, (intermediate_field.gc (S : set E) (adjoin F S)).1 $ le_refl _,
  choice_eq := λ _ _, rfl }

instance : complete_lattice (intermediate_field F E) :=
galois_insertion.lift_complete_lattice intermediate_field.gi

instance : inhabited (intermediate_field F E) := ⟨⊤⟩

lemma mem_bot {x : E} : x ∈ (⊥ : intermediate_field F E) ↔ x ∈ set.range (algebra_map F E) :=
begin
  suffices : set.range (algebra_map F E) = (⊥ : intermediate_field F E),
  { rw this, refl },
  { change set.range (algebra_map F E) = subfield.closure (set.range (algebra_map F E) ∪ ∅),
    simp [←set.image_univ, ←ring_hom.map_field_closure] }
end

lemma mem_top {x : E} : x ∈ (⊤ : intermediate_field F E) :=
subfield.subset_closure $ or.inr trivial

@[simp] lemma bot_to_subalgebra : (⊥ : intermediate_field F E).to_subalgebra = ⊥ :=
by { ext, rw [mem_to_subalgebra, algebra.mem_bot, mem_bot] }

@[simp] lemma top_to_subalgebra : (⊤ : intermediate_field F E).to_subalgebra = ⊤ :=
begin
  ext,
  rw [mem_to_subalgebra, iff_true_right algebra.mem_top],
  exact mem_top,
end

@[simp] lemma lift2_bot (K : intermediate_field F E) : ↑(⊥ : intermediate_field K E) = K :=
begin
  ext,
  rw [mem_lift2, mem_bot, (show ⇑(algebra_map K E) = coe, by ext;refl), subtype.range_coe],
  refl,
end

@[simp] lemma lift2_top (K : intermediate_field F E) :
  ↑(⊤ : intermediate_field K E) = (⊤ : intermediate_field F E) :=
begin
  ext,
  exact iff_of_true mem_top mem_top,
end

end lattice

section adjoin_def
variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

lemma adjoin_eq_range_algebra_map_adjoin :
  (adjoin F S : set E) = set.range (algebra_map (adjoin F S) E) := (subtype.range_coe).symm

lemma adjoin.algebra_map_mem (x : F) : algebra_map F E x ∈ adjoin F S :=
intermediate_field.algebra_map_mem (adjoin F S) x

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
λ x hx, subfield.subset_closure (or.inr hx)

instance adjoin.set_coe : has_coe_t S (adjoin F S) :=
{coe := λ x, ⟨x,subset_adjoin F S (subtype.mem x)⟩}

@[mono] lemma adjoin.mono (T : set E) (h : S ⊆ T) : adjoin F S ≤ adjoin F T :=
galois_connection.monotone_l gc h

lemma adjoin_contains_field_as_subfield (F : subfield E) : (F : set E) ⊆ adjoin F S :=
λ x hx, adjoin.algebra_map_mem F S ⟨x, hx⟩

lemma subset_adjoin_of_subset_left {F : subfield E} {T : set E} (HT : T ⊆ F) :
  T ⊆ adjoin F S :=
λ x hx, (adjoin F S).algebra_map_mem ⟨x, HT hx⟩

lemma subset_adjoin_of_subset_right {T : set E} (H : T ⊆ S) : T ⊆ adjoin F S :=
begin
  intros x hx,
  exact subset_adjoin F S (H hx),
end

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ≤ K`. -/
lemma adjoin_le_subfield {K : subfield E} (HF : set.range (algebra_map F E) ⊆ K)
  (HS : S ⊆ K) : (adjoin F S).to_subfield ≤ K :=
begin
  apply subfield.closure_le.mpr,
  rw set.union_subset_iff,
  exact ⟨HF, HS⟩,
end

lemma adjoin_subset_adjoin_iff {F' : Type*} [field F'] [algebra F' E]
  {S S' : set E} : (adjoin F S : set E) ⊆ adjoin F' S' ↔
  set.range (algebra_map F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
⟨λ h, ⟨trans (adjoin.range_algebra_map_subset _ _) h, trans (subset_adjoin _ _) h⟩,
  λ ⟨hF, hS⟩, subfield.closure_le.mpr (set.union_subset hF hS)⟩

/-- `F[S][T] = F[S ∪ T]` -/
lemma adjoin_adjoin_left (T : set E) : ↑(adjoin (adjoin F S) T) = adjoin F (S ∪ T) :=
begin
  rw intermediate_field.ext'_iff,
  change ↑(adjoin (adjoin F S) T) = _,
  apply set.eq_of_subset_of_subset; rw adjoin_subset_adjoin_iff; split,
  { rintros _ ⟨⟨x, hx⟩, rfl⟩, exact adjoin.mono _ _ _ (set.subset_union_left _ _) hx },
  { exact subset_adjoin_of_subset_right _ _ (set.subset_union_right _ _) },
  { exact subset_adjoin_of_subset_left _ (adjoin.range_algebra_map_subset _ _) },
  { exact set.union_subset
            (subset_adjoin_of_subset_left _ (subset_adjoin _ _))
            (subset_adjoin _ _) },
end

/-- `F[S][T] = F[T][S]` -/
lemma adjoin_adjoin_comm (T : set E) :
  ↑(adjoin (adjoin F S) T) = (↑(adjoin (adjoin F T) S) : (intermediate_field F E)) :=
by rw [adjoin_adjoin_left, adjoin_adjoin_left, set.union_comm]

lemma adjoin_map {E' : Type*} [field E'] [algebra F E'] (f : E →ₐ[F] E') :
  (adjoin F S).map f = adjoin F (f '' S) :=
begin
  ext x,
  show x ∈ (subfield.closure (set.range (algebra_map F E) ∪ S)).map (f : E →+* E') ↔
       x ∈ subfield.closure (set.range (algebra_map F E') ∪ f '' S),
  rw [ring_hom.map_field_closure, set.image_union, ← set.range_comp, ← ring_hom.coe_comp,
      f.comp_algebra_map],
  refl,
end

/-- `adjoin F S ≤ K` if `K` is an intermediate field that contains `S`. -/
lemma adjoin_le {K : intermediate_field F E} (HS : S ⊆ K) :
  adjoin F S ≤ K :=
show (adjoin F S).to_subfield ≤ K.to_subfield,
from adjoin_le_subfield _ S K.set_range_subset HS

lemma algebra_adjoin_le_adjoin : algebra.adjoin F S ≤ (adjoin F S).to_subalgebra :=
algebra.adjoin_le (subset_adjoin _ _)

lemma adjoin_le_algebra_adjoin (inv_mem : ∀ x ∈ algebra.adjoin F S, x⁻¹ ∈ algebra.adjoin F S) :
  (adjoin F S).to_subalgebra ≤ algebra.adjoin F S :=
show adjoin F S ≤
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

lemma adjoin_simple_adjoin_simple (β : E) : ↑F⟮α⟯⟮β⟯ = F⟮α, β⟯ :=
adjoin_adjoin_left _ _ _

lemma adjoin_simple_comm (β : E) : ↑F⟮α⟯⟮β⟯ = (↑F⟮β⟯⟮α⟯ : intermediate_field F E) :=
adjoin_adjoin_comm _ _ _

end adjoin_simple
end adjoin_def

section adjoin_subalgebra_lattice
variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E] {α : E} {S : set E}

lemma adjoin_eq_bot (h : S ⊆ (⊥ : intermediate_field F E)) : adjoin F S = ⊥ :=
eq_bot_iff.mpr ((adjoin_le_iff F S).mpr h)

lemma adjoin_simple_eq_bot (hα : α ∈ (⊥ : intermediate_field F E)) : F⟮α⟯ = ⊥ :=
adjoin_eq_bot (set.singleton_subset_iff.mpr hα)

@[simp] lemma adjoin_zero : F⟮(0 : E)⟯ = ⊥ :=
adjoin_simple_eq_bot (⊥ : intermediate_field F E).zero_mem

@[simp] lemma adjoin_one : F⟮(1 : E)⟯ = ⊥ :=
adjoin_simple_eq_bot (⊥ : intermediate_field F E).one_mem

lemma sub_bot_of_adjoin_sub_bot (h : adjoin F S = ⊥) : S ⊆ (⊥ : intermediate_field F E) :=
calc S ⊆ adjoin F S : subset_adjoin _ _
  ... = (⊥ : intermediate_field F E) : congr_arg coe h

lemma mem_bot_of_adjoin_simple_sub_bot (h : F⟮α⟯ = ⊥) : α ∈ (⊥ : intermediate_field F E) :=
  ((⊥ : intermediate_field F E).mem_coe α).mp
    (set.singleton_subset_iff.mp (sub_bot_of_adjoin_sub_bot h))

lemma adjoin_eq_bot_iff : S ⊆ (⊥ : intermediate_field F E) ↔ adjoin F S = ⊥ :=
⟨adjoin_eq_bot, sub_bot_of_adjoin_sub_bot⟩

lemma adjoin_simple_eq_bot_iff : α ∈ (⊥ : intermediate_field F E) ↔ F⟮α⟯ = ⊥ :=
⟨adjoin_simple_eq_bot, mem_bot_of_adjoin_simple_sub_bot⟩

section adjoin_dim
open finite_dimensional vector_space

lemma dim_intermediate_field_eq_dim_subalgebra :
  dim F (adjoin F S) = dim F (adjoin F S).to_subalgebra := rfl

lemma findim_intermediate_field_eq_findim_subalgebra :
  findim F (adjoin F S) = findim F (adjoin F S).to_subalgebra := rfl

lemma sub_bot_of_adjoin_dim_eq_one (h : dim F (adjoin F S) = 1) : S ⊆ (⊥ : intermediate_field F E) :=
begin
  rw [dim_intermediate_field_eq_dim_subalgebra, subalgebra.dim_eq_one_iff, ←bot_to_subalgebra] at h,
  rw adjoin_eq_bot_iff,
  ext,
  exact subalgebra.ext_iff.mp h x,
end

lemma mem_bot_of_adjoin_simple_dim_eq_one (h : dim F F⟮α⟯ = 1) : α ∈ ((⊥ : intermediate_field F E) : set E) :=
set.singleton_subset_iff.mp (sub_bot_of_adjoin_dim_eq_one h)

lemma adjoin_dim_eq_one_of_sub_bot (h : S ⊆ (⊥ : intermediate_field F E)) : dim F (adjoin F S) = 1 :=
begin
  rw [dim_intermediate_field_eq_dim_subalgebra, adjoin_eq_bot h, bot_to_subalgebra],
  exact subalgebra.dim_bot,
end

lemma adjoin_simple_dim_eq_one_of_mem_bot (h : α ∈ (⊥ : intermediate_field F E)) : dim F F⟮α⟯ = 1 :=
adjoin_dim_eq_one_of_sub_bot (set.singleton_subset_iff.mpr h)

lemma adjoin_dim_eq_one_iff : dim F (adjoin F S) = 1 ↔ S ⊆ (⊥ : intermediate_field F E) :=
⟨sub_bot_of_adjoin_dim_eq_one, adjoin_dim_eq_one_of_sub_bot⟩

lemma adjoin_simple_dim_eq_one_iff : dim F F⟮α⟯ = 1 ↔ α ∈ (⊥ : intermediate_field F E) :=
⟨mem_bot_of_adjoin_simple_dim_eq_one, adjoin_simple_dim_eq_one_of_mem_bot⟩

lemma adjoin_findim_eq_one_iff : findim F (adjoin F S) = 1 ↔ S ⊆ (⊥ : intermediate_field F E) :=
by rw [findim_intermediate_field_eq_findim_subalgebra, ←adjoin_dim_eq_one_iff,
    dim_intermediate_field_eq_dim_subalgebra, subalgebra.dim_eq_one_iff, subalgebra.findim_eq_one_iff]

lemma adjoin_simple_findim_eq_one_iff : findim F F⟮α⟯ = 1 ↔ α ∈ (⊥ : intermediate_field F E) :=
begin
  rw adjoin_findim_eq_one_iff,
  exact set.singleton_subset_iff,
end

/-- If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
lemma bot_eq_top_of_dim_adjoin_eq_one (h : ∀ x : E, dim F F⟮x⟯ = 1) :
  (⊥ : intermediate_field F E) = ⊤ :=
begin
  ext,
  rw iff_true_right intermediate_field.mem_top,
  exact mem_bot_of_adjoin_simple_dim_eq_one (h x),
end

lemma bot_eq_top_of_findim_adjoin_eq_one (h : ∀ x : E, findim F F⟮x⟯ = 1) :
  (⊥ : intermediate_field F E) = ⊤ :=
begin
  ext,
  rw iff_true_right intermediate_field.mem_top,
  exact adjoin_simple_findim_eq_one_iff.mp (h x),
end

instance [finite_dimensional F E] (K : intermediate_field F E) : finite_dimensional F K :=
  finite_dimensional.finite_dimensional_submodule (K.to_subalgebra.to_submodule)

/-- If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/
lemma bot_eq_top_of_findim_adjoin_le_one [finite_dimensional F E]
  (h : ∀ x : E, findim F F⟮x⟯ ≤ 1) : (⊥ : intermediate_field F E) = ⊤ :=
begin
  apply bot_eq_top_of_findim_adjoin_eq_one,
  exact λ x, by linarith [h x, show 0 < findim F F⟮x⟯, from findim_pos],
end

end adjoin_dim
end adjoin_subalgebra_lattice

section induction

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

lemma induction_on_adjoin [fd : finite_dimensional F E] (P : intermediate_field F E → Prop)
  (base : P ⊥) (ih : ∀ (K : intermediate_field F E) (x : E), P K → P ↑K⟮x⟯)
  (K : intermediate_field F E) : P K :=
begin
  haveI := classical.prop_decidable,
  have induction : ∀ (s : finset E), P (adjoin F ↑s),
  { intro s,
    apply @finset.induction_on E (λ s, P (adjoin F ↑s)) _ s base,
    intros a t _ h,
    rw [finset.coe_insert, ←set.union_singleton, ←adjoin_adjoin_left],
    exact ih (adjoin F ↑t) a h },
  cases finite_dimensional.iff_fg.mp (intermediate_field.finite_dimensional K) with s hs,
  suffices : adjoin F ↑(finset.image coe s) = K,
  { rw ←this, exact induction (s.image coe) },
  apply le_antisymm,
  { apply adjoin_le,
    intros x hx,
    rcases finset.mem_image.mp (finset.mem_coe.mp hx) with ⟨y, _, hy⟩,
    rw ←hy,
    exact subtype.mem y, },
  { change K.to_subalgebra.to_submodule ≤ (adjoin F _).to_subalgebra.to_submodule,
    suffices step : submodule.span F _ = K.to_subalgebra.to_submodule,
    { rw ← step,
      exact submodule.span_le.mpr (subset_adjoin F ↑(finset.image coe s)) },
    have swap : coe = (⇑((val K).to_linear_map : K →ₗ[F] E) : K → E) := rfl,
    rw [finset.coe_image, swap, submodule.span_image, hs, submodule.map_top],
    ext,
    split,
    { intro hx,
      rw linear_map.mem_range at hx,
      cases hx with y hy,
      rw [←hy, alg_hom.to_linear_map_apply],
      exact subtype.mem y },
    { intro hx,
      rw linear_map.mem_range,
      exact ⟨⟨x, hx⟩, rfl⟩ } }
end

end induction

end intermediate_field
