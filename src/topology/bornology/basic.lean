/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import order.filter.cofinite

/-!
# Basic theory of bornology

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We develop the basic theory of bornologies. Instead of axiomatizing bounded sets and defining
bornologies in terms of those, we recognize that the cobounded sets form a filter and define a
bornology as a filter of cobounded sets which contains the cofinite filter.  This allows us to make
use of the extensive library for filters, but we also provide the relevant connecting results for
bounded sets.

The specification of a bornology in terms of the cobounded filter is equivalent to the standard
one (e.g., see [Bourbaki, *Topological Vector Spaces*][bourbaki1987], **covering bornology**, now
often called simply **bornology**) in terms of bounded sets (see `bornology.of_bounded`,
`is_bounded.union`, `is_bounded.subset`), except that we do not allow the empty bornology (that is,
we require that *some* set must be bounded; equivalently, `∅` is bounded). In the literature the
cobounded filter is generally referred to as the *filter at infinity*.

## Main definitions

- `bornology α`: a class consisting of `cobounded : filter α` and a proof that this filter
  contains the `cofinite` filter.
- `bornology.is_cobounded`: the predicate that a set is a member of the `cobounded α` filter. For
  `s : set α`, one should prefer `bornology.is_cobounded s` over `s ∈ cobounded α`.
- `bornology.is_bounded`: the predicate that states a set is bounded (i.e., the complement of a
  cobounded set). One should prefer `bornology.is_bounded s` over `sᶜ ∈ cobounded α`.
- `bounded_space α`: a class extending `bornology α` with the condition
  `bornology.is_bounded (set.univ : set α)`

Although use of `cobounded α` is discouraged for indicating the (co)boundedness of individual sets,
it is intended for regular use as a filter on `α`.
-/

open set filter

variables {ι α β : Type*}

/-- A **bornology** on a type `α` is a filter of cobounded sets which contains the cofinite filter.
Such spaces are equivalently specified by their bounded sets, see `bornology.of_bounded`
and `bornology.ext_iff_is_bounded`-/
@[ext]
class bornology (α : Type*) :=
(cobounded [] : filter α)
(le_cofinite [] : cobounded ≤ cofinite)

/-- A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions. -/
@[simps]
def bornology.of_bounded {α : Type*} (B : set (set α))
  (empty_mem : ∅ ∈ B) (subset_mem : ∀ s₁ ∈ B, ∀ s₂ : set α, s₂ ⊆ s₁ → s₂ ∈ B)
  (union_mem : ∀ s₁ s₂ ∈ B, s₁ ∪ s₂ ∈ B) (singleton_mem : ∀ x, {x} ∈ B) :
  bornology α :=
{ cobounded :=
  { sets := {s : set α | sᶜ ∈ B},
    univ_sets := by rwa ←compl_univ at empty_mem,
    sets_of_superset := λ x y hx hy, subset_mem xᶜ hx yᶜ (compl_subset_compl.mpr hy),
    inter_sets := λ x y hx hy, by simpa [compl_inter] using union_mem xᶜ hx yᶜ hy, },
  le_cofinite :=
  begin
    rw le_cofinite_iff_compl_singleton_mem,
    intros x,
    change {x}ᶜᶜ ∈ B,
    rw compl_compl,
    exact singleton_mem x
  end }

/-- A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions. -/
@[simps]
def bornology.of_bounded' {α : Type*} (B : set (set α))
  (empty_mem : ∅ ∈ B) (subset_mem : ∀ s₁ ∈ B, ∀ s₂ : set α, s₂ ⊆ s₁ → s₂ ∈ B)
  (union_mem : ∀ s₁ s₂ ∈ B, s₁ ∪ s₂ ∈ B) (sUnion_univ : ⋃₀ B = univ) :
  bornology α :=
bornology.of_bounded B empty_mem subset_mem union_mem $ λ x,
  begin
    rw sUnion_eq_univ_iff at sUnion_univ,
    rcases sUnion_univ x with ⟨s, hs, hxs⟩,
    exact subset_mem s hs {x} (singleton_subset_iff.mpr hxs)
  end

namespace bornology

section
variables [bornology α] {s t : set α} {x : α}

/-- `is_cobounded` is the predicate that `s` is in the filter of cobounded sets in the ambient
bornology on `α` -/
def is_cobounded (s : set α) : Prop := s ∈ cobounded α

/-- `is_bounded` is the predicate that `s` is bounded relative to the ambient bornology on `α`. -/
def is_bounded (s : set α) : Prop := is_cobounded sᶜ

lemma is_cobounded_def {s : set α} : is_cobounded s ↔ s ∈ cobounded α := iff.rfl

lemma is_bounded_def {s : set α} : is_bounded s ↔ sᶜ ∈ cobounded α := iff.rfl

@[simp] lemma is_bounded_compl_iff : is_bounded sᶜ ↔ is_cobounded s :=
by rw [is_bounded_def, is_cobounded_def, compl_compl]

@[simp] lemma is_cobounded_compl_iff : is_cobounded sᶜ ↔ is_bounded s := iff.rfl

alias is_bounded_compl_iff ↔ is_bounded.of_compl is_cobounded.compl
alias is_cobounded_compl_iff ↔ is_cobounded.of_compl is_bounded.compl

@[simp] lemma is_bounded_empty : is_bounded (∅ : set α) :=
by { rw [is_bounded_def, compl_empty], exact univ_mem}

@[simp] lemma is_bounded_singleton : is_bounded ({x} : set α) :=
by {rw [is_bounded_def], exact le_cofinite _ (finite_singleton x).compl_mem_cofinite}

@[simp] lemma is_cobounded_univ : is_cobounded (univ : set α) := univ_mem

@[simp] lemma is_cobounded_inter : is_cobounded (s ∩ t) ↔ is_cobounded s ∧ is_cobounded t :=
inter_mem_iff

lemma is_cobounded.inter (hs : is_cobounded s) (ht : is_cobounded t) : is_cobounded (s ∩ t) :=
is_cobounded_inter.2 ⟨hs, ht⟩

@[simp] lemma is_bounded_union : is_bounded (s ∪ t) ↔ is_bounded s ∧ is_bounded t :=
by simp only [← is_cobounded_compl_iff, compl_union, is_cobounded_inter]

lemma is_bounded.union (hs : is_bounded s) (ht : is_bounded t) : is_bounded (s ∪ t) :=
is_bounded_union.2 ⟨hs, ht⟩

lemma is_cobounded.superset (hs : is_cobounded s) (ht : s ⊆ t) : is_cobounded t :=
mem_of_superset hs ht

lemma is_bounded.subset (ht : is_bounded t) (hs : s ⊆ t) : is_bounded s :=
ht.superset (compl_subset_compl.mpr hs)

@[simp]
lemma sUnion_bounded_univ : (⋃₀ {s : set α | is_bounded s}) = univ :=
sUnion_eq_univ_iff.2 $ λ a, ⟨{a}, is_bounded_singleton, mem_singleton a⟩

lemma comap_cobounded_le_iff [bornology β] {f : α → β} :
  (cobounded β).comap f ≤ cobounded α ↔ ∀ ⦃s⦄, is_bounded s → is_bounded (f '' s) :=
begin
  refine ⟨λ h s hs, _, λ h t ht,
    ⟨(f '' tᶜ)ᶜ, h $ is_cobounded.compl ht, compl_subset_comm.1 $ subset_preimage_image _ _⟩⟩,
  obtain ⟨t, ht, hts⟩ := h hs.compl,
  rw [subset_compl_comm, ←preimage_compl] at hts,
  exact (is_cobounded.compl ht).subset ((image_subset f hts).trans $ image_preimage_subset _ _),
end

end

lemma ext_iff' {t t' : bornology α} :
  t = t' ↔ ∀ s, (@cobounded α t).sets s ↔ (@cobounded α t').sets s :=
(ext_iff _ _).trans filter.ext_iff

lemma ext_iff_is_bounded {t t' : bornology α} :
  t = t' ↔ ∀ s, @is_bounded α t s ↔ @is_bounded α t' s :=
⟨λ h s, h ▸ iff.rfl, λ h, by { ext, simpa only [is_bounded_def, compl_compl] using h sᶜ, }⟩

variables {s : set α}

lemma is_cobounded_of_bounded_iff (B : set (set α)) {empty_mem subset_mem union_mem sUnion_univ} :
  @is_cobounded _ (of_bounded B empty_mem subset_mem union_mem sUnion_univ) s ↔ sᶜ ∈ B := iff.rfl

lemma is_bounded_of_bounded_iff (B : set (set α)) {empty_mem subset_mem union_mem sUnion_univ} :
  @is_bounded _ (of_bounded B empty_mem subset_mem union_mem sUnion_univ) s ↔ s ∈ B :=
by rw [is_bounded_def, ←filter.mem_sets, of_bounded_cobounded_sets, set.mem_set_of_eq, compl_compl]

variables [bornology α]

lemma is_cobounded_bInter {s : set ι} {f : ι → set α} (hs : s.finite) :
  is_cobounded (⋂ i ∈ s, f i) ↔ ∀ i ∈ s, is_cobounded (f i) :=
bInter_mem hs

@[simp] lemma is_cobounded_bInter_finset (s : finset ι) {f : ι → set α} :
  is_cobounded (⋂ i ∈ s, f i) ↔ ∀ i ∈ s, is_cobounded (f i) :=
bInter_finset_mem s

@[simp] lemma is_cobounded_Inter [finite ι] {f : ι → set α} :
  is_cobounded (⋂ i, f i) ↔ ∀ i, is_cobounded (f i) :=
Inter_mem

lemma is_cobounded_sInter {S : set (set α)} (hs : S.finite) :
  is_cobounded (⋂₀ S) ↔ ∀ s ∈ S, is_cobounded s :=
sInter_mem hs

lemma is_bounded_bUnion {s : set ι} {f : ι → set α} (hs : s.finite) :
  is_bounded (⋃ i ∈ s, f i) ↔ ∀ i ∈ s, is_bounded (f i) :=
by simp only [← is_cobounded_compl_iff, compl_Union, is_cobounded_bInter hs]

lemma is_bounded_bUnion_finset (s : finset ι) {f : ι → set α} :
  is_bounded (⋃ i ∈ s, f i) ↔ ∀ i ∈ s, is_bounded (f i) :=
is_bounded_bUnion s.finite_to_set

lemma is_bounded_sUnion {S : set (set α)} (hs : S.finite) :
  is_bounded (⋃₀ S) ↔ (∀ s ∈ S, is_bounded s) :=
by rw [sUnion_eq_bUnion, is_bounded_bUnion hs]

@[simp] lemma is_bounded_Union [finite ι] {s : ι → set α} :
  is_bounded (⋃ i, s i) ↔ ∀ i, is_bounded (s i) :=
by rw [← sUnion_range, is_bounded_sUnion (finite_range s), forall_range_iff]

end bornology

open bornology

lemma set.finite.is_bounded [bornology α] {s : set α} (hs : s.finite) : is_bounded s :=
bornology.le_cofinite α hs.compl_mem_cofinite

instance : bornology punit := ⟨⊥, bot_le⟩

/-- The cofinite filter as a bornology -/
@[reducible] def bornology.cofinite : bornology α :=
{ cobounded := cofinite,
  le_cofinite := le_rfl }

/-- A space with a `bornology` is a **bounded space** if `set.univ : set α` is bounded. -/
class bounded_space (α : Type*) [bornology α] : Prop :=
(bounded_univ : bornology.is_bounded (univ : set α))

namespace bornology

variables [bornology α]

lemma is_bounded_univ : is_bounded (univ : set α) ↔ bounded_space α :=
⟨λ h, ⟨h⟩, λ h, h.1⟩

lemma cobounded_eq_bot_iff : cobounded α = ⊥ ↔ bounded_space α :=
by rw [← is_bounded_univ, is_bounded_def, compl_univ, empty_mem_iff_bot]

variables [bounded_space α]

lemma is_bounded.all (s : set α) : is_bounded s := bounded_space.bounded_univ.subset s.subset_univ
lemma is_cobounded.all (s : set α) : is_cobounded s := compl_compl s ▸ is_bounded.all sᶜ

variable (α)

@[simp] lemma cobounded_eq_bot : cobounded α = ⊥ := cobounded_eq_bot_iff.2 ‹_›

end bornology
