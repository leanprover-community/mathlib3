/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import order.filter.cofinite

/-!
# Basic theory of bornology

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

variables {α β : Type*}

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
  (union_mem : ∀ s₁ s₂ ∈ B, s₁ ∪ s₂ ∈ B) (sUnion_univ : ⋃₀ B = univ) :
  bornology α :=
{ cobounded :=
  { sets := {s : set α | sᶜ ∈ B},
    univ_sets := by rwa ←compl_univ at empty_mem,
    sets_of_superset := λ x y hx hy, subset_mem xᶜ hx yᶜ (compl_subset_compl.mpr hy),
    inter_sets := λ x y hx hy, by simpa [compl_inter] using union_mem xᶜ hx yᶜ hy, },
  le_cofinite :=
  begin
    refine le_def.mpr (λ s, _),
    simp only [mem_set_of_eq, mem_cofinite, filter.mem_mk],
    generalize : sᶜ = s',
    refine λ h, h.dinduction_on _ (λ x t hx ht h, _),
    { exact empty_mem, },
    { refine insert_eq x t ▸ union_mem _ _ _ h,
      obtain ⟨b, hb : b ∈ B, hxb : x ∈ b⟩ :=
        mem_sUnion.mp (by simpa [←sUnion_univ] using mem_univ x),
      exact subset_mem _ hb _ (singleton_subset_iff.mpr hxb) },
  end }

namespace bornology

section
variables [bornology α] {s₁ s₂ : set α}

/-- `is_cobounded` is the predicate that `s` is in the filter of cobounded sets in the ambient
bornology on `α` -/
def is_cobounded (s : set α) : Prop := s ∈ cobounded α

/-- `is_bounded` is the predicate that `s` is bounded relative to the ambient bornology on `α`. -/
def is_bounded (s : set α) : Prop := sᶜ ∈ cobounded α

lemma is_cobounded_def {s : set α} : is_cobounded s ↔ s ∈ cobounded α := iff.rfl

lemma is_bounded_def {s : set α} : is_bounded s ↔ sᶜ ∈ cobounded α := iff.rfl

lemma is_bounded_compl_iff {s : set α} : is_bounded sᶜ ↔ is_cobounded s :=
by rw [is_bounded_def, is_cobounded_def, compl_compl]

@[simp]
lemma is_bounded_empty : is_bounded (∅ : set α) :=
by { rw [is_bounded_def, compl_empty], exact univ_mem}

lemma is_bounded.union (h₁ : is_bounded s₁) (h₂ : is_bounded s₂) : is_bounded (s₁ ∪ s₂) :=
by { rw [is_bounded_def, compl_union], exact (cobounded α).inter_sets h₁ h₂ }

lemma is_bounded.subset (h₁ : is_bounded s₂) (h₂ : s₁ ⊆ s₂) : is_bounded s₁ :=
by { rw [is_bounded_def], exact (cobounded α).sets_of_superset h₁ (compl_subset_compl.mpr h₂) }

@[simp]
lemma sUnion_bounded_univ : (⋃₀ {s : set α | is_bounded s}) = set.univ :=
univ_subset_iff.mp $ λ x hx, mem_sUnion_of_mem (mem_singleton x)
  $ le_def.mp (le_cofinite α) {x}ᶜ $ (set.finite_singleton x).compl_mem_cofinite

end

lemma ext_iff' {t t' : bornology α} :
  t = t' ↔ ∀ s, (@cobounded α t).sets s ↔ (@cobounded α t').sets s :=
⟨λ h s, h ▸ iff.rfl, λ h, by { ext, exact h _ } ⟩

lemma ext_iff_is_bounded {t t' : bornology α} :
  t = t' ↔ ∀ s, @is_bounded α t s ↔ @is_bounded α t' s :=
⟨λ h s, h ▸ iff.rfl, λ h, by { ext, simpa only [is_bounded_def, compl_compl] using h sᶜ, }⟩

variables [bornology α]

lemma is_bounded_sUnion {s : set (set α)} (hs : finite s) :
  (∀ t ∈ s, is_bounded t) → is_bounded (⋃₀ s) :=
finite.induction_on hs (λ _, by { rw sUnion_empty, exact is_bounded_empty }) $
λ a s has hs ih h, by
  { rw sUnion_insert,
    exact is_bounded.union (h _ $ mem_insert _ _) (ih $ λ t, h t ∘ mem_insert_of_mem _) }

lemma is_bounded_bUnion {s : set β} {f : β → set α} (hs : finite s) :
  (∀ i ∈ s, is_bounded (f i)) → is_bounded (⋃ i ∈ s, f i) :=
finite.induction_on hs
  (λ _, by { rw bUnion_empty, exact is_bounded_empty })
  (λ a s has hs ih h, by
    { rw bUnion_insert,
      exact is_bounded.union (h a (mem_insert _ _)) (ih (λ i hi, h i (mem_insert_of_mem _ hi))) })

lemma is_bounded_Union [fintype β] {s : β → set α}
  (h : ∀ i, is_bounded (s i)) : is_bounded (⋃ i, s i) :=
by simpa using is_bounded_bUnion finite_univ (λ i _, h i)

end bornology

instance : bornology punit := ⟨⊥, bot_le⟩

/-- The cofinite filter as a bornology -/
@[reducible] def bornology.cofinite : bornology α :=
{ cobounded := cofinite,
  le_cofinite := le_refl _ }

/-- A **bounded space** is a `bornology α` such that `set.univ : set α` is bounded. -/
class bounded_space extends bornology α :=
(bounded_univ : bornology.is_bounded (univ : set α))
