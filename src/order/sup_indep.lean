/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.lattice

/-!
# Finite supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

In distributive lattices, this is equivalent to being pairwise disjoint. Note however that
`set.pairwise_disjoint` does not currently handle indexed sets.

## TODO

As we don't have `lattice_bot`, all this file is set into distributive lattices, which kills the
nuance with `set.pairwise_disjoint`. This ought to change.

`complete_lattice.independent` and `complete_lattice.set_independent` should live in this file.
-/

variables {α β ι ι' : Type*}

namespace finset
variables [distrib_lattice_bot α] [decidable_eq ι] [decidable_eq ι']

/-- Supremum independence of finite sets. -/
def sup_indep (s : finset ι) (f : ι → α) : Prop :=
∀ ⦃a⦄, a ∈ s → disjoint (f a) ((s.erase a).sup f)

variables {s t : finset ι} {f : ι → α}

lemma sup_indep.subset (ht : t.sup_indep f) (h : s ⊆ t) :
  s.sup_indep f :=
λ a ha, (ht $ h ha).mono_right $ sup_mono $ erase_subset_erase _ h

lemma sup_indep_empty (f : ι → α) : (∅ : finset ι).sup_indep f := λ a ha, ha.elim

lemma sup_indep_singleton (i : ι) (f : ι → α) : ({i} : finset ι).sup_indep f :=
λ j hj, by { rw [mem_singleton.1 hj, erase_singleton, sup_empty], exact disjoint_bot_right }

lemma sup_indep.attach (hs : s.sup_indep f) : s.attach.sup_indep (f ∘ subtype.val) :=
λ i _,
  by { rw [←finset.sup_image, image_erase subtype.val_injective, attach_image_val], exact hs i.2 }

-- This really is a `set.pairwise_disjoint` lemma, but we can't state it that way
/-- Bind operation for `sup_indep`. -/
lemma sup_indep.sup {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.sup g).sup_indep f :=
begin
  rintro i hi,
  rw disjoint_sup_right',
  refine λ j hj, _,
  rw mem_sup at hi,
  obtain ⟨i', hi', hi⟩ := hi,
  rw [mem_erase, mem_sup] at hj,
  obtain ⟨hij, j', hj', hj⟩ := hj,
  obtain hij' | hij' := eq_or_ne j' i',
  { exact disjoint_sup_right'.1 (hg i' hi' hi) _ (mem_erase.2 ⟨hij, hij'.subst hj⟩) },
  { exact (hs hi').mono (le_sup hi) ((le_sup hj).trans $ le_sup $ mem_erase.2 ⟨hij', hj'⟩) }
end

/-- Bind operation for `sup_indep`. -/
lemma sup_indep.bUnion {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.bUnion g).sup_indep f :=
by { rw ←sup_eq_bUnion, exact hs.sup hg }

-- Could be generalized if `set.pairwise_disjoint` were about indexed sets
lemma sup_indep.pairwise_disjoint {s : finset α} [decidable_eq α] (hs : s.sup_indep id) :
  (s : set α).pairwise_disjoint :=
λ a ha b hb hab, (hs ha).mono_right $ le_sup $ mem_erase.2 ⟨hab.symm, hb⟩

-- Could be generalized if `set.pairwise_disjoint` were about indexed sets
-- Once `finset.sup_indep` will have been generalized to non distributive lattices, we can state
-- this lemma for nondistributive atomic lattices. This setting makes the `←` implication much
-- harder.
lemma sup_inded_iff_pairwise_disjoint {s : finset α} [decidable_eq α] :
  s.sup_indep id ↔ (s : set α).pairwise_disjoint :=
begin
  refine ⟨sup_indep.pairwise_disjoint, λ hs a ha, _⟩,
  rw disjoint_sup_right',
  exact λ b hb, hs a ha b (mem_of_mem_erase hb) (ne_of_mem_erase hb).symm,
end

end finset
