/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import order.well_founded
import order.order_iso_nat
import data.set.finite
import tactic.tfae

/-!
# Compactness properties for complete lattices

For complete lattices, there are numerous equivalent ways to express the fact that the relation `>`
is well-founded. In this file we define three especially-useful characterisations and provide
proofs that they are indeed equivalent to well-foundedness.

## Main definitions
 * `complete_lattice.is_sup_closed_compact`
 * `complete_lattice.is_Sup_finite_compact`
 * `complete_lattice.is_compact_element`
 * `complete_lattice.is_compactly_generated`

## Main results
The main result is that the following four conditions are equivalent for a complete lattice:
 * `well_founded (>)`
 * `complete_lattice.is_sup_closed_compact`
 * `complete_lattice.is_Sup_finite_compact`
 * `∀ k, complete_lattice.is_compact_element k`

This is demonstrated by means of the following four lemmas:
 * `complete_lattice.well_founded.is_Sup_finite_compact`
 * `complete_lattice.is_Sup_finite_compact.is_sup_closed_compact`
 * `complete_lattice.is_sup_closed_compact.well_founded`
 * `complete_lattice.is_Sup_finite_compact_iff_all_elements_compact`

 We also show well-founded lattices are compactly generated
 (`complete_lattice.compactly_generated_of_well_founded`).

## Tags

complete lattice, well-founded, compact
-/

namespace complete_lattice

variables (α : Type*) [complete_lattice α]

/-- A compactness property for a complete lattice is that any `sup`-closed non-empty subset
contains its `Sup`. -/
def is_sup_closed_compact : Prop :=
  ∀ (s : set α) (h : s.nonempty), (∀ a b, a ∈ s → b ∈ s → a ⊔ b ∈ s) → (Sup s) ∈ s

/-- A compactness property for a complete lattice is that any subset has a finite subset with the
same `Sup`. -/
def is_Sup_finite_compact : Prop :=
∀ (s : set α), ∃ (t : finset α), ↑t ⊆ s ∧ Sup s = t.sup id

/-- An element `k` of a complete lattice is said to be compact if any set with `Sup`
above `k` has a finite subset with `Sup` above `k`.  Such an element is also called
"finite" or "S-compact". -/
def is_compact_element {α : Type*} [complete_lattice α] (k : α) :=
∀ s : set α, k ≤ Sup s → ∃ t : finset α, ↑t ⊆ s ∧ k ≤ t.sup id

/-- A complete lattice is said to be compactly generated if any
element is the `Sup` of compact elements. -/
def is_compactly_generated : Prop :=
∀ (x : α), ∃ (s : set α), (∀ x ∈ s, is_compact_element x) ∧ Sup s = x

/-- An element `k` is compact if and only if any directed set with `Sup` above
`k` already got above `k` at some point in the set. -/
theorem is_compact_element_iff_le_of_directed_Sup_le (k : α) :
  is_compact_element k ↔
  ∀ s : set α, s.nonempty → directed_on (≤) s → k ≤ Sup s → ∃ x : α, x ∈ s ∧ k ≤ x :=
begin
  classical,
  split,
  { by_cases hbot : k = ⊥,
    -- Any nonempty directed set certainly has sup above ⊥
    { rintros _ _ ⟨x, hx⟩ _ _, use x, by simp only [hx, hbot, bot_le, and_self], },
    { intros hk s hne hdir hsup,
      obtain ⟨t, ht⟩ := hk s hsup,
      -- If t were empty, its sup would be ⊥, which is not above k ≠ ⊥.
      have tne : t.nonempty,
      { by_contradiction n,
        rw [finset.nonempty_iff_ne_empty, not_not] at n,
        simp only [n, true_and, set.empty_subset, finset.coe_empty,
          finset.sup_empty, le_bot_iff] at ht,
        exact absurd ht hbot, },
      -- certainly every element of t is below something in s, since ↑t ⊆ s.
      have t_below_s : ∀ x ∈ t, ∃ y ∈ s, x ≤ y, from λ x hxt, ⟨x, ht.left hxt, by refl⟩,
      obtain ⟨x, ⟨hxs, hsupx⟩⟩ := finset.sup_le_of_le_directed s hne hdir t t_below_s,
      exact ⟨x, ⟨hxs, le_trans k (t.sup id) x ht.right hsupx⟩⟩, }, },
  { intros hk s hsup,
    -- Consider the set of finite joins of elements of the (plain) set s.
    let S : set α := { x | ∃ t : finset α, ↑t ⊆ s ∧ x = t.sup id },
    -- S is directed, nonempty, and still has sup above k.
    have dir_US : directed_on (≤) S,
    { rintros x ⟨c, hc⟩ y ⟨d, hd⟩,
      use x ⊔ y,
      split,
      { use c ∪ d,
        split,
        { simp only [hc.left, hd.left, set.union_subset_iff, finset.coe_union, and_self], },
        { simp only [hc.right, hd.right, finset.sup_union], }, },
      simp only [and_self, le_sup_left, le_sup_right], },
    have sup_S : Sup s ≤ Sup S,
    { apply Sup_le_Sup,
      intros x hx, use {x},
      simpa only [and_true, id.def, finset.coe_singleton, eq_self_iff_true, finset.sup_singleton,
        set.singleton_subset_iff], },
    have Sne : S.nonempty,
    { suffices : ⊥ ∈ S, from set.nonempty_of_mem this,
      use ∅,
      simp only [set.empty_subset, finset.coe_empty, finset.sup_empty,
        eq_self_iff_true, and_self], },
    -- Now apply the defn of compact and finish.
    obtain ⟨j, ⟨hjS, hjk⟩⟩ := hk S Sne dir_US (le_trans k (Sup s) (Sup S) hsup sup_S),
    obtain ⟨t, ⟨htS, htsup⟩⟩ := hjS,
    use t, exact ⟨htS, by rwa ←htsup⟩, },
end

lemma finset_sup_compact_of_compact {α β : Type*} [complete_lattice α] {f : β → α}
  (s : finset β) (h : ∀ x ∈ s, is_compact_element (f x)) : is_compact_element (s.sup f) :=
begin
  classical,
  rw is_compact_element_iff_le_of_directed_Sup_le,
  intros d hemp hdir hsup,
  change f with id ∘ f, rw finset.sup_finset_image,
  apply finset.sup_le_of_le_directed d hemp hdir,
  rintros x hx,
  obtain ⟨p, ⟨hps, rfl⟩⟩ := finset.mem_image.mp hx,
  specialize h p hps,
  rw is_compact_element_iff_le_of_directed_Sup_le at h,
  specialize h d hemp hdir (_root_.le_trans (finset.le_sup hps) hsup),
  simpa only [exists_prop],
end

lemma well_founded.is_Sup_finite_compact (h : well_founded ((>) : α → α → Prop)) :
  is_Sup_finite_compact α :=
begin
  intros s,
  let p : set α := { x | ∃ (t : finset α), ↑t ⊆ s ∧ t.sup id = x },
  have hp : p.nonempty, { use [⊥, ∅], simp, },
  obtain ⟨m, ⟨t, ⟨ht₁, ht₂⟩⟩, hm⟩ := well_founded.well_founded_iff_has_max'.mp h p hp,
  use t, simp only [ht₁, ht₂, true_and], apply le_antisymm,
  { apply Sup_le, intros y hy, classical,
    have hy' : (insert y t).sup id ∈ p,
    { use insert y t, simp, rw set.insert_subset, exact ⟨hy, ht₁⟩, },
    have hm' : m ≤ (insert y t).sup id, { rw ← ht₂, exact finset.sup_mono (t.subset_insert y), },
    rw ← hm _ hy' hm', simp, },
  { rw [← ht₂, finset.sup_eq_Sup], exact Sup_le_Sup ht₁, },
end

lemma is_Sup_finite_compact.is_sup_closed_compact (h : is_Sup_finite_compact α) :
  is_sup_closed_compact α :=
begin
  intros s hne hsc, obtain ⟨t, ht₁, ht₂⟩ := h s, clear h,
  cases t.eq_empty_or_nonempty with h h,
  { subst h, rw finset.sup_empty at ht₂, rw ht₂,
    simp [eq_singleton_bot_of_Sup_eq_bot_of_nonempty ht₂ hne], },
  { rw ht₂, exact t.sup_closed_of_sup_closed h ht₁ hsc, },
end

lemma is_sup_closed_compact.well_founded (h : is_sup_closed_compact α) :
  well_founded ((>) : α → α → Prop) :=
begin
  rw rel_embedding.well_founded_iff_no_descending_seq, rintros ⟨a⟩,
  suffices : Sup (set.range a) ∈ set.range a,
  { obtain ⟨n, hn⟩ := set.mem_range.mp this,
    have h' : Sup (set.range a) < a (n+1), { change _ > _, simp [← hn, a.map_rel_iff], },
    apply lt_irrefl (a (n+1)), apply lt_of_le_of_lt _ h', apply le_Sup, apply set.mem_range_self, },
  apply h (set.range a),
  { use a 37, apply set.mem_range_self, },
  { rintros x y ⟨m, hm⟩ ⟨n, hn⟩, use m ⊔ n, rw [← hm, ← hn], apply a.to_rel_hom.map_sup, },
end

lemma is_Sup_finite_compact_iff_all_elements_compact :
  is_Sup_finite_compact α ↔ (∀ k : α, is_compact_element k) :=
begin
  split,
  { intros h k s hs,
    obtain ⟨t, ⟨hts, htsup⟩⟩ := h s,
    use [t, hts],
    rwa ←htsup, },
  { intros h s,
    obtain ⟨t, ⟨hts, htsup⟩⟩ := h (Sup s) s (by refl),
    have : Sup s = t.sup id,
    { suffices : t.sup id ≤ Sup s, by { apply le_antisymm; assumption },
      simp only [id.def, finset.sup_le_iff],
      intros x hx,
      apply le_Sup, exact hts hx, },
    use [t, hts], assumption, },
end

lemma well_founded_characterisations :
  tfae [well_founded ((>) : α → α → Prop),
        is_Sup_finite_compact α,
        is_sup_closed_compact α,
        ∀ k : α, is_compact_element k] :=
begin
  tfae_have : 1 → 2, by { exact well_founded.is_Sup_finite_compact α, },
  tfae_have : 2 → 3, by { exact is_Sup_finite_compact.is_sup_closed_compact α, },
  tfae_have : 3 → 1, by { exact is_sup_closed_compact.well_founded α, },
  tfae_have : 2 ↔ 4, by { exact is_Sup_finite_compact_iff_all_elements_compact α },
  tfae_finish,
end

lemma well_founded_iff_is_Sup_finite_compact :
  well_founded ((>) : α → α → Prop) ↔ is_Sup_finite_compact α :=
(well_founded_characterisations α).out 0 1

lemma is_Sup_finite_compact_iff_is_sup_closed_compact :
  is_Sup_finite_compact α ↔ is_sup_closed_compact α :=
(well_founded_characterisations α).out 1 2

lemma is_sup_closed_compact_iff_well_founded :
  is_sup_closed_compact α ↔ well_founded ((>) : α → α → Prop) :=
(well_founded_characterisations α).out 2 0

alias well_founded_iff_is_Sup_finite_compact ↔ _ is_Sup_finite_compact.well_founded
alias is_Sup_finite_compact_iff_is_sup_closed_compact ↔
      _ is_sup_closed_compact.is_Sup_finite_compact
alias is_sup_closed_compact_iff_well_founded ↔ _ well_founded.is_sup_closed_compact

lemma compactly_generated_of_well_founded (h : well_founded ((>) : α → α → Prop)) :
  is_compactly_generated α :=
begin
  rw [well_founded_iff_is_Sup_finite_compact, is_Sup_finite_compact_iff_all_elements_compact] at h,
  -- x is the join of the set of compact elements {x}
  exact λ x, ⟨{x}, ⟨λ x _, h x, Sup_singleton⟩⟩,
end

end complete_lattice
