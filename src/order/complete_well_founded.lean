/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import order.well_founded
import order.order_iso_nat
import data.set.finite

/-!
# Well-foundedness for complete lattices

For complete lattices, there are numerous equivalent ways to express the fact that the relation `>`
is well-founded. In this file we define two especially-useful characterisations and provide
proofs that they are indeed equivalent to well-foundedness.

## Main definitions
 * `is_sup_closed_compact`
 * `is_Sup_finite_compact`

## Main results
 * `is_sup_closed_compact_iff_is_Sup_finite_compact`
 * `well_founded_iff_is_sup_closed_compact`

## Tags

complete lattice, well-founded, compact
-/

namespace complete_lattice

variables (α : Type*) [complete_lattice α]

/-- A compactness property for a complete lattice is that any `sup`-closed non-empty subset
contains its `Sup`. -/
def is_sup_closed_compact :=
  ∀ (s : set α) (h : s.nonempty), (∀ a b, a ∈ s → b ∈ s → a ⊔ b ∈ s) → (Sup s) ∈ s

/-- A compactness property for a complete lattice is that any subset has a finite subset with the
same `Sup`. -/
def is_Sup_finite_compact := ∀ (s : set α), ∃ (t ⊆ s) (h : t.finite), Sup s = Sup t

lemma is_sup_closed_compact_iff_is_Sup_finite_compact :
  is_sup_closed_compact α ↔ is_Sup_finite_compact α :=
begin
  split; intros h,
  { intros s, change ∃ (t : set α) (H : t ⊆ s) (h : t.finite), has_Sup.Sup s = has_Sup.Sup t,
    by_cases hne : s.nonempty,
    { let s' : set α := { x | ∃ (t ⊆ s), t.finite ∧ x = has_Sup.Sup t },
      have h_Sup : has_Sup.Sup s = has_Sup.Sup s',
      { apply le_antisymm,
        { suffices : s ⊆ s', { exact Sup_le_Sup this, },
          intros x hx,
          use { x }, rw Sup_singleton, simp [hx], },
        { have hs' : ∀ (x ∈ s'), x ≤ Sup s,
          { rintros x ⟨t, h_subset, h_finite, hx⟩, rw hx, exact Sup_le_Sup h_subset, },
          apply Sup_le, exact hs', }, },
      have hs' : ∀ a b, a ∈ s' → b ∈ s' → a ⊔ b ∈ s',
      { rintros a b ⟨t₁, h_subset₁, h_finite₁, ha⟩ ⟨t₂, h_subset₂, h_finite₂, hb⟩,
        use t₁ ∪ t₂,
        refine ⟨set.union_subset h_subset₁ h_subset₂, set.finite.union h_finite₁ h_finite₂, _⟩,
        rw [ha, hb, Sup_union.symm], },
      have hne' : s'.nonempty,
      { let t : set α := { hne.some },
        have ht : t.finite, { exact set.finite_singleton (set.nonempty.some hne), },
        use Sup t, refine ⟨t, _, ht, rfl⟩,
        simp only [set.singleton_subset_iff], apply hne.some_spec, },
      rw h_Sup, obtain ⟨t, ht, h_finite, h_Sup'⟩ := h s' hne' hs',
      use t, split,
      { use ht, },
      { use h_finite, exact h_Sup', }, },
    { use ⊥, split,
      { simp only [set.empty_subset, set.bot_eq_empty], },
      { simp only [set.bot_eq_empty, Sup_empty, Sup_eq_bot, set.finite_empty, exists_prop_of_true],
        intros a ha, exfalso, apply hne, exact ⟨a, ha⟩, }, },  },
  { suffices : ∀ (s : set α), (⊥ ∈ s) → (∀ a b, a ∈ s → b ∈ s → a ⊔ b ∈ s) → (has_Sup.Sup s) ∈ s,
    { intros s hne h_sup,
      have h_sup' : (∀ a b, a ∈ s.insert ⊥ → b ∈ s.insert ⊥ → a ⊔ b ∈ s.insert ⊥),
      { intros a b ha hb,
        have ha' := set.eq_or_mem_of_mem_insert ha,
        have hb' := set.eq_or_mem_of_mem_insert hb,
        rcases ha'; rcases hb',
        { simp only [ha', hb', sup_bot_eq], exact s.mem_insert ⊥, },
        { simp only [ha', hb', bot_sup_eq], exact hb, },
        { simp only [ha', hb', sup_bot_eq], exact ha, },
        { apply set.mem_insert_of_mem ⊥, apply h_sup _ _ ha' hb', }, },
      specialize this (s.insert ⊥) (s.mem_insert ⊥) h_sup',
      have h₁ : has_Sup.Sup (s.insert ⊥) = has_Sup.Sup s,
      { change has_Sup.Sup (insert ⊥ s) = has_Sup.Sup s, simp, }, rw h₁ at this,
      rcases set.eq_or_mem_of_mem_insert this,
      { have h₂ := Sup_eq_bot.mp h_1, change has_Sup.Sup s ∈ s, rw h_1,
        rw ← h₂ hne.some hne.some_spec, apply hne.some_spec, },
      { assumption, }, },
    intros s h_bot h_sup, obtain ⟨t, h_subset, h_finite, h_Sup⟩ := h s, change Sup s ∈ s, rw h_Sup,
    revert h_subset, apply h_finite.induction_on,
    { change _ → has_Sup.Sup ∅ ∈ s, simp [h_bot], },
    { intros x t' h₁ h₂ h₃ h₄, rw set.insert_subset at h₄, change has_Sup.Sup _ ∈ s,
      simp only [Sup_insert], exact h_sup _ _ h₄.1 (h₃ h₄.2), }, },
end

lemma finite_subset_is_bounded {β : Type*} [semilattice_sup_bot β] {s : set β} (h : s.finite) :
  ∃ y, ∀ x ∈ s, x ≤ y :=
begin
  use h.to_finset.sup id,
  intros x hx, exact finset.le_sup (set.finite.mem_to_finset.mpr hx),
end

lemma well_founded_iff_is_sup_closed_compact :
  well_founded ((>) : α → α → Prop) ↔ is_sup_closed_compact α :=
begin
  split; intros h,
  { have : ∀ (s : set α) (a ∈ s) (hs : a < has_Sup.Sup s), ∃ (b ∈ s), a < a ⊔ b,
    { intros, by_contradiction contra,
      have contra' : a ∈ upper_bounds s, { simp [lt_iff_le_and_ne] at contra, exact contra, },
      change a < has_Sup.Sup s at hs,
      refine lt_irrefl a (gt_of_ge_of_gt _ hs), apply Sup_le, exact contra', },
    rw well_founded.well_founded_iff_has_max' at h,
    intros s h₁ h₂,
    obtain ⟨b, hb₁, hb₂⟩ := h s h₁,
    by_cases h : b = Sup s,
    { rw ← h, exact hb₁, },
    { exfalso,
      have h' : b < Sup s, { rw lt_iff_le_and_ne, refine ⟨_, h⟩, apply le_Sup, exact hb₁, },
      obtain ⟨b', hb₁', hb₂'⟩ := this s b hb₁ h',
      specialize hb₂ (b ⊔ b') (h₂ b b' hb₁ hb₁'),
      simp only [forall_prop_of_true, sup_eq_left, le_sup_left] at hb₂,
      have hh : ¬ (b' ≤ b), { rw lt_iff_le_and_ne at hb₂', simp at hb₂', exact hb₂', },
      apply hh, assumption, }, },
  { rw rel_embedding.well_founded_iff_no_descending_seq, rintros ⟨a⟩,
    rw is_sup_closed_compact_iff_is_Sup_finite_compact at h,
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := h (set.range a),
    have hn : ∃ (n : ℕ), Sup t ≤ a n,
    { let s := a ⁻¹' t,
      have hs : s.finite, { apply set.finite.preimage_embedding, assumption, },
      obtain ⟨n, hn⟩ := finite_subset_is_bounded hs,
      have hn' : ∀ m, a m ∈ t → a m ≤ a n,
      { intros m hm, specialize hn m hm, by_cases hmn : m = n,
        { rw hmn, },
        { rw ne.le_iff_lt hmn at hn, change _ > _ at hn, rw a.map_rel_iff at hn,
          exact le_of_lt hn,  }, },
      use n, apply Sup_le, intros x hx,
      have hx' : ∃ m, a m = x, { exact set.mem_range.mp (ht₁ hx), },
      obtain ⟨m, hm⟩ := hx', rw ← hm, apply hn', rw hm, exact hx, },
    obtain ⟨n, hn⟩ := hn, rw ← ht₃ at hn,
    have contra : a (n + 1) ≤ a n, { refine le_trans _ _ _ _ hn, apply le_Sup, use n+1, },
    have contra' : a n < a (n + 1),
    { change a (n + 1) > a n, rw ← a.map_rel_iff,
      simp only [nat.succ_pos', gt_iff_lt, lt_add_iff_pos_right], },
    apply lt_irrefl (a (n+1)), exact gt_of_gt_of_ge contra' contra, },
end

end complete_lattice
