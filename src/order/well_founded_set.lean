/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.set.finite
import data.fintype.basic
import order.well_founded
import order.order_iso_nat

/-!
# Well-founded sets

A well-founded subset of an ordered type is one on which the relation `<` is well-founded.

## Main Definitions
 * `set.well_founded_on s r` indicates that the relation `r` is
  well-founded when restricted to the set `s`.
 * `set.is_wf s` indicates that `<` is well-founded when restricted to `s`.notation

## Main Results
 * `set.well_founded_on_iff` relates `well_founded_on` to the well-foundedness of a relation on the
 original type, to avoid dealing with subtypes.
 * `set.is_wf.mono` shows that a subset of a well-founded subset is well-founded.
 * `set.is_wf.union` shows that the union of two well-founded subsets is well-founded.
 * `finset.is_wf` shows that all `finset`s are well-founded.

-/

variables {α : Type*}

namespace set

/-- `s.well_founded_on r` indicates that the relation `r` is well-founded when restricted to `s`. -/
def well_founded_on (s : set α) (r : α → α → Prop) : Prop :=
well_founded (λ (a : s) (b : s), r a b)

lemma well_founded_on_iff {s : set α} {r : α → α → Prop} :
  s.well_founded_on r ↔ well_founded (λ (a b : α), r a b ∧ a ∈ s ∧ b ∈ s) :=
begin
  have f : rel_embedding (λ (a : s) (b : s), r a b) (λ (a b : α), r a b ∧ a ∈ s ∧ b ∈ s) :=
    ⟨⟨coe, subtype.coe_injective⟩, λ a b, by simp⟩,
  refine ⟨λ h, _, f.well_founded⟩,
  rw well_founded.well_founded_iff_has_min,
  intros t ht,
  by_cases hst : (s ∩ t).nonempty,
  { rw ← subtype.preimage_coe_nonempty at hst,
    rcases well_founded.well_founded_iff_has_min.1 h (coe ⁻¹' t) hst with ⟨⟨m, ms⟩, mt, hm⟩,
    exact ⟨m, mt, λ x xt ⟨xm, xs, ms⟩, hm ⟨x, xs⟩ xt xm⟩ },
  { rcases ht with ⟨m, mt⟩,
    exact ⟨m, mt, λ x xt ⟨xm, xs, ms⟩, hst ⟨m, ⟨ms, mt⟩⟩⟩ }
end

section has_lt
variables [has_lt α]

/-- `s.is_wf` indicates that `<` is well-founded when restricted to `s`. -/
def is_wf (s : set α) : Prop := well_founded_on s (<)

variables {s t : set α}

theorem is_wf.mono (h : is_wf t) (st : s ⊆ t) : is_wf s :=
begin
  rw [is_wf, well_founded_on_iff] at *,
  refine subrelation.wf (λ x y xy, _) h,
  exact ⟨xy.1, st xy.2.1, st xy.2.2⟩,
end
end has_lt

section partial_order
variables [partial_order α] {s t : set α} {a : α}

theorem is_wf_iff_no_descending_seq :
  is_wf s ↔ ∀ (f : (order_dual ℕ) ↪o α), ¬ (range f) ⊆ s :=
begin
  haveI : is_strict_order α (λ (a b : α), a < b ∧ a ∈ s ∧ b ∈ s) := {
    to_is_irrefl := ⟨λ x con, lt_irrefl x con.1⟩,
    to_is_trans := ⟨λ a b c ab bc, ⟨lt_trans ab.1 bc.1, ab.2.1, bc.2.2⟩⟩,
  },
  rw [is_wf, well_founded_on_iff, rel_embedding.well_founded_iff_no_descending_seq],
  refine ⟨λ h f con, h begin
    use f,
      { exact f.injective },
      { intros a b,
        simp only [con (mem_range_self a), con (mem_range_self b), and_true, gt_iff_lt,
          function.embedding.coe_fn_mk, order_embedding.lt_iff_lt],
        refl } end, λ h con, _⟩,
  rcases con with ⟨f, hf⟩,
  have hfs' : ∀ n : ℕ, f n ∈ s := λ n, (hf.2 n.lt_succ_self).2.2,
  refine h ⟨f, λ a b, _⟩ (λ n hn, _),
  { split; intro hle,
    { cases lt_or_eq_of_le hle with hlt heq,
      { exact le_of_lt (hf.1 ⟨hlt, hfs' _, hfs' _⟩) },
      { rw [f.injective heq] } },
    { cases lt_or_eq_of_le hle with hlt heq,
      { exact le_of_lt (hf.2 hlt).1, },
      { rw [heq] } } },
  { rcases set.mem_range.1 hn with ⟨m, hm⟩,
    rw ← hm,
    apply hfs' }
end

theorem is_wf.union (hs : is_wf s) (ht : is_wf t) : is_wf (s ∪ t) :=
begin
  classical,
  rw [is_wf_iff_no_descending_seq] at *,
  rintros f fst,
  have h : infinite (f ⁻¹' s) ∨ infinite (f ⁻¹' t),
  { have h : infinite (univ : set ℕ) := infinite_univ,
    have hpre : f ⁻¹' (s ∪ t) = set.univ,
    { rw [← image_univ, image_subset_iff, univ_subset_iff] at fst,
      exact fst },
    rw preimage_union at hpre,
    rw ← hpre at h,
    rw [infinite, infinite],
    rw infinite at h,
    contrapose! h,
    exact finite.union h.1 h.2, },
  rw [← infinite_coe_iff, ← infinite_coe_iff] at h,
  cases h with inf inf; haveI := inf,
  { apply hs ((nat.order_embedding_of_set (f ⁻¹' s)).dual.trans f),
    change range (function.comp f (nat.order_embedding_of_set (f ⁻¹' s))) ⊆ s,
    rw [range_comp, image_subset_iff],
      simp },
  { apply ht ((nat.order_embedding_of_set (f ⁻¹' t)).dual.trans f),
    change range (function.comp f (nat.order_embedding_of_set (f ⁻¹' t))) ⊆ t,
    rw [range_comp, image_subset_iff],
      simp }
end
end partial_order

end set

@[simp]
theorem finset.is_wf [partial_order α] {f : finset α} : set.is_wf (↑f : set α) :=
fintype.preorder.well_founded

namespace set
variables [partial_order α] {s : set α} {a : α}

theorem finite.is_wf (h : s.finite) : s.is_wf :=
begin
  rw ← h.coe_to_finset,
  exact finset.is_wf,
end

@[simp]
theorem fintype.is_wf [fintype α] : s.is_wf := (finite.of_fintype s).is_wf

@[simp]
theorem is_wf_singleton : is_wf ({a} : set α) :=
by simp [← finset.coe_singleton]

theorem is_wf.insert (hs : is_wf s) : is_wf (insert a s) :=
by { rw ← union_singleton, exact hs.union is_wf_singleton }

end set
