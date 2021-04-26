/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.set.finite
import data.fintype.basic
import order.well_founded
import order.order_iso_nat
import algebra.pointwise

/-!
# Well-founded sets

A well-founded subset of an ordered type is one on which the relation `<` is well-founded.

## Main Definitions
 * `set.well_founded_on s r` indicates that the relation `r` is
  well-founded when restricted to the set `s`.
 * `set.is_wf s` indicates that `<` is well-founded when restricted to `s`.
 * `set.is_pwo s` indicates that any infinite sequence of elements in `s`
  contains an infinite monotone subsequence.

### Definitions for Hahn Series
 * `set.add_antidiagonal s t a` and `set.mul_antidiagonal s t a` are the sets of pairs of elements
  from `s` and `t` that add/multiply to `a`.
 * `finset.add_antidiagonal` and `finset.mul_antidiagonal` are finite versions of
  `set.add_antidiagonal` and `set.mul_antidiagonal` defined when `s` and `t` are well-founded.

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

instance is_strict_order.subset {s : set α} {r : α → α → Prop} [is_strict_order α r] :
  is_strict_order α (λ (a b : α), r a b ∧ a ∈ s ∧ b ∈ s) :=
{ to_is_irrefl := ⟨λ a con, irrefl_of r a con.1 ⟩,
  to_is_trans := ⟨λ a b c ab bc, ⟨trans_of r ab.1 bc.1, ab.2.1, bc.2.2⟩ ⟩ }

theorem well_founded_on_iff_no_descending_seq {s : set α} {r : α → α → Prop} [is_strict_order α r] :
  s.well_founded_on r ↔ ∀ (f : ((>) : ℕ → ℕ → Prop) ↪r r), ¬ (range f) ⊆ s :=
begin
  rw [well_founded_on_iff, rel_embedding.well_founded_iff_no_descending_seq],
  refine ⟨λ h f con, h begin
    use f,
      { exact f.injective },
      { intros a b,
        simp only [con (mem_range_self a), con (mem_range_self b), and_true, gt_iff_lt,
          function.embedding.coe_fn_mk, f.map_rel_iff] }
    end, λ h con, _⟩,
  rcases con with ⟨f, hf⟩,
  have hfs' : ∀ n : ℕ, f n ∈ s := λ n, (hf.2 n.lt_succ_self).2.2,
  refine h ⟨f, λ a b, _⟩ (λ n hn, _),
  { rw ← hf,
    exact ⟨λ h, ⟨h, hfs' _, hfs' _⟩, λ h, h.1⟩ },
  { rcases set.mem_range.1 hn with ⟨m, hm⟩,
    rw ← hm,
    apply hfs' }
end

section has_lt
variables [has_lt α]

/-- `s.is_wf` indicates that `<` is well-founded when restricted to `s`. -/
def is_wf (s : set α) : Prop := well_founded_on s (<)

lemma is_wf_univ_iff : is_wf (univ : set α) ↔ well_founded ((<) : α → α → Prop) :=
by simp [is_wf, well_founded_on_iff]

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
  rw [is_wf, well_founded_on_iff_no_descending_seq],
  exact ⟨λ h f, h f.lt_embedding, λ h f, h (order_embedding.of_strict_mono
    f (λ _ _, f.map_rel_iff.2))⟩,
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

namespace set

/-- A subset is partially well-ordered by a relation `r` when any infinite sequence contains
  two elements where the first is related to the second by `r`. -/
def partially_well_ordered_on (s) (r : α → α → Prop) : Prop :=
  ∀ (f : ℕ → α), range f ⊆ s → ∃ (m n : ℕ), m < n ∧ r (f m) (f n)

/-- A subset of a preorder is partially well-ordered when any infinite sequence contains
  a monotone subsequence of length 2 (or equivalently, an infinite monotone subsequence). -/
def is_pwo [preorder α] (s) : Prop :=
partially_well_ordered_on s ((≤) : α → α → Prop)

theorem partially_well_ordered_on.image_of_monotone {s : set α}
  {r : α → α → Prop} {β : Type*} {r' : β → β → Prop}
  (hs : s.partially_well_ordered_on r) {f : α → β} (hf : ∀ a1 a2 : α, r a1 a2 → r' (f a1) (f a2)) :
  (f '' s).partially_well_ordered_on r' :=
λ g hg, begin
  have h := λ (n : ℕ), ((mem_image _ _ _).1 (hg (mem_range_self n))),
  obtain ⟨m, n, hlt, hmn⟩ := hs (λ n, classical.some (h n)) _,
  { refine ⟨m, n, hlt, _⟩,
    rw [← (classical.some_spec (h m)).2,
      ← (classical.some_spec (h n)).2],
    apply hf _ _ hmn },
  { rintros _ ⟨n, rfl⟩,
    exact (classical.some_spec (h n)).1 }
end

section partial_order
variables {s : set α} {t : set α} {r : α → α → Prop}

theorem partially_well_ordered_on.exists_monotone_subseq [is_refl α r] [is_trans α r]
  (h : s.partially_well_ordered_on r) (f : ℕ → α) (hf : range f ⊆ s) :
  ∃ (g : ℕ ↪o ℕ), ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) :=
begin
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq r f,
  { refine ⟨g, λ m n hle, _⟩,
    obtain hlt | heq := lt_or_eq_of_le hle,
    { exact h1 m n hlt, },
    { rw [heq],
      apply refl_of r } },
  { exfalso,
    obtain ⟨m, n, hlt, hle⟩ := h (f ∘ g) (subset.trans (range_comp_subset_range _ _) hf),
    exact h2 m n hlt hle }
end

theorem partially_well_ordered_on_iff_exists_monotone_subseq [is_refl α r] [is_trans α r] :
  s.partially_well_ordered_on r ↔
    ∀ f : ℕ → α, range f ⊆ s → ∃ (g : ℕ ↪o ℕ), ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) :=
begin
  classical,
  split; intros h f hf,
  { exact h.exists_monotone_subseq f hf },
  { obtain ⟨g, gmon⟩ := h f hf,
    refine ⟨g 0, g 1, g.lt_iff_lt.2 zero_lt_one, gmon _ _ zero_le_one⟩, }
end

lemma partially_well_ordered_on.well_founded_on [is_partial_order α r]
  (h : s.partially_well_ordered_on r) :
  s.well_founded_on (λ a b, r a b ∧ a ≠ b) :=
begin
  haveI : is_strict_order α (λ a b, r a b ∧ a ≠ b) :=
  { to_is_irrefl := ⟨λ a con, con.2 rfl⟩,
    to_is_trans := ⟨λ a b c ab bc, ⟨trans ab.1 bc.1,
      λ ac, ab.2 (antisymm ab.1 (ac.symm ▸ bc.1))⟩⟩ },
  rw well_founded_on_iff_no_descending_seq,
  intros f con,
  obtain ⟨m, n, hlt, hle⟩ := h f con,
  exact (f.map_rel_iff.2 hlt).2 (antisymm hle (f.map_rel_iff.2 hlt).1).symm,
end

variables [partial_order α]

lemma is_pwo.is_wf (h : s.is_pwo) :
  s.is_wf :=
begin
  rw [is_wf],
  convert h.well_founded_on,
  ext x y,
  rw lt_iff_le_and_ne,
end

theorem is_pwo.exists_monotone_subseq
  (h : s.is_pwo) (f : ℕ → α) (hf : range f ⊆ s) :
  ∃ (g : ℕ ↪o ℕ), monotone (f ∘ g) :=
h.exists_monotone_subseq f hf

theorem is_pwo_iff_exists_monotone_subseq :
  s.is_pwo ↔
    ∀ f : ℕ → α, range f ⊆ s → ∃ (g : ℕ ↪o ℕ), monotone (f ∘ g) :=
partially_well_ordered_on_iff_exists_monotone_subseq

lemma is_pwo.prod (hs : s.is_pwo)
  (ht : t.is_pwo) :
  (s.prod t).is_pwo :=
begin
  classical,
  rw is_pwo_iff_exists_monotone_subseq at *,
  intros f hf,
  obtain ⟨g1, h1⟩ := hs (prod.fst ∘ f) _,
  swap,
  { rw [range_comp, image_subset_iff],
    refine subset.trans hf _,
    rintros ⟨x1, x2⟩ hx,
    simp only [mem_preimage, hx.1] },
  obtain ⟨g2, h2⟩ := ht (prod.snd ∘ f ∘ g1) _,
  refine ⟨g2.trans g1, λ m n mn, _⟩,
  swap,
  { rw [range_comp, image_subset_iff],
    refine subset.trans (range_comp_subset_range _ _) (subset.trans hf _),
    rintros ⟨x1, x2⟩ hx,
    simp only [mem_preimage, hx.2] },
  simp only [rel_embedding.coe_trans, function.comp_app],
  exact ⟨h1 (g2.le_iff_le.2 mn), h2 mn⟩,
end

theorem is_pwo.image_of_monotone {β : Type*} [partial_order β]
  (hs : s.is_pwo) {f : α → β} (hf : monotone f) :
  is_pwo (f '' s) :=
hs.image_of_monotone hf

end partial_order

theorem is_wf.is_pwo [linear_order α] {s : set α}
  (hs : s.is_wf) : s.is_pwo :=
λ f hf, begin
  rw [is_wf, well_founded_on_iff] at hs,
  have hrange : (range f).nonempty := ⟨f 0, mem_range_self 0⟩,
  let a := hs.min (range f) hrange,
  obtain ⟨m, hm⟩ := hs.min_mem (range f) hrange,
  refine ⟨m, m.succ, m.lt_succ_self, le_of_not_lt (λ con, _)⟩,
  rw hm at con,
  apply hs.not_lt_min (range f) hrange (mem_range_self m.succ)
    ⟨con, hf (mem_range_self m.succ), hf _⟩,
  rw ← hm,
  apply mem_range_self,
end

theorem is_wf_iff_is_pwo [linear_order α] {s : set α} :
  s.is_wf ↔ s.is_pwo :=
⟨is_wf.is_pwo, is_pwo.is_wf⟩

end set

@[simp]
theorem finset.partially_well_ordered_on {r : α → α → Prop} [is_refl α r] {f : finset α} :
  set.partially_well_ordered_on (↑f : set α) r :=
begin
  intros g hg,
  by_cases hinj : function.injective g,
  { exact (set.infinite_of_injective_forall_mem hinj (set.range_subset_iff.1 hg)
      f.finite_to_set).elim },
  { rw [function.injective] at hinj,
    push_neg at hinj,
    obtain ⟨m, n, gmgn, hne⟩ := hinj,
    cases lt_or_gt_of_ne hne with hlt hlt;
    { refine ⟨_, _, hlt, _⟩,
      rw gmgn,
      exact refl_of r _, } }
end

@[simp]
theorem finset.is_pwo [partial_order α] {f : finset α} :
  set.is_pwo (↑f : set α) :=
finset.partially_well_ordered_on

@[simp]
theorem finset.well_founded_on {r : α → α → Prop} [is_strict_order α r] {f : finset α} :
  set.well_founded_on (↑f : set α) r :=
begin
  rw [set.well_founded_on_iff_no_descending_seq],
  intros g con,
  apply set.infinite_of_injective_forall_mem g.injective (set.range_subset_iff.1 con),
  exact f.finite_to_set,
end

@[simp]
theorem finset.is_wf [partial_order α] {f : finset α} : set.is_wf (↑f : set α) :=
finset.is_pwo.is_wf

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
theorem is_wf_empty : is_wf (∅ : set α) :=
finite_empty.is_wf

@[simp]
theorem is_wf_singleton (a) : is_wf ({a} : set α) :=
(finite_singleton a).is_wf

theorem is_wf.insert (a) (hs : is_wf s) : is_wf (insert a s) :=
by { rw ← union_singleton, exact hs.union (is_wf_singleton a) }

/-- `is_wf.min` returns a minimal element of a nonempty well-founded set. -/
noncomputable def is_wf.min (hs : is_wf s) (hn : s.nonempty) : α :=
hs.min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)

lemma is_wf.min_mem (hs : is_wf s) (hn : s.nonempty) : hs.min hn ∈ s :=
(well_founded.min hs univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)).2

lemma is_wf.not_lt_min (hs : is_wf s) (hn : s.nonempty) (ha : a ∈ s) : ¬ a < hs.min hn :=
hs.not_lt_min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype) (mem_univ (⟨a, ha⟩ : s))

@[simp]
lemma is_wf_min_singleton (a) {hs : is_wf ({a} : set α)} {hn : ({a} : set α).nonempty} :
  hs.min hn = a :=
eq_of_mem_singleton (is_wf.min_mem hs hn)

end set

@[simp]
theorem finset.is_wf_sup {ι : Type*} [partial_order α] (f : finset ι) (g : ι → set α)
  (hf : ∀ i : ι, i ∈ f → (g i).is_wf) : (f.sup g).is_wf :=
begin
  classical,
  revert hf,
  apply f.induction_on,
  { intro h,
    simp, },
  { intros s f sf hf hsf,
    rw finset.sup_insert,
    exact (hsf s (finset.mem_insert_self _ _)).union  (hf (λ s' s'f, hsf _
      (finset.mem_insert_of_mem s'f))) }
end

namespace set
variables [linear_order α] {s t : set α} {a : α}

lemma is_wf.min_le
  (hs : s.is_wf) (hn : s.nonempty) (ha : a ∈ s) : hs.min hn ≤ a :=
le_of_not_lt (hs.not_lt_min hn ha)

lemma is_wf.le_min_iff
  (hs : s.is_wf) (hn : s.nonempty) :
  a ≤ hs.min hn ↔ ∀ b, b ∈ s → a ≤ b :=
⟨λ ha b hb, le_trans ha (hs.min_le hn hb), λ h, h _ (hs.min_mem _)⟩

lemma is_wf.min_le_min_of_subset
  {hs : s.is_wf} {hsn : s.nonempty} {ht : t.is_wf} {htn : t.nonempty} (hst : s ⊆ t) :
  ht.min htn ≤ hs.min hsn :=
(is_wf.le_min_iff _ _).2 (λ b hb, ht.min_le htn (hst hb))

lemma is_wf.min_union (hs : s.is_wf) (hsn : s.nonempty) (ht : t.is_wf) (htn : t.nonempty) :
  (hs.union ht).min (union_nonempty.2 (or.intro_left _ hsn)) = min (hs.min hsn) (ht.min htn) :=
begin
  refine le_antisymm (le_min (is_wf.min_le_min_of_subset (subset_union_left _ _))
      (is_wf.min_le_min_of_subset (subset_union_right _ _))) _,
  rw min_le_iff,
  exact ((mem_union _ _ _).1 ((hs.union ht).min_mem
    (union_nonempty.2 (or.intro_left _ hsn)))).imp (hs.min_le _) (ht.min_le _),
end

end set

namespace set

variables [linear_ordered_cancel_comm_monoid α] {s : set α} {t : set α}

@[to_additive]
theorem is_pwo.mul
  (hs : s.is_pwo) (ht : t.is_pwo) :
  is_pwo (s * t) :=
begin
  rw ← image_mul_prod,
  exact (is_pwo.prod hs ht).image_of_monotone (λ _ _ h, mul_le_mul' h.1 h.2),
end

@[to_additive]
theorem is_wf.mul (hs : s.is_wf) (ht : t.is_wf) : is_wf (s * t) :=
(hs.is_pwo.mul ht.is_pwo).is_wf

@[to_additive]
theorem is_wf.min_mul (hs : s.is_wf) (ht : t.is_wf) (hsn : s.nonempty) (htn : t.nonempty) :
  (hs.mul ht).min (hsn.mul htn) = hs.min hsn * ht.min htn :=
begin
  refine le_antisymm (is_wf.min_le _ _ (mem_mul.2 ⟨_, _, hs.min_mem _, ht.min_mem _, rfl⟩)) _,
  rw is_wf.le_min_iff,
  rintros _ ⟨x, y, hx, hy, rfl⟩,
  exact mul_le_mul' (hs.min_le _ hx) (ht.min_le _ hy),
end

end set

namespace set

/-- `set.mul_antidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
  that multiply to `a`. -/
@[to_additive "`set.add_antidiagonal s t a` is the set of all pairs of an element in `s`
  and an element in `t` that add to `a`."]
def mul_antidiagonal [monoid α] (s t : set α) (a : α) : set (α × α) :=
{ x | x.1 * x.2 = a ∧ x.1 ∈ s ∧ x.2 ∈ t }

namespace mul_antidiagonal

@[simp, to_additive]
lemma mem_mul_antidiagonal [monoid α] {s t : set α} {a : α} {x : α × α} :
  x ∈ mul_antidiagonal s t a ↔ x.1 * x.2 = a ∧ x.1 ∈ s ∧ x.2 ∈ t := iff.refl _

section cancel_comm_monoid
variables [cancel_comm_monoid α] {s t : set α} {a : α}

@[to_additive]
lemma fst_eq_fst_iff_snd_eq_snd {x y : (mul_antidiagonal s t a)} :
  (x : α × α).fst = (y : α × α).fst ↔ (x : α × α).snd = (y : α × α).snd :=
⟨λ h, begin
  have hx := x.2.1,
  rw [subtype.val_eq_coe, h] at hx,
  apply mul_left_cancel (hx.trans y.2.1.symm),
end, λ h, begin
  have hx := x.2.1,
  rw [subtype.val_eq_coe, h] at hx,
  apply mul_right_cancel (hx.trans y.2.1.symm),
end⟩

@[to_additive]
lemma eq_of_fst_eq_fst {x y : (mul_antidiagonal s t a)}
  (h : (x : α × α).fst = (y : α × α).fst) : x = y :=
subtype.ext (prod.ext h (mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd.1 h))

@[to_additive]
lemma eq_of_snd_eq_snd {x y : (mul_antidiagonal s t a)}
  (h : (x : α × α).snd = (y : α × α).snd) : x = y :=
subtype.ext (prod.ext (mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd.2 h) h)

end cancel_comm_monoid

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid α] (s t : set α) (a : α)

@[to_additive]
lemma eq_of_fst_le_fst_of_snd_le_snd {x y : (mul_antidiagonal s t a)}
  (h1 : (x : α × α).fst ≤ (y : α × α).fst) (h2 : (x : α × α).snd ≤ (y : α × α).snd ) :
  x = y :=
begin
  apply eq_of_fst_eq_fst,
  cases eq_or_lt_of_le h1 with heq hlt,
  { exact heq },
  exfalso,
  exact ne_of_lt (mul_lt_mul_of_lt_of_le hlt h2)
    ((mem_mul_antidiagonal.1 x.2).1.trans (mem_mul_antidiagonal.1 y.2).1.symm)
end

variables {s} {t}

@[to_additive]
theorem finite_of_is_pwo (hs : s.is_pwo) (ht : t.is_pwo) (a) :
  (mul_antidiagonal s t a).finite :=
begin
  by_contra h,
  rw [← set.infinite] at h,
  have h1 : (mul_antidiagonal s t a).partially_well_ordered_on (prod.fst ⁻¹'o (≤)),
  { intros f hf,
    refine hs (prod.fst ∘ f) _,
    rw range_comp,
    rintros _ ⟨⟨x, y⟩, hxy, rfl⟩,
    exact (mem_mul_antidiagonal.1 (hf hxy)).2.1 },
  have h2 : (mul_antidiagonal s t a).partially_well_ordered_on (prod.snd ⁻¹'o (≤)),
  { intros f hf,
    refine ht (prod.snd ∘ f) _,
    rw range_comp,
    rintros _ ⟨⟨x, y⟩, hxy, rfl⟩,
    exact (mem_mul_antidiagonal.1 (hf hxy)).2.2 },
  obtain ⟨g, hg⟩ := h1.exists_monotone_subseq (λ x, h.nat_embedding _ x) _,
  swap, { rintro _ ⟨k, rfl⟩,
    exact ((infinite.nat_embedding (s.mul_antidiagonal t a) h) _).2 },
  obtain ⟨m, n, mn, h2'⟩ := h2 (λ x, (h.nat_embedding _) (g x)) _,
  swap, { rintro _ ⟨k, rfl⟩,
    exact ((infinite.nat_embedding (s.mul_antidiagonal t a) h) _).2, },
  apply ne_of_lt mn (g.injective ((h.nat_embedding _).injective _)),
  exact eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ (le_of_lt mn)) h2',
end

end ordered_cancel_comm_monoid

@[to_additive]
theorem finite_of_is_wf [linear_ordered_cancel_comm_monoid α] {s t : set α}
  (hs : s.is_wf) (ht : t.is_wf) (a) :
  (mul_antidiagonal s t a).finite :=
finite_of_is_pwo hs.is_pwo ht.is_pwo a

end mul_antidiagonal
end set

namespace finset

variables [linear_ordered_cancel_comm_monoid α]
variables {s t : set α} (hs : s.is_wf) (ht : t.is_wf) (a : α)

/-- `finset.mul_antidiagonal_of_is_wf hs ht a` is the set of all pairs of an element in
  `s` and an element in `t` that multiply to `a`, but its construction requires proofs
  `hs` and `ht` that `s` and `t` are well-ordered. -/
@[to_additive "`finset.add_antidiagonal_of_is_wf hs ht a` is the set of all pairs of an element in
  `s` and an element in `t` that add to `a`, but its construction requires proofs
  `hs` and `ht` that `s` and `t` are well-ordered."]
noncomputable def mul_antidiagonal : finset (α × α) :=
(set.mul_antidiagonal.finite_of_is_wf hs ht a).to_finset

variables {hs} {ht} {u : set α} {hu : u.is_wf} {a} {x : α × α}

@[simp, to_additive]
lemma mem_mul_antidiagonal :
  x ∈ mul_antidiagonal hs ht a ↔ x.1 * x.2 = a ∧ x.1 ∈ s ∧ x.2 ∈ t :=
by simp [mul_antidiagonal]

@[to_additive]
lemma mul_antidiagonal_mono_left (hus : u ⊆ s) :
  (finset.mul_antidiagonal hu ht a) ⊆ (finset.mul_antidiagonal hs ht a) :=
λ x hx, begin
  rw mem_mul_antidiagonal at *,
  exact ⟨hx.1, hus hx.2.1, hx.2.2⟩,
end

@[to_additive]
lemma mul_antidiagonal_mono_right (hut : u ⊆ t) :
  (finset.mul_antidiagonal hs hu a) ⊆ (finset.mul_antidiagonal hs ht a) :=
λ x hx, begin
  rw mem_mul_antidiagonal at *,
  exact ⟨hx.1, hx.2.1, hut hx.2.2⟩,
end

@[to_additive]
lemma support_mul_antidiagonal_subset_mul :
  { a : α | (mul_antidiagonal hs ht a).nonempty } ⊆ s * t :=
(λ x ⟨⟨a1, a2⟩, ha⟩, begin
  obtain ⟨hmul, h1, h2⟩ := mem_mul_antidiagonal.1 ha,
  exact ⟨a1, a2, h1, h2, hmul⟩,
end)

@[to_additive]
theorem is_wf_support_mul_antidiagonal :
  { a : α | (mul_antidiagonal hs ht a).nonempty }.is_wf :=
(hs.mul ht).mono support_mul_antidiagonal_subset_mul

@[to_additive]
theorem mul_antidiagonal_min_mul_min (hns : s.nonempty) (hnt : t.nonempty) :
  mul_antidiagonal hs ht ((hs.min hns) * (ht.min hnt)) = {(hs.min hns, ht.min hnt)} :=
begin
  ext ⟨a1, a2⟩,
  rw [mem_mul_antidiagonal, finset.mem_singleton, prod.ext_iff],
  split,
  { rintro ⟨hast, has, hat⟩,
    cases eq_or_lt_of_le (hs.min_le hns has) with heq hlt,
    { refine ⟨heq.symm, _⟩,
      rw heq at hast,
      exact mul_left_cancel hast },
    { contrapose hast,
      exact ne_of_gt (mul_lt_mul_of_lt_of_le hlt (ht.min_le hnt hat)) } },
  { rintro ⟨ha1, ha2⟩,
    rw [ha1, ha2],
    exact ⟨rfl, hs.min_mem _, ht.min_mem _⟩ }
end

end finset

lemma well_founded.is_wf [has_lt α] (h : well_founded ((<) : α → α → Prop)) (s : set α) :
  s.is_wf :=
(set.is_wf_univ_iff.2 h).mono (set.subset_univ s)
