/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Measurable spaces -- measures
-/
import data.set order.galois_connection topology.ennreal topology.measurable_space
  algebra.big_operators
noncomputable theory

open classical set lattice finset function
local attribute [instance] decidable_inhabited prop_decidable

lemma supr_bool_eq {α : Type*} [complete_lattice α] {f : bool → α} :
  (⨆b:bool, f b) = f tt ⊔ f ff :=
le_antisymm
  (supr_le $ assume b, match b with tt := le_sup_left | ff := le_sup_right end)
  (sup_le (le_supr _ _) (le_supr _ _))

universes u v w x

namespace measure_theory

structure measure_space (α : Type*) [m : measurable_space α] :=
(measure_of       : Π(s : set α), is_measurable s → ennreal)
(measure_of_empty : measure_of ∅ is_measurable_empty = 0)
(measure_of_Union :
  ∀{f:ℕ → set α}, ∀h : ∀i, is_measurable (f i), pairwise (disjoint on f) →
  measure_of (⋃i, f i) (is_measurable_Union h) = (∑i, measure_of (f i) (h i)))

section
variables {α : Type*} {β : Type*} [measurable_space α] {μ μ₁ μ₂ : measure_space α} {s s₁ s₂ : set α}

def measure_space.measure (μ : measure_space α) (s : set α) : ennreal :=
if h : is_measurable s then μ.measure_of s h else 0

lemma measure_eq_measure_of (h : is_measurable s) :
  μ.measure s = μ.measure_of s h :=
dif_pos h

lemma measure_space_eq_of : ∀{μ₁ μ₂ : measure_space α},
  (∀s, ∀h:is_measurable s, μ₁.measure_of s h = μ₂.measure_of s h) → μ₁ = μ₂
| ⟨m₁, e₁, u₁⟩ ⟨m₂, e₂, u₂⟩ h :=
  have m₁ = m₂, from funext $ assume s, funext $ assume hs, h s hs,
  by simp [this]

lemma measure_space_eq (h : ∀s, is_measurable s → μ₁.measure s = μ₂.measure s) : μ₁ = μ₂ :=
measure_space_eq_of $ assume s hs,
  have μ₁.measure s = μ₂.measure s, from h s hs,
  by simp [measure_eq_measure_of, hs] at this; assumption

@[simp] lemma measure_empty : μ.measure ∅ = 0 :=
by rw [measure_eq_measure_of is_measurable_empty, μ.measure_of_empty]

lemma measure_Union_nat {f : ℕ → set α}
  (hn : pairwise (disjoint on f)) (h : ∀i, is_measurable (f i)) :
  μ.measure (⋃i, f i) = (∑i, μ.measure (f i)) :=
by simp [measure_eq_measure_of, h, is_measurable_Union h, μ.measure_of_Union h hn]

lemma measure_bUnion {i : set β} {s : β → set α} (hi : countable i)
  (hd : pairwise_on i (disjoint on s)) (h : ∀b∈i, is_measurable (s b)) :
  μ.measure (⋃b∈i, s b) = ∑p:{b // b ∈ i}, μ.measure (s p.val) :=
let ⟨f, hf⟩ := hi in
let g : ℕ → set α := λn, ⋃b (h : b ∈ i) (h : f b = n), s b in
have h_gf : ∀b∈i, g (f b) = s b,
  from assume b hb, le_antisymm
    (supr_le $ assume b', supr_le $ assume hb', supr_le $ assume hbn,
      have f b = f b', by simp [hbn],
      have b = b', from hf _ hb _ hb' this,
      by simp [this]; exact le_refl _)
    (le_supr_of_le b $ le_supr_of_le hb $ le_supr_of_le rfl $ le_refl _),
have eq₁ : (⋃b∈i, s b) = (⋃i, g i),
  from le_antisymm
    (bUnion_subset $ assume b hb, show s b ≤ ⨆n (b:β) (h : b ∈ i) (h : f b = n), s b,
      from le_supr_of_le (f b) $ le_supr_of_le b $ le_supr_of_le hb $ le_supr_of_le rfl $ le_refl (s b))
    (supr_le $ assume n, supr_le $ assume b, supr_le $ assume hb, supr_le $ assume hnb,
      subset_bUnion_of_mem hb),
have hd : pairwise (disjoint on g),
  from assume n m h,
  set.eq_empty_of_subset_empty $ calc g n ∩ g m =
      (⋃b (h : b ∈ i) (h : f b = n) b' (h : b' ∈ i) (h : f b' = m), s b ∩ s b') :
        by simp [g, inter_distrib_Union_left, inter_distrib_Union_right]
      ... ⊆ ∅ :
        bUnion_subset $ assume b hb, Union_subset $ assume hbn,
        bUnion_subset $ assume b' hb', Union_subset $ assume hbm,
        have b ≠ b',
          from assume h_eq,
          have f b = f b', from congr_arg f h_eq,
          by simp [hbm, hbn, h] at this; assumption,
        have s b ∩ s b' = ∅,
          from hd b hb b' hb' this,
        by rw [this]; exact subset.refl _,
have hm : ∀n, is_measurable (g n),
  from assume n,
  by_cases
    (assume : ∃b∈i, f b = n, let ⟨b, hb, h_eq⟩ := this in
      have s b = g n, from h_eq ▸ (h_gf b hb).symm,
      this ▸ h b hb)
    (assume : ¬ ∃b∈i, f b = n,
      have g n = ∅, from set.eq_empty_of_subset_empty $
        bUnion_subset $ assume b hb, Union_subset $ assume h_eq, (this ⟨b, hb, h_eq⟩).elim,
      this.symm ▸ is_measurable_empty),
calc μ.measure (⋃b∈i, s b) = μ.measure (⋃i, g i) : by rw [eq₁]
  ... = (∑i, μ.measure (g i)) : measure_Union_nat hd hm
  ... = (∑p:{b // b ∈ i}, μ.measure (s p.val)) : tsum_eq_tsum_of_ne_zero_bij
    (λb h, f b.val)
    (assume ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ _ _ h, subtype.eq $ show b₁ = b₂, from hf b₁ hb₁ b₂ hb₂ h)
    (assume n hn,
      have g n ≠ ∅, from assume h, by simp [h] at hn; assumption,
      have ∃b∈i, f b = n,
        from let ⟨x, hx⟩ := set.exists_mem_of_ne_empty this in
        by simp at hx; exact let ⟨b, h_eq, hb, _⟩ := hx in ⟨b, hb, h_eq⟩,
      let ⟨b, hb, h_eq⟩ := this in
      have g n = s b,
        from h_eq ▸ h_gf b hb,
      ⟨⟨b, hb⟩, by simp [this] at hn; assumption, h_eq⟩)
    (assume ⟨b, hb⟩, by simp [hb, h_gf])

lemma measure_sUnion [encodable β] {s : β → set α}
  (hd : pairwise (disjoint on s)) (h : ∀b, is_measurable (s b)) :
  μ.measure (⋃b, s b) = ∑b, μ.measure (s b) :=
calc μ.measure (⋃b, s b) = μ.measure (⋃b∈(univ:set β), s b) :
    congr_arg μ.measure $ set.ext $ by simp
  ... = ∑p:{b:β // true}, μ.measure (s p.val) :
    measure_bUnion countable_encodable (assume i _ j _, hd i j) (assume b _, h b)
  ... = ∑b, μ.measure (s b) : @tsum_eq_tsum_of_iso _ _ _ _ _ _ _ (λb, μ.measure (s b)) subtype.val
    (λb, ⟨b, trivial⟩ : β → {b:β // true}) (λ⟨b, hb⟩, rfl) (λb, rfl)

lemma measure_union {s₁ s₂ : set α}
  (hd : disjoint s₁ s₂) (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) :
  μ.measure (s₁ ∪ s₂) = μ.measure s₁ + μ.measure s₂ :=
have hd : pairwise (disjoint on λ (b : bool), cond b s₁ s₂),
  from assume i j h,
  match i, j, h with
  | tt, tt, h := (h rfl).elim
  | tt, ff, h := hd
  | ff, tt, h := show s₂ ⊓ s₁ = ⊥, by rw [inf_comm]; assumption
  | ff, ff, h := (h rfl).elim
  end,
calc μ.measure (s₁ ∪ s₂) = μ.measure (⋃b:bool, cond b s₁ s₂) :
    congr_arg μ.measure (@supr_bool_eq _ _ (λb, cond b s₁ s₂)).symm
  ... = (∑b:bool, μ.measure (cond b s₁ s₂)) :
    measure_sUnion hd (assume b, match b with tt := h₁ | ff := h₂ end)
  ... = (insert tt (insert ff ∅) : finset bool).sum (λb:bool, μ.measure (cond b s₁ s₂)) :
    tsum_eq_sum $ assume b, by cases b; simp
  ... = μ.measure s₁ + μ.measure s₂ :
    by simp [sum_insert]

lemma measure_mono {s₁ s₂ : set α} (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) (hs : s₁ ⊆ s₂) :
  μ.measure s₁ ≤ μ.measure s₂ :=
have hd : s₁ ∩ (s₂ \ s₁) = ∅, from set.ext $ by simp [mem_sdiff_iff] {contextual:=tt},
have hu : s₁ ∪ (s₂ \ s₁) = s₂,
  from set.ext $ assume x, by by_cases x ∈ s₁; simp [mem_sdiff_iff, h, @hs x] {contextual:=tt},
calc μ.measure s₁ ≤ μ.measure s₁ + μ.measure (s₂ - s₁) : le_add_of_nonneg_right' ennreal.zero_le
  ... = μ.measure (s₁ ∪ (s₂ - s₁)) : (measure_union hd h₁ (is_measurable_sdiff h₂ h₁)).symm
  ... = μ.measure s₂ : congr_arg _ hu

lemma measure_Union_le_nat {s : ℕ → set α} (h : ∀i, is_measurable (s i)) :
  μ.measure (⋃i, s i) ≤ (∑i, μ.measure (s i)) :=
calc μ.measure (⋃i, s i) = μ.measure (⋃i, disjointed s i) :
  congr_arg _ disjointed_Union.symm
  ... = ∑i, μ.measure (disjointed s i) :
    measure_sUnion disjoint_disjointed $ assume i, is_measurable_disjointed h
  ... ≤ ∑i, μ.measure (s i) :
    ennreal.tsum_le_tsum $ assume i,
      measure_mono (is_measurable_disjointed h) (h i) (inter_subset_left _ _)

end

section constructions
variables {α : Type u} [measurable_space α]

def count : measure_space α :=
{ measure_of := λs hs, ∑x, if x ∈ s then 1 else 0,
  measure_of_empty := by simp,
  measure_of_Union := assume f _ hd,
    begin
      rw [ennreal.tsum_comm],
      congr, apply funext, intro,
      by_cases ∃i, x ∈ f i,
      { have h' : (∑(i : ℕ), ite (x ∈ f i) 1 0 : ennreal) = 1,
          from let ⟨i, hi⟩ := h in
            calc (∑(i : ℕ), ite (x ∈ f i) 1 0 : ennreal) =
              finset.sum {i} (λi, ite (x ∈ f i) 1 0) :
                tsum_eq_sum (assume j hj,
                  have j ≠ i, by simp at hj; assumption,
                  have f j ∩ f i = ∅, from hd j i this,
                  have x ∉ f j,
                    from assume hj,
                    have hx : x ∈ f j ∩ f i, from ⟨hj, hi⟩,
                    by rwa [this] at hx,
                  by simp [this])
              ... = (1 : ennreal) : by simp [hi],
        simp [h, h'] },
      { have h₁ : x ∉ ⋃ (i : ℕ), f i, by simp [h],
        have h₂ : ∀i, x ∉ f i, from assume i hi, h ⟨i, hi⟩,
        simp [h₁, h₂] }
    end }

instance : has_zero (measure_space α) :=
⟨{ measure_of := λs hs, 0, measure_of_empty := rfl, measure_of_Union := by simp }⟩

instance : partial_order (measure_space α) :=
{ partial_order .
  le          := λm₁ m₂, ∀s (hs : is_measurable s), m₁.measure_of s hs ≤ m₂.measure_of s hs,
  le_refl     := assume m s hs, le_refl _,
  le_trans    := assume m₁ m₂ m₃ h₁ h₂ s hs, le_trans (h₁ s hs) (h₂ s hs),
  le_antisymm := assume m₁ m₂ h₁ h₂, measure_space_eq_of $
    assume s hs, le_antisymm (h₁ s hs) (h₂ s hs) }

end constructions

end measure_theory
