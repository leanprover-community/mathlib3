/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import combinatorics.colex
import combinatorics.set_family.basic
import combinatorics.set_family.compression.uv
import combinatorics.set_family.intersecting
import data.finset.fin

/-!
# Kruskal-Katona theorem

The Kruskal-Katona theorem in a few different versions, and an application to
the Erdos-Ko-Rado theorem.

The key results proved here are:

* The basic Kruskal-Katona theorem, expressing that given a set family 𝒜
  consisting of `r`-sets, and 𝒞 an initial segment of the colex order of the
  same size, the shadow of 𝒞 is smaller than the shadow of 𝒜.
  In particular, this shows that the minimum shadow size is achieved by initial
  segments of colex.

theorem kruskal_katona {r : ℕ} {𝒜 𝒞 : finset (finset X)} (h₁ : (𝒜 : set (finset α)).sized r)
  (h₂ : 𝒜.card = 𝒞.card) (h₃ : is_init_seg 𝒞 r) :
  (∂𝒞).card ≤ (∂𝒜).card :=

* A strengthened form, giving the same result under a weaker constraint.

theorem strengthened_kk {r : ℕ} {𝒜 𝒞 : finset (finset X)} (h₁ : (𝒜 : set (finset α)).sized r)
  (h₂ : 𝒞.card ≤ 𝒜.card) (h₃ : is_init_seg 𝒞 r) :
  (∂𝒞).card ≤ (∂𝒜).card :=

* An iterated form, giving that the minimum iterated shadow size is given
  by initial segments of colex.

theorem iterated_kk {r k : ℕ} {𝒜 𝒞 : finset (finset X)} (h₁ : (𝒜 : set (finset α)).sized r)
  (h₂ : 𝒞.card ≤ 𝒜.card) (h₃ : is_init_seg 𝒞 r) :
  (shadow^[k] 𝒞).card ≤ (shadow^[k] 𝒜).card :=

* A special case of iterated_kk which is often more practical to use.

theorem lovasz_form {r k i : ℕ} {𝒜 : finset (finset X)} (hir : i ≤ r)
  (hrk : r ≤ k) (hkn : k ≤ n) (h₁ : (𝒜 : set (finset α)).sized r) (h₂ : choose k r ≤ 𝒜.card) :
  choose k (r-i) ≤ (shadow^[i] 𝒜).card :=

* Erdos-Ko-Rado theorem, giving the upper bound on the size of an intersecting
  family of `r`-sets

theorem EKR {𝒜 : finset (finset X)} {r : ℕ}
  (h₁ : intersecting 𝒜) (h₂ : (𝒜 : set (finset α)).sized r) (h₃ : r ≤ n/2) :
  𝒜.card ≤ choose (n-1) (r-1) :=

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

kruskal-katona, kruskal, katona, shadow, initial segments, intersecting
-/

namespace colex
variables {α : Type*} [linear_order α]

/-- `𝒜` is an initial segment of the colexigraphic order on sets of `r`, and that if `B` is below
`A` in colex where `B` has size `r` and `A` is in `𝒜`, then `B` is also in `𝒜`. In effect, `𝒜` is
downwards closed with respect to colex among sets of size `r`. -/
def is_init_seg [has_lt α] (𝒜 : finset (finset α)) (r : ℕ) : Prop :=
(𝒜 : set (finset α)).sized r ∧
  ∀ ⦃A B : finset α⦄, A ∈ 𝒜 → B.to_colex < A.to_colex ∧ B.card = r → B ∈ 𝒜

/-- Initial segments are nested in some way. In particular, if they're the same size they're equal.
-/
lemma init_seg_total [linear_order α] {𝒜₁ 𝒜₂ : finset (finset α)} (r : ℕ)
  (h₁ : is_init_seg 𝒜₁ r) (h₂ : is_init_seg 𝒜₂ r) :
  𝒜₁ ⊆ 𝒜₂ ∨ 𝒜₂ ⊆ 𝒜₁ :=
begin
  classical,
  rw [←sdiff_eq_empty_iff_subset, ←sdiff_eq_empty_iff_subset],
  by_contra a,
  push_neg at a,
  rw [←nonempty_iff_ne_empty, ←nonempty_iff_ne_empty] at a,
  rcases a with ⟨⟨A, Ah⟩, B, hB⟩,
  rw mem_sdiff at Ah hB,
  obtain lt | eq | gt := trichotomous_of (<) A.to_colex B.to_colex,
  { exact Ah.2 (h₂.2 hB.1 ⟨lt, h₁.1 Ah.1⟩) },
  { rw colex.eq_iff.1 eq at Ah,
    exact hB.2 Ah.1 },
  { exact hB.2 (h₁.2 Ah.1 ⟨gt, h₂.1 hB.1⟩) }
end

end colex

open colex finset nat uv
open_locale finset_family

variable {α : Type*}
variables {n : ℕ}

namespace UV
section

/-- Applying the compression makes the set smaller in colex. This is intuitive since a portion of
the set is being "shifted 'down" as `max U < max V`. -/
lemma compression_reduces_set [linear_order α] {U V : finset α} {hU : U.nonempty} {hV : V.nonempty}
  (A : finset α) (h : max' U hU < max' V hV) (hA : compress U V A ≠ A) :
  (compress U V A).to_colex < A.to_colex :=
begin
  rw [compress, if_pos (ite_ne_right_iff.1 hA).1],
  -- split_ifs with h₁,
  -- { intro h₂,
  --   exact max' V hV },
  -- { any_goals {exfalso, apply h₂, refl},
  --   exact max' V hV },
  -- refine ⟨_, not_mem_sdiff_of_mem_right (max'_mem _ _), h₁.2 (max'_mem _ _)⟩,
  -- intros x hx,
  /-have : x ∉ V := λ z, not_le_of_lt hx (le_max' _ _ _ z),
  have : x ∉ U := λ z, not_le_of_lt hx (trans (le_max' _ _ _ z) (le_of_lt h)),
  simp [‹x ∉ U›, ‹x ∉ V›]-/
  sorry,
end

/-- This measures roughly how compressed the family is. (Note that it does depend on the ordering of
the ground set, unlike Kruskal-Katona itself). -/
def family_measure (𝒜 : finset (finset (fin n))) : ℕ :=
𝒜.sum $ λ A, (image fin.val A).sum (pow 2)

/-- Applying a compression strictly decreases the measure. This helps show that "compress until we
can't any more" is a terminating process. -/
lemma compression_reduces_family {U V : finset (fin n)} {hU : U.nonempty} {hV : V.nonempty}
  (h : max' U hU < max' V hV)
  {𝒜 : finset (finset (fin n))} (a : 𝓒 U V 𝒜 ≠ 𝒜) :
  family_measure (𝓒 U V 𝒜) < family_measure 𝒜 :=
begin
  rw compression at ⊢ a,
  have q : ∀ Q ∈ filter (λ A, compress U V A ∉ 𝒜) 𝒜, compress U V Q ≠ Q,
    intros Q HQ, rw mem_filter at HQ, intro z, rw z at HQ, exact HQ.2 HQ.1,
  set CA₁ := filter (λ A, compress U V A ∈ 𝒜) 𝒜,
  have uA: CA₁ ∪ filter (λ A, compress U V A ∉ 𝒜) 𝒜 = 𝒜 :=
    filter_union_filter_neg_eq _ _,
  have ne₂ : finset.nonempty (filter (λ A, compress U V A ∉ 𝒜) 𝒜),
  { rw nonempty_iff_ne_empty,
    refine λ z, a _,
    rw image_filter,
    dsimp,
    change _ ∪ image _ (𝒜.filter $ λ A, compress U V A ∉ 𝒜) = _,
    rw [z, image_empty, empty_union],
    rw [z, union_empty] at uA,
    exact a uA },
  rw [family_measure, family_measure, sum_union (compress_disjoint U V)],
  conv_rhs {rw ←uA},
    rw [sum_union, add_comm, add_lt_add_iff_left, sum_image],
      apply sum_lt_sum_of_nonempty ne₂,
      intros A hA,
      -- rw [colex.sum_two_pow_le_iff_colex_le, colex_hom_fin],
      sorry, sorry,
      /-apply compression_reduces_set A h (q _ hA),
    intros x Hx y Hy k, have cx := q x Hx, have cy := q y Hy,
    rw compress at k cx, split_ifs at k cx,
      rw compress at k cy, split_ifs at k cy,
        exact inj_ish h_1 h_2 k,
      exfalso, apply cy rfl,
    exfalso, apply cx rfl,-/
  rw disjoint_iff_inter_eq_empty,
  apply filter_inter_filter_neg_eq
end

/-- These are the compressions which we will apply to decrease the "measure" of a family of sets.-/
def useful_compression [linear_order α] (U V : finset α) : Prop :=
disjoint U V ∧ U.card = V.card ∧ ∃ (HU : U.nonempty), ∃ (HV : V.nonempty), max' U HU < max' V HV

/-- Applying a good compression will decrease measure, keep cardinality, keep sizes and decrease
shadow. In particular, 'good' means it's useful, and every smaller compression won't make a
difference. -/
lemma compression_improved [linear_order α] (U V : finset α)
  (𝒜 : finset (finset α)) (h₁ : useful_compression U V)
  (h₂ : ∀ ⦃U₁ V₁⦄, useful_compression U₁ V₁ ∧ U₁.card < U.card → is_compressed U₁ V₁ 𝒜) :
  (∂ (𝓒 U V 𝒜)).card ≤ (∂𝒜).card :=
begin
  obtain ⟨UVd, same_size, hU, hV, max_lt⟩ := h₁,
  refine card_shadow_compression_le _ _ (λ x Hx, ⟨min' V hV, min'_mem _ _, _⟩),
  obtain hU' | hU' := eq_or_lt_of_le (succ_le_iff.2 hU.card_pos),
  { rw ←hU' at same_size,
    have : erase U x = ∅,
    { rw [←finset.card_eq_zero, card_erase_of_mem Hx, ←hU'] },
    have : erase V (min' V hV) = ∅,
    { rw [←finset.card_eq_zero, card_erase_of_mem (min'_mem _ _), ←same_size] },
    rw [‹erase U x = ∅›, ‹erase V (min' V hV) = ∅›],
    exact is_compressed_self _ _ },
  refine h₂ ⟨⟨UVd.mono (erase_subset _ _) (erase_subset _ _), _, _, _, _⟩, card_erase_lt_of_mem Hx⟩,
  { rw [card_erase_of_mem (min'_mem _ _), card_erase_of_mem Hx, same_size] },
  { rwa [←card_pos, card_erase_of_mem Hx, tsub_pos_iff_lt] },
  { rwa [←finset.card_pos, card_erase_of_mem (min'_mem _ _), ←same_size, tsub_pos_iff_lt] },
  { sorry
    -- refine (finset.max'_subset _ $ erase_subset _ _).trans_lt _,

    -- refine lt_of_le_of_lt (max'_le (erase U x) _ _
    --                               (λ y hy, le_max' U y (mem_of_mem_erase hy))) _,
    -- apply lt_of_lt_of_le max_lt (le_max' _ _ _ _),
    -- rw mem_erase, refine ⟨ne_of_gt _, max'_mem _ _⟩,
    --   apply min'_lt_max'_of_card,
    -- rwa ←same_size
  }
end

instance [decidable_eq α] (s : finset α) : decidable (s.nonempty) :=
by { rw nonempty_iff_ne_empty, apply_instance }

instance thing2 [linear_order α] (U V : finset α) : decidable (useful_compression U V) :=
by { rw useful_compression, apply_instance }

/-- The main Kruskal-Katona helper: use induction with our measure to keep compressing until
we can't any more, which gives a set family which is fully compressed and has the nice properties we
want. -/
lemma kruskal_katona_helper {r : ℕ} (𝒜 : finset (finset (fin n)))
  (h : (𝒜 : set (finset (fin n))).sized r) :
  ∃ (ℬ : finset (finset (fin n))),
    (∂ℬ).card ≤ (∂𝒜).card ∧ 𝒜.card = ℬ.card ∧ (ℬ  : set (finset (fin n))).sized r
  ∧ (∀ U V, useful_compression U V → is_compressed U V ℬ) :=
begin
  classical,
  revert h, apply well_founded.recursion (measure_wf family_measure) 𝒜,
  intros A ih h,
  -- Are there any compressions we can make now?
  set usable : finset (finset (fin n) × finset (fin n)) :=
    univ.filter (λ t, useful_compression t.1 t.2 ∧ ¬ is_compressed t.1 t.2 A),
  -- No. Then where we are is the required set family.
  obtain husable | husable := usable.eq_empty_or_nonempty,
  { refine ⟨A, le_rfl, rfl, h, λ U V hUV, _⟩,
    rw eq_empty_iff_forall_not_mem at husable,
    by_contra,
    exact husable ⟨U, V⟩ (mem_filter.2 ⟨mem_univ _, hUV, h⟩) },
  -- Yes. Then apply the compression, then keep going
  obtain ⟨⟨U, V⟩, uvh, t⟩ := exists_min_image usable (λ t, t.1.card) husable,
  rw mem_filter at uvh,
  have h₂ : ∀ U₁ V₁, useful_compression U₁ V₁ → U₁.card < U.card → is_compressed U₁ V₁ A,
  { rintro U₁ V₁ huseful hUcard,
    by_contra,
    exact hUcard.not_le (t ⟨U₁, V₁⟩ $ mem_filter.2 ⟨mem_univ _, huseful, h⟩) },
  have p1 : (∂(𝓒 U V A)).card ≤ (∂A).card,
  refine card_shadow_compression_le _ _ _,
  sorry
  --   compression_improved _ _ _ uvh.2.1 h₂,
  -- rcases uvh.2.1 with ⟨_, _, _, same_size, max_lt⟩,
  -- rw [measure, inv_image] at ih,
  -- rcases ih (𝓒 U V A) _ _ with ⟨B, q1, q2, q3, q4⟩,
  -- { exact ⟨B, trans q1 p1, trans (compressed_size _ _).symm q2, q3, q4⟩ },
  -- { apply compression_reduces_family max_lt uvh.2.2 },
  -- { apply 𝓒_sized same_size h }
end

/-- If we're compressed by all useful compressions, then we're an initial segment. This is the other
key Kruskal-Katona part. -/
lemma init_seg_of_compressed [linear_order α]
  {ℬ : finset (finset α)} {r : ℕ} (h₁ : (ℬ  : set (finset α)).sized r)
  (h₂ : ∀ U V, useful_compression U V → is_compressed U V ℬ):
  is_init_seg ℬ r :=
begin
  refine ⟨h₁, _⟩,
  rintro A B hA ⟨hBA, sizeA⟩,
  by_contra hB,
  have hAB : A ≠ B := ne_of_mem_of_not_mem hA hB,
  have hAB' : A.card = B.card := (h₁ hA).trans sizeA.symm,
  have hU : (A \ B).nonempty,
  { exact sdiff_nonempty.2 (λ h, hAB $ eq_of_subset_of_card_le h hAB'.ge ) },
  have hV : (B \ A).nonempty,
  { exact sdiff_nonempty.2 (λ h, hAB.symm $ eq_of_subset_of_card_le h hAB'.le ) },
  have disj : disjoint (B \ A) (A \ B),
  { exact disjoint_sdiff.mono_left (sdiff_subset _ _) },
  have smaller : max' _ hV < max' _ hU,
  { obtain lt | eq | gt := lt_trichotomy (max' _ hU) (max' _ hV),
    { have h := compression_reduces_set B lt,
      rw compress_sdiff_sdiff at h,
      exact (hBA.not_lt $ h hAB).elim },
    { exact (disjoint_right.1 disj (max'_mem _ hU) $ eq.symm ▸ max'_mem _ _).elim },
    { assumption } },
  have : useful_compression (B \ A) (A \ B),
  { refine ⟨disj, _, hV, hU, smaller⟩,
    have : (A \ B ∪ A ∩ B).card = (B \ A ∪ B ∩ A).card,
      rwa [sdiff_union_inter, sdiff_union_inter],
    rwa [card_disjoint_union (disjoint_sdiff_inter _ _),
        card_disjoint_union (disjoint_sdiff_inter _ _), inter_comm, add_left_inj,
        eq_comm] at this },
  refine hB _,
  rw ←(h₂ _ _ this).eq,
  exact mem_compression.2 (or.inr ⟨hB, A, hA, compress_sdiff_sdiff _ _⟩),
end

-- These currently aren't used but I think they could be
-- They give initial segments of colex with α = ℕ, in a different way to
-- everything_up_to below.
-- Kruskal-Katona could also in theory work with these

-- def all_under (A : finset ℕ) : finset (finset ℕ) :=
-- A.sup (λ k, filter (λ B, card A = card B)
--                     (image (λ B, B ∪ A.filter (λ x, x > k)) (powerset (range k))))
-- def all_up_to (A : finset ℕ) : finset (finset ℕ) :=
--   all_under A ∪ finset.singleton A

-- lemma mem_all_under (A B : finset ℕ) : B ∈ all_under A ↔ card A = card B ∧ B <ᶜ A :=
-- begin
  -- simp [all_under, colex_lt],
  -- split,
  --   rintro ⟨k, kinA, ⟨lows, lows_small, rfl⟩, cards⟩,
  --   refine ⟨cards, k, _, _, kinA⟩,
  --   intros x hx,
  --   simp [hx],
  --     convert false_or _,
  --     simp only [eq_iff_iff, iff_false],
  --     intro,
  --     apply not_lt_of_gt hx,
  --     rw ←mem_range, apply lows_small a,
  --   simp [kinA, not_or_distrib, le_refl],
  --   intro,
  --   have := lows_small a,
  --   apply not_mem_range_self this,
  -- rintro ⟨cards, k, z, knotinB, kinA⟩,
  -- refine ⟨k, kinA, ⟨filter (λ x, x < k) B, _, _⟩, cards⟩,
  -- intro,
  -- simp,
  -- ext,
  -- simp,
  -- split,
  --   rintro (⟨a1l, a1r⟩ | ⟨a2l, a2r⟩),
  --   rwa z a1r,
  --   exact a2l,
  -- intro,
  -- rcases (lt_or_gt_of_ne (ne_of_mem_of_not_mem a_1 knotinB)),
  --   right,
  --   exact ⟨‹_›, h⟩,
  -- left,
  -- rw ←z h,
  -- exact ⟨a_1, h⟩
-- end

-- lemma mem_all_up_to (A B : finset ℕ) : B ∈ all_up_to A ↔ (card A = card B ∧ B <ᶜ A) ∨ B = A :=
-- by simp [all_up_to, mem_all_under]; tauto

variables [fintype α] [linear_order α]

/-- Gives all sets up to `A` with the same size as it: this is equivalent to
being an initial segment of colex. -/
def everything_up_to (A : finset α) : finset (finset α) :=
univ.filter (λ (B : finset α), A.card = B.card ∧ B.to_colex ≤ A.to_colex)

/-- `B` is in up to `A` if it's the same size, and is lower than `A` -/
lemma mem_everything_up_to {A B : finset α} :
  B ∈ everything_up_to A ↔ A.card = B.card ∧ B.to_colex ≤ A.to_colex :=
begin
  rw [everything_up_to, mem_filter],
  simp only [true_and, iff_self, mem_univ],
end

/-- Being a nonempty initial segment of colex if equivalent to being an `everything_up_to`. -/
lemma IS_iff_le_max (𝒜 : finset (finset α)) (r : ℕ) :
  𝒜.nonempty ∧ is_init_seg 𝒜 r ↔
  ∃ (A : finset α), A ∈ 𝒜 ∧ A.card = r ∧ 𝒜 = everything_up_to A :=
begin
  rw is_init_seg, split,
  { rintro ⟨ne, layer, IS⟩,
    have Ah := @max'_mem (colex α) _ 𝒜 ne,
    refine ⟨@max' (colex α) _ 𝒜 ne, Ah, layer Ah, _⟩,
    ext B,
    rw mem_everything_up_to,
    refine ⟨λ p, _, _⟩,
    { rw [layer p, layer Ah],
      refine ⟨rfl, le_max' _ _ p⟩ },
    rintro ⟨cards, le⟩,
    obtain p | p := le.eq_or_lt,
    { rw colex.eq_iff.1 p,
      exact Ah },
    { exact IS Ah ⟨p, cards ▸ layer Ah⟩ } },
  { rintro ⟨A, Ah, Ac, rfl⟩,
    refine ⟨⟨_, Ah⟩, λ B hB, (mem_everything_up_to.1 hB).1.symm.trans Ac,
      λ B₁ B₂ hB₁ hB₂, mem_everything_up_to.2 ⟨_, _⟩⟩,
    { rwa hB₂.2 },
    { rw mem_everything_up_to at hB₁,
      exact hB₂.1.le.trans hB₁.2 } }
end

/-- `everything_up_to` is automatically an initial segment. -/
lemma up_to_is_IS {A : finset α} {r : ℕ} (h₁ : A.card = r) :
  is_init_seg (everything_up_to A) r :=
and.right $ (IS_iff_le_max _ _).2
  (by refine ⟨A, _, h₁, rfl⟩; simp [mem_everything_up_to, @refl_of (colex α)])

/-- This is important for iterating Kruskal-Katona: the shadow of an `everything_up_to`
is also an `everything_up_to`. This is useful in particular for the next lemma. -/
lemma shadow_of_everything_up_to (A : finset α) (hA : A.nonempty) :
  ∂ (everything_up_to A) = everything_up_to (erase A (min' A hA)) :=
begin
  -- This is a pretty painful proof, with lots of cases.
  ext B,
  simp [mem_shadow_iff_insert_mem, mem_everything_up_to],
  split,
    -- First show that if B ∪ i ≤ A, then B ≤ A - min A
    rintro ⟨i, ih, p, t⟩,
    rw [card_insert_of_not_mem ih] at p,
    have cards : (erase A (min' A hA)).card = B.card,
      rw [card_erase_of_mem (min'_mem _ _), p], refl,
    rcases t with ⟨k, z, _, _⟩ | h, -- cases on B ∪ i = A or B ∪ i < A
    { simp [cards],
      have : k ≠ i,
      rintro rfl,
      exact ‹k ∉ insert k B› (mem_insert_self _ _),
      -- B ∪ i < A, with k as the colex witness. Cases on k < i or k > i.
      cases this.lt_or_lt,
      { left, refine ⟨i, λ x hx, _, ih, _⟩,
        -- When k < i, then i works as the colex witness to show B < A - min A
        { refine ⟨λ p, mem_erase_of_ne_of_mem (((min'_le _ _ ‹_›).trans_lt h).trans hx).ne'
            ((z $ h.trans hx).1 (mem_insert_of_mem p)), λ p, _⟩,
          refine mem_of_mem_insert_of_ne ((z (h.trans hx)).2 _) hx.ne',
          apply mem_of_mem_erase p },
        apply mem_erase_of_ne_of_mem, apply ne_of_gt (lt_of_le_of_lt _ h),
        apply min'_le,
        assumption,
        exact (z h).1 (mem_insert_self _ _) },
      { obtain h₁ | h₁ := (min'_le _ _ ‹k ∈ A›).lt_or_eq,
        -- When k > i, cases on min A < k or min A = k
          -- If min A < k, k works as the colex witness for B < A - min A
          left,
          refine ⟨k, λ x hx, _, ‹k ∉ insert i B› ∘ mem_insert_of_mem,
                        mem_erase_of_ne_of_mem (ne_of_gt h₁) ‹_›⟩,
          simp [(h.trans hx).ne'],
          rw ←z hx,
          rw mem_insert,
          simp [(h.trans hx).ne'],
        -- If k = min A, then B = A - min A
        right,
        symmetry,
        apply eq_of_subset_of_card_le _ (ge_of_eq cards),
        intros t ht,
        rw [mem_erase] at ht,
        have : t ≠ i := ne_of_gt (lt_of_lt_of_le h (min'_le _ _ _ ht.2)),
        rw ←z _ at ht,
        apply mem_of_mem_insert_of_ne ht.2 ‹t ≠ i›,
        apply lt_of_le_of_ne (min'_le _ _ _ ht.2),
        exact ht.1.symm } },
    { refine ⟨cards, _⟩, -- Here B ∪ i = A, do cases on i = min A or not
      by_cases q: (i = min' A hA),
        right,
        rw ←q,
        rw ←h,
        rw erase_insert ih,
      left,
      refine ⟨i, λ x hx, _, ih, mem_erase_of_ne_of_mem q (h ▸ mem_insert_self _ _)⟩,
      rw mem_erase,
      split,
        intro,
        split,
          apply ne_of_gt (lt_of_le_of_lt _ hx),
          apply min'_le, rw ←h, apply mem_insert_self,
        rw ←h, apply mem_insert_of_mem a, rintro ⟨a, b⟩, rw ←h at b,
        apply mem_of_mem_insert_of_ne b (ne_of_gt hx) },
  -- Now show that if B ≤ A - min A, there is j such that B ∪ j ≤ A
  -- We choose j as the smallest thing not in B
  rintro ⟨cards', ⟨k, z, _, _⟩ | rfl⟩,
    have notB: (univ \ B).nonempty,
      refine ⟨k, mem_sdiff.2 ⟨complete _, ‹k ∉ B›⟩⟩,
    set j := min' (univ \ B) notB,
    -- Assume first B < A - min A, and take k as the colex witness for this
    have r: j ≤ k := min'_le _ _ _ _,
    have : j ∉ B, have : j ∈ univ \ B := min'_mem _ _,
      rw mem_sdiff at this, exact this.2,
    have cards: card A = card (insert j B),
    { rw [card_insert_of_not_mem ‹j ∉ B›, ←‹_ = card B›, card_erase_of_mem (min'_mem _ _)],
      apply nat.pos_of_ne_zero,
      rwa [ne, card_eq_zero, ←ne, ←nonempty_iff_ne_empty] },
    refine ⟨j, ‹_›, cards, _⟩,
    rcases lt_or_eq_of_le r with r | r₁, -- cases on j < k or j = k
      -- if j < k, k is our colex witness for B ∪ j < A
      left, refine ⟨k, _, mt (λ t, mem_of_mem_insert_of_ne t (ne_of_gt r)) ‹k ∉ B›,
                    mem_of_mem_erase ‹_›⟩, intros x hx,
      rw mem_insert, rw z hx, simp [ne_of_gt (trans hx r),
      ne_of_gt (lt_of_le_of_lt (min'_le _ _ _ (mem_of_mem_erase ‹_›)) hx)],
    -- if j = k, all of range k is in B so by sizes B ∪ j = A
    right, symmetry, apply eq_of_subset_of_card_le, intros t th,
    rcases lt_trichotomy k t with lt | rfl | gt,
    { apply mem_insert_of_mem, rw z lt, apply mem_erase_of_ne_of_mem _ th,
      apply ne_of_gt (lt_of_le_of_lt _ lt),
      apply min'_le _ _ _ (mem_of_mem_erase ‹_›) },
    { rw r₁, apply mem_insert_self },
    { apply mem_insert_of_mem, rw ←r₁ at gt, by_contra,
      apply not_lt_of_le (min'_le (univ \ B) _ t _) gt, rw mem_sdiff,
      exact ⟨complete _, a⟩ },
    apply ge_of_eq cards, rw mem_sdiff, exact ⟨complete _, ‹_›⟩,
  -- If B = A - min A, then use j = min A so B ∪ j = A
  refine ⟨min' A hA, not_mem_erase _ _, _⟩,
  rw insert_erase (min'_mem _ _), exact ⟨rfl, refl _⟩
end

/-- The shadow of an initial segment is also an initial segment. -/
lemma shadow_of_IS {𝒜 : finset (finset α)} (r : ℕ) (h₁ : is_init_seg 𝒜 r) :
  is_init_seg (∂𝒜) (r - 1) :=
begin
  rcases nat.eq_zero_or_pos r with rfl | hr,
    have : 𝒜 ⊆ {∅},
    { intros A hA,
      rw [mem_singleton, ←finset.card_eq_zero],
      exact h₁.1 hA },
    have := shadow_monotone this,
    simp only [shadow, subset_empty, sup_singleton, image_empty] at this,
    simp [shadow, this, is_init_seg, set.sized],
  obtain rfl | h𝒜 := 𝒜.eq_empty_or_nonempty,
  { rw sup_empty, simp },
  replace h₁ := and.intro h𝒜 h₁, rw IS_iff_le_max at h₁,
  rcases h₁ with ⟨B, _, hB, rfl⟩,
  rw shadow_of_everything_up_to,
  { apply up_to_is_IS,
    rw card_erase_of_mem (min'_mem _ _),
    refl },
  { rwa ←finset.card_pos }
end

end
end UV

local notation `X` := fin n
-- Finally we can prove Kruskal-Katona.
section KK

/-- The Kruskal-Katona theorem. It says that given a set family `𝒜` consisting of `r`-sets, and `𝒞`
an initial segment of the colex order of the same size, the shadow of `𝒞` is smaller than the shadow
of `𝒜`. In particular, this gives that the minimum shadow size is achieved by initial segments of
colex.

Proof notes: Most of the work was done in Kruskal-Katona helper; it gives a `ℬ` which is fully
compressed, and so we know it's an initial segment, which by uniqueness is the same as `𝒞`. -/
theorem kruskal_katona {r : ℕ} {𝒜 𝒞 : finset (finset X)} (h₁ : (𝒜 : set (finset (fin n))).sized r)
  (h₂ : 𝒜.card = 𝒞.card) (h₃ : is_init_seg 𝒞 r) :
  (∂𝒞).card ≤ (∂𝒜).card :=
begin
  rcases UV.kruskal_katona_helper 𝒜 h₁ with ⟨ℬ, card_le, t, layerB, fully_comp⟩,
  have : is_init_seg ℬ r := UV.init_seg_of_compressed layerB fully_comp,
  convert card_le,
  have z: card ℬ = card 𝒞 := t.symm.trans h₂,
  cases init_seg_total r this h₃ with BC CB,
    symmetry, apply eq_of_subset_of_card_le BC (ge_of_eq z),
  apply eq_of_subset_of_card_le CB (le_of_eq z)
end

/--  We can strengthen Kruskal-Katona slightly: note the middle and has been relaxed to a `≤`.
This shows that the minimum possible shadow size is attained by initial segments. -/
theorem strengthened_kk {r : ℕ} {𝒜 𝒞 : finset (finset X)} (h₁ : (𝒜 : set (finset (fin n))).sized r)
  (h₂ : 𝒞.card ≤ 𝒜.card) (h₃ : is_init_seg 𝒞 r) :
  (∂𝒞).card ≤ (∂𝒜).card :=
begin
  rcases exists_smaller_set 𝒜 𝒞.card h₂ with ⟨𝒜', prop, size⟩,
  refine (kruskal_katona (λ A hA, h₁ (prop hA)) size h₃).trans (card_le_of_subset _),
  rw [shadow, shadow],
  apply shadow_monotone prop
end

/--An iterated form of the Kruskal-Katona theorem. In particular, the minimum possible iterated
shadow size is attained by initial segments. -/
theorem iterated_kk {r k : ℕ} {𝒜 𝒞 : finset (finset X)} (h₁ : (𝒜 : set (finset (fin n))).sized r)
  (h₂ : 𝒞.card ≤ 𝒜.card) (h₃ : is_init_seg 𝒞 r) :
  (shadow^[k] 𝒞).card ≤ (shadow^[k] 𝒜).card :=
begin
  induction k generalizing r 𝒜 𝒞, simpa,
  exact k_ih h₁.shadow (strengthened_kk h₁ h₂ h₃) (UV.shadow_of_IS _ h₃),
end

/-- A special case of Kruskal-Katona which is sometimes easier to work with.
If `|𝒜| ≥ k choose r`, (and everything in `𝒜` has size `r`) then the initial segment we compare to
is just all the subsets of `{0, ..., k - 1}` of size `r`. The `i`-th iterated shadow of this is all
the subsets of `{0, ..., k - 1}` of size `r - i`, so the `i`-th iterated shadow of `𝒜` has at least
`k.choose (r - i)` elements. -/
theorem lovasz_form {r k i : ℕ} {𝒜 : finset (finset X)} (hir : i ≤ r)
  (hrk : r ≤ k) (hkn : k ≤ n) (h₁ : (𝒜 : set (finset X)).sized r) (h₂ : choose k r ≤ 𝒜.card) :
  choose k (r-i) ≤ (shadow^[i] 𝒜).card :=
begin
  set range'k : finset X := attach_fin (range k)
    (λ m, by rw mem_range; apply forall_lt_iff_le.2 hkn),
  set 𝒞 : finset (finset X) := powerset_len r range'k,
  have Ccard : 𝒞.card = nat.choose k r,
    rw [card_powerset_len, card_attach_fin, card_range],
  have : (𝒞 : set (finset X)).sized r,
  { intros A HA,
    rw [mem_coe, mem_powerset_len] at HA,
    exact HA.2 },
  suffices this : (shadow^[i] 𝒞).card = nat.choose k (r-i),
  { rw ←this,
    apply iterated_kk h₁ _ _,
    rwa Ccard,
    refine ⟨‹_›, _⟩,
    rintros A B hA ⟨HB₁, HB₂⟩,
    rw mem_powerset_len,
    refine ⟨_, ‹_›⟩,
    intros t th,
    rw [mem_attach_fin, mem_range],
    have : (image coe B).to_colex < (image coe A).to_colex,
    { rwa colex.hom_fin_lt_iff },
    apply colex.forall_lt_of_colex_lt_of_forall_lt k this _ t.val _,
      intros x hx,
      rw mem_image at hx,
      rw mem_powerset_len at hA,
      rcases hx with ⟨a, ha, q⟩,
      rw [←q, ←mem_range],
      have := hA.1 ha,
      rwa mem_attach_fin at this,
    rw mem_image,
    exact ⟨t, th, rfl⟩ },
  suffices : (shadow^[i] 𝒞) = powerset_len (r-i) range'k,
  { rw [this, card_powerset_len, card_attach_fin, card_range] },
  ext B,
  rw [mem_powerset_len, sub_iff_shadow_iter],
  split,
  { rintro ⟨A, Ah, BsubA, card_sdiff_i⟩,
    rw mem_powerset_len at Ah,
    refine ⟨subset.trans BsubA Ah.1, _⟩,
    symmetry,
    rw [nat.sub_eq_iff_eq_add hir, ←Ah.2, ←card_sdiff_i,
        ←card_disjoint_union disjoint_sdiff,
        union_sdiff_of_subset BsubA] },
  rintro ⟨hBk, hB⟩,
  rcases exists_intermediate_set i _ hBk with ⟨C, BsubC, Csubrange, cards⟩,
  rw [hB, ←nat.add_sub_assoc hir, nat.add_sub_cancel_left] at cards,
  refine ⟨C, _, BsubC, _⟩, rw mem_powerset_len, exact ⟨Csubrange, cards⟩,
  rw [card_sdiff BsubC, cards, hB, nat.sub_sub_self hir],
  { rwa [hB, card_attach_fin, card_range, ←nat.add_sub_assoc hir, nat.add_sub_cancel_left] }
end

end KK

/-- The **Erdős–Ko–Rado theorem**: The maximum size of an intersecting family in `α` where all sets
have size `r` is bounded by `(card α - 1).choose (r - 1)`. This bound is sharp. -/
theorem EKR {𝒜 : finset (finset X)} {r : ℕ} (h𝒜 : set.intersecting (𝒜 : set (finset X)))
  (h₂ : (𝒜 : set (finset X)).sized r) (h₃ : r ≤ n/2) :
  𝒜.card ≤ choose (n-1) (r-1) :=
begin
  -- Take care of the r=0 case first: it's not very interesting.
  cases nat.eq_zero_or_pos r with b h1r,
  { convert nat.zero_le _,
    rw [finset.card_eq_zero, eq_empty_iff_forall_not_mem],
    refine λ A HA, h𝒜 HA HA _,
    rw [disjoint_self_iff_empty, ←finset.card_eq_zero, ←b],
    exact h₂ HA },
  refine le_of_not_lt (λ size, _),
  -- Consider 𝒜bar = {A^c | A ∈ 𝒜}
  set 𝒜bar := 𝒜.image (λ A, univ \ A),
  -- Then its iterated shadow (∂^[n-2k] 𝒜bar) is disjoint from 𝒜 by
  -- intersecting-ness
  have : disjoint 𝒜 (shadow^[n-2*r] 𝒜bar),
  { rw disjoint_right,
    intros A hAbar hA,
    simp [sub_iff_shadow_iter, mem_image] at hAbar,
    rcases hAbar with ⟨C, hC, AsubnotC, _⟩,
    exact h𝒜 hA hC (disjoint_of_subset_left AsubnotC sdiff_disjoint) },
  have : r ≤ n := trans h₃ (nat.div_le_self n 2),
  have : 1 ≤ n := trans ‹1 ≤ r› ‹r ≤ n›,
  -- We know the size of 𝒜bar since it's the same size as 𝒜
  have z : nat.choose (n-1) (n-r) < 𝒜bar.card,
  { convert size using 1,
    { apply choose_symm_of_eq_add,
      rw [←nat.add_sub_assoc ‹r ≥ 1›, nat.sub_add_cancel ‹r ≤ n›] },
    { refine card_image_of_inj_on (λ A _ B _ k, _),
      replace k : ⊤ ⊓ A = ⊤ ⊓ B := sdiff_eq_sdiff_iff_inf_eq_inf.1 k,
      rwa [top_inf_eq, top_inf_eq] at k } },
  -- and everything in 𝒜bar has size n-r.
  have : (𝒜bar : set (finset X)).sized (n - r),
  { intro A,
    rw mem_image,
    rintro ⟨B, Bz, rfl⟩,
    rw [card_univ_diff, fintype.card_fin, h₂ Bz] },
  have : n - 2 * r ≤ n - r,
  { rw tsub_le_tsub_iff_left ‹r ≤ n›,
    exact nat.le_mul_of_pos_left zero_lt_two },
  -- We can use the Lovasz form of Kruskal-Katona to get |∂^[n-2k] 𝒜bar| ≥ (n-1) choose r
  have kk := lovasz_form ‹n - 2 * r ≤ n - r›
             ((tsub_le_tsub_iff_left ‹1 ≤ n›).2 h1r)
             tsub_le_self ‹sized 𝒜bar (n - r)› z.le,
  have q: n - r - (n - 2 * r) = r,
  { rw [nat.sub.right_comm, nat.sub_sub_self, two_mul],
    apply nat.add_sub_cancel,
    rw [mul_comm, ←nat.le_div_iff_mul_le' zero_lt_two],
    exact h₃ },
  rw q at kk,
  -- But this gives a contradiction: `n choose r < |𝒜| + |∂^[n-2k] 𝒜bar|`
  have : n.choose r < (𝒜 ∪ (shadow^[n - 2 * r] 𝒜bar)).card,
    rw card_disjoint_union ‹_›,
    convert lt_of_le_of_lt (add_le_add_left kk _) (add_lt_add_right size _),
    convert nat.choose_succ_succ _ _,
    any_goals {rwa [nat.sub_one, nat.succ_pred_eq_of_pos]},
  apply not_le_of_lt this,
  convert sized.card_le _,
  rw fintype.card_fin,
  rw sized_union,
  refine ⟨‹_›, _⟩,
  convert ‹sized 𝒜bar (n - r)›.shadow_iter,
  rw q,
end
