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

namespace finset
variables {α : Type*} [decidable_eq α] {s t : finset α}

lemma card_sdiff_comm (h : s.card = t.card) : (s \ t).card = (t \ s).card :=
begin
  have : (s \ t ∪ s ∩ t).card = (t \ s ∪ t ∩ s).card,
    rwa [sdiff_union_inter, sdiff_union_inter],
  rwa [card_disjoint_union (disjoint_sdiff_inter _ _),
      card_disjoint_union (disjoint_sdiff_inter _ _), inter_comm, add_left_inj] at this,
end

end finset

namespace finset
namespace colex
variables {α : Type*} [linear_order α] {𝒜 𝒜₁ 𝒜₂ : finset (finset α)} {s t : finset α} {r : ℕ}

open_locale finset_family

variables [fintype α]

/-- This is important for iterating Kruskal-Katona: the shadow of an initial segment is also an
initial segment. -/
lemma shadow_init_seg (hs : s.nonempty) : ∂ (init_seg s) = init_seg (erase s (min' s hs)) :=
begin
  -- This is a pretty painful proof, with lots of cases.
  ext t,
  simp only [mem_shadow_iff_insert_mem, mem_init_seg, exists_prop],
  split,
    -- First show that if t ∪ i ≤ s, then t ≤ s - min s
  { rintro ⟨i, ih, p, hts⟩,
    rw card_insert_of_not_mem ih at p,
    rw le_def at hts,
    have cards : (erase s (min' s hs)).card = t.card,
    { rw [card_erase_of_mem (min'_mem _ _), p, add_tsub_cancel_right] },
    -- Case on t ∪ i = s or t ∪ i < s
    obtain rfl | ⟨k, z, hkt, hks⟩ := hts,
    { -- Case on i = min s or not
      refine ⟨cards, le_def.2 $ (eq_or_ne i $ min' _ hs).imp (λ q, _) $ λ q, _⟩,
      { rw [←q, erase_insert ih] },
      { refine ⟨i, λ x hx, _, ih, mem_erase.2 ⟨q, mem_insert_self _ _⟩⟩,
        simpa only [mem_erase, mem_insert, hx.ne', ne.def, false_or, iff_and_self]
          using λ _, ((min'_le _ _ $ mem_insert_self _ _).trans_lt hx).ne' } },
    { simp only [cards, eq_self_iff_true, true_and, mem_insert, not_or_distrib,
        ←ne.def] at ⊢ hkt hks z,
      -- t ∪ i < s, with k as the colex witness. Cases on k < i or k > i.
      cases hkt.1.lt_or_lt,
      { refine or.inr ⟨i, λ x hx, _, ih, _⟩,
        -- When k < i, then i works as the colex witness to show t < s - min s
        { refine ⟨λ p, mem_erase_of_ne_of_mem (((min'_le _ _ ‹_›).trans_lt h).trans hx).ne'
            ((z $ h.trans hx).1 $ or.inr p), λ p, _⟩,
          exact ((z $ h.trans hx).2 $ mem_of_mem_erase p).resolve_left hx.ne' },
        apply mem_erase_of_ne_of_mem _ ((z h).1 $ or.inl rfl),
        apply ne_of_gt (lt_of_le_of_lt _ h),
        apply min'_le,
        assumption },
      { -- When k > i, cases on min s < k or min s = k
        obtain h₁ | h₁ := (min'_le _ _ ‹k ∈ s›).lt_or_eq,
          -- If min s < k, k works as the colex witness for t < s - min s
        { refine or.inr ⟨k, λ x hx, _, hkt.2,
                        mem_erase_of_ne_of_mem (ne_of_gt h₁) ‹_›⟩,
          simpa [(h.trans hx).ne', ←z hx] using λ _, (h₁.trans hx).ne' },
        -- If k = min s, then t = s - min s
        generalize_proofs at h₁,
        subst h₁,
        refine or.inl (eq_of_subset_of_card_le (λ a ha, _) cards.ge).symm,
        rw mem_erase at ha,
        have : a ≠ i := ne_of_gt (lt_of_lt_of_le h $ min'_le _ _ ha.2),
        rw ←z at ha,
        apply ha.2.resolve_left ‹a ≠ i›,
        exact (min'_le _ _ ha.2).lt_of_ne ha.1.symm } } },
  -- Now show that if t ≤ s - min s, there is j such that t ∪ j ≤ s
  -- We choose j as the smallest thing not in t
  simp_rw le_def,
  rintro ⟨cards', rfl | ⟨k, z, hkt, hks⟩⟩,
  -- If t = s - min s, then use j = min s so t ∪ j = s
  { refine ⟨min' s hs, not_mem_erase _ _, _⟩,
    rw [←le_def, insert_erase (min'_mem _ _)],
    exact ⟨rfl, le_rfl⟩ },
  set j := min' tᶜ ⟨k, mem_compl.2 hkt⟩,
  -- Assume first t < s - min s, and take k as the colex witness for this
  have hjk : j ≤ k := min'_le _ _ (mem_compl.2 ‹k ∉ t›),
  have : j ∉ t := mem_compl.1 (min'_mem _ _),
  have cards : card s = card (insert j t),
  { rw [card_insert_of_not_mem ‹j ∉ t›, ←‹_ = card t›, card_erase_add_one (min'_mem _ _)] },
  refine ⟨j, ‹_›, cards, _⟩,
  -- Cases on j < k or j = k
  obtain hjk | r₁ := hjk.lt_or_eq,
  -- if j < k, k is our colex witness for t ∪ {j} < s
  { refine or.inr ⟨k, _, mt (λ t, mem_of_mem_insert_of_ne t hjk.ne') hkt, mem_of_mem_erase ‹_›⟩,
    intros x hx,
    simpa only [mem_insert, z hx, (hjk.trans hx).ne', mem_erase, ne.def, false_or,
      and_iff_right_iff_imp] using λ _, ((min'_le _ _ $ mem_of_mem_erase hks).trans_lt hx).ne' },
  -- if j = k, all of range k is in t so by sizes t ∪ {j} = s
  refine or.inl (eq_of_subset_of_card_le (λ a ha, _) cards.ge).symm,
  rcases lt_trichotomy k a with lt | rfl | gt,
  { apply mem_insert_of_mem,
    rw z lt,
    apply mem_erase_of_ne_of_mem _ ha,
    apply ne_of_gt (lt_of_le_of_lt _ lt),
    apply min'_le _ _ (mem_of_mem_erase ‹_›) },
  { rw r₁, apply mem_insert_self },
  { apply mem_insert_of_mem, rw ←r₁ at gt,
    by_contra,
    apply not_lt_of_le (min'_le tᶜ _ _) gt,
    rwa mem_compl }
end

/-- The shadow of an initial segment is also an initial segment. -/
protected lemma is_init_seg.shadow (h₁ : is_init_seg 𝒜 r) : is_init_seg (∂𝒜) (r - 1) :=
begin
  obtain rfl | hr := nat.eq_zero_or_pos r,
  { have : 𝒜 ⊆ {∅},
    { intros A hA,
      rw [mem_singleton, ←finset.card_eq_zero],
      exact h₁.1 hA },
    have := shadow_monotone this,
    simp only [subset_empty, le_eq_subset, shadow_singleton_empty] at this,
    simp [this] },
  obtain rfl | h𝒜 := 𝒜.eq_empty_or_nonempty,
  { simp },
  obtain ⟨s, rfl, rfl⟩ := is_init_seg_iff_exists_init_seg.1 ⟨h𝒜, h₁⟩,
  rw [shadow_init_seg (card_pos.1 hr), ←card_erase_of_mem (min'_mem _ _)],
  exact is_init_seg_init_seg,
end

end colex

open finset colex nat uv
open_locale finset_family

variables {α : Type*} [linear_order α] {s U V : finset α} {n : ℕ}

namespace UV

/-- Applying the compression makes the set smaller in colex. This is intuitive since a portion of
the set is being "shifted 'down" as `max U < max V`. -/
lemma to_colex_compress_lt_to_colex {hU : U.nonempty} {hV : V.nonempty} (h : max' U hU < max' V hV)
  (hA : compress U V s ≠ s) : (compress U V s).to_colex < s.to_colex :=
begin
  rw [compress, ite_ne_right_iff] at hA,
  rw [compress, if_pos hA.1, lt_def],
  refine ⟨max' V hV, λ a ha, _, not_mem_sdiff_of_mem_right $ max'_mem _ _, hA.1.2 $ max'_mem _ _⟩,
  have : a ∉ V := λ H, ha.not_le (le_max' _ _ H),
  have : a ∉ U := λ H, ha.not_lt ((le_max' _ _ H).trans_lt h),
  simp [‹a ∉ U›, ‹a ∉ V›],
end

/-- These are the compressions which we will apply to decrease the "measure" of a family of sets.-/
def useful_compression (U V : finset α) : Prop :=
disjoint U V ∧ U.card = V.card ∧ ∃ (HU : U.nonempty) (HV : V.nonempty), max' U HU < max' V HV

instance useful_compression.decidable_rel : @decidable_rel (finset α) (useful_compression) :=
λ U V, decidable_of_iff (_ ∧ _) iff.rfl

/-- Applying a good compression will decrease measure, keep cardinality, keep sizes and decrease
shadow. In particular, 'good' means it's useful, and every smaller compression won't make a
difference. -/
lemma compression_improved (𝒜 : finset (finset α)) (h₁ : useful_compression U V)
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
  { refine (finset.max'_subset _ $ erase_subset _ _).trans_lt (max_lt.trans_le $
      le_max' _ _ $ mem_erase.2 ⟨(min'_lt_max'_of_card _ _).ne', max'_mem _ _⟩),
    rwa ←same_size }
end

/-- If we're compressed by all useful compressions, then we're an initial segment. This is the other
key Kruskal-Katona part. -/
lemma is_init_seg_of_compressed {ℬ : finset (finset α)} {r : ℕ} (h₁ : (ℬ  : set (finset α)).sized r)
  (h₂ : ∀ U V, useful_compression U V → is_compressed U V ℬ) :
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
    { have h := to_colex_compress_lt_to_colex lt,
      rw compress_sdiff_sdiff at h,
      exact (hBA.not_lt $ h hAB).elim },
    { exact (disjoint_right.1 disj (max'_mem _ hU) $ eq.symm ▸ max'_mem _ _).elim },
    { assumption } },
  refine hB _,
  rw ←(h₂ _ _ ⟨disj, card_sdiff_comm hAB'.symm, hV, hU, smaller⟩).eq,
  exact mem_compression.2 (or.inr ⟨hB, A, hA, compress_sdiff_sdiff _ _⟩),
end

/-- This measures roughly how compressed the family is. (Note that it does depend on the ordering of
the ground set, unlike Kruskal-Katona itself). -/
def family_measure (𝒜 : finset (finset (fin n))) : ℕ := 𝒜.sum $ λ A, (image fin.val A).sum (pow 2)

/-- Applying a compression strictly decreases the measure. This helps show that "compress until we
can't any more" is a terminating process. -/
lemma family_measure_compression_lt_family_measure {U V : finset (fin n)} {hU : U.nonempty}
  {hV : V.nonempty} (h : max' U hU < max' V hV) {𝒜 : finset (finset (fin n))} (a : 𝓒 U V 𝒜 ≠ 𝒜) :
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
      /-apply to_colex_compress_lt_to_colex A h (q _ hA),
    intros x Hx y Hy k, have cx := q x Hx, have cy := q y Hy,
    rw compress at k cx, split_ifs at k cx,
      rw compress at k cy, split_ifs at k cy,
        exact inj_ish h_1 h_2 k,
      exfalso, apply cy rfl,
    exfalso, apply cx rfl,-/
  rw disjoint_iff_inter_eq_empty,
  apply filter_inter_filter_neg_eq
end

/-- The main Kruskal-Katona helper: use induction with our measure to keep compressing until
we can't any more, which gives a set family which is fully compressed and has the nice properties we
want. -/
lemma kruskal_katona_helper {r : ℕ} (𝒜 : finset (finset (fin n)))
  (h : (𝒜 : set (finset (fin n))).sized r) :
  ∃ ℬ : finset (finset (fin n)),
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
  have p1 : (∂(𝓒 U V A)).card ≤ (∂A).card := compression_improved _ uvh.2.1 h₂,
  -- rcases uvh.2.1 with ⟨_, _, _, same_size, max_lt⟩,
  -- rw [measure, inv_image] at ih,
  -- rcases ih (𝓒 U V A) _ _ with ⟨t, q1, q2, q3, q4⟩,
  -- { exact ⟨t, trans q1 p1, trans (compressed_size _ _).symm q2, q3, q4⟩ },
  -- { apply family_measure_compression_lt_family_measure max_lt uvh.2.2 },
  -- { apply 𝓒_sized same_size h }
end

end UV

local notation `X` := fin n

-- Finally we can prove Kruskal-Katona.
section KK
variables {r k i : ℕ} {𝒜 𝒞 : finset (finset X)}

/-- The Kruskal-Katona theorem. It says that given a set family `𝒜` consisting of `r`-sets, and `𝒞`
an initial segment of the colex order of the same size, the shadow of `𝒞` is smaller than the shadow
of `𝒜`. In particular, this gives that the minimum shadow size is achieved by initial segments of
colex.

Proof notes: Most of the work was done in Kruskal-Katona helper; it gives a `ℬ` which is fully
compressed, and so we know it's an initial segment, which by uniqueness is the same as `𝒞`. -/
theorem kruskal_katona (h₁ : (𝒜 : set (finset (fin n))).sized r) (h₂ : 𝒜.card = 𝒞.card)
  (h₃ : is_init_seg 𝒞 r) :
  (∂𝒞).card ≤ (∂𝒜).card :=
begin
  obtain ⟨ℬ, card_le, t, hℬ, fully_comp⟩ := UV.kruskal_katona_helper 𝒜 h₁,
  convert card_le,
  have hcard : card ℬ = card 𝒞 := t.symm.trans h₂,
  obtain CB | BC :=
    h₃.total (UV.is_init_seg_of_compressed hℬ $ λ U V hUV, by convert fully_comp U V hUV),
  { exact eq_of_subset_of_card_le CB hcard.le },
  { exact (eq_of_subset_of_card_le BC hcard.ge).symm }
end

/--  We can strengthen Kruskal-Katona slightly: note the middle and has been relaxed to a `≤`.
This shows that the minimum possible shadow size is attained by initial segments. -/
theorem strengthened_kk (h₁ : (𝒜 : set (finset (fin n))).sized r) (h₂ : 𝒞.card ≤ 𝒜.card)
  (h₃ : is_init_seg 𝒞 r) :
  (∂𝒞).card ≤ (∂𝒜).card :=
begin
  rcases exists_smaller_set 𝒜 𝒞.card h₂ with ⟨𝒜', prop, size⟩,
  refine (kruskal_katona (λ A hA, h₁ (prop hA)) size h₃).trans (card_le_of_subset _),
  rw [shadow, shadow],
  apply shadow_monotone prop
end

/--An iterated form of the Kruskal-Katona theorem. In particular, the minimum possible iterated
shadow size is attained by initial segments. -/
theorem iterated_kk (h₁ : (𝒜 : set (finset (fin n))).sized r) (h₂ : 𝒞.card ≤ 𝒜.card)
  (h₃ : is_init_seg 𝒞 r) :
  (shadow^[k] 𝒞).card ≤ (shadow^[k] 𝒜).card :=
begin
  induction k with k ih generalizing r 𝒜 𝒞,
  { simpa },
  { exact ih h₁.shadow (strengthened_kk h₁ h₂ h₃) h₃.shadow }
end

/-- A special case of Kruskal-Katona which is sometimes easier to work with.
If `|𝒜| ≥ k choose r`, (and everything in `𝒜` has size `r`) then the initial segment we compare to
is just all the subsets of `{0, ..., k - 1}` of size `r`. The `i`-th iterated shadow of this is all
the subsets of `{0, ..., k - 1}` of size `r - i`, so the `i`-th iterated shadow of `𝒜` has at least
`k.choose (r - i)` elements. -/
theorem lovasz_form {𝒜 : finset (finset X)} (hir : i ≤ r)
  (hrk : r ≤ k) (hkn : k ≤ n) (h₁ : (𝒜 : set (finset X)).sized r) (h₂ : k.choose r ≤ 𝒜.card) :
  k.choose (r - i) ≤ (shadow^[i] 𝒜).card :=
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
  𝒜.card ≤ (n - 1).choose (r - 1) :=
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
  have h𝒜bar : (𝒜bar : set (finset X)).sized (n - r),
  { intro A,
    rw [coe_image, set.mem_image],
    rintro ⟨B, Bz, rfl⟩,
    rw [card_univ_diff, fintype.card_fin, h₂ Bz] },
  have : n - 2 * r ≤ n - r,
  { rw tsub_le_tsub_iff_left ‹r ≤ n›,
    exact nat.le_mul_of_pos_left zero_lt_two },
  -- We can use the Lovasz form of Kruskal-Katona to get |∂^[n-2k] 𝒜bar| ≥ (n-1) choose r
  have kk := lovasz_form ‹n - 2 * r ≤ n - r›
             ((tsub_le_tsub_iff_left ‹1 ≤ n›).2 h1r)
             tsub_le_self h𝒜bar z.le,
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
  convert set.sized.card_le _,
  rw fintype.card_fin,
  rw [coe_union, set.sized_union],
  refine ⟨‹_›, _⟩,
  convert h𝒜bar.shadow_iter,
  rw q,
end

end finset
