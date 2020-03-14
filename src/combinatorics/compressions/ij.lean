/-
ij compressions
-/

import data.finset
import combinatorics.shadows

open finset

variable {α : Type*}
variables [decidable_eq α]

namespace ij
  def compress (i j : α) (A : finset α) : finset α :=
  if j ∈ A ∧ i ∉ A
    then insert i (A.erase j)
    else A

  lemma compressed_set (i j : α) {A : finset α} : ¬ (j ∈ compress i j A ∧ i ∉ compress i j A) :=
  begin
    intro,
    rw compress at a,
    split_ifs at a,
      apply a.2,
      apply mem_insert_self,
    exact h a
  end

  lemma compress_idem (i j : α) (A : finset α) : compress i j (compress i j A) = compress i j A :=
  begin
    rw compress,
    split_ifs,
      exfalso,
      apply compressed_set _ _ h,
    refl
  end

  @[reducible] def compress_remains (i j : α) (𝒜 : finset (finset α)) : finset (finset α) := 𝒜.filter (λ A, compress i j A ∈ 𝒜)
  @[reducible] def compress_motion (i j : α) (𝒜 : finset (finset α)) : finset (finset α) := (𝒜.filter (λ A, compress i j A ∉ 𝒜)).image (compress i j)

  def compress_family (i j : α) (𝒜 : finset (finset α)) : finset (finset α) :=
  compress_motion i j 𝒜 ∪ compress_remains i j 𝒜

  lemma mem_compress_remains (𝒜 : finset (finset α)) (i j : α) (A : finset α) : A ∈ compress_remains i j 𝒜 ↔ A ∈ 𝒜 ∧ compress i j A ∈ 𝒜 :=
  by rw mem_filter

  lemma mem_compress_motion (𝒜 : finset (finset α)) (i j : α) (A : finset α) : A ∈ compress_motion i j 𝒜 ↔ A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, compress i j B = A) :=
  begin
    simp [compress_motion],
    split; rintro ⟨p, q, r⟩,
      exact ⟨r ▸ q.2, p, ⟨q.1, r⟩⟩,
    exact ⟨q, ⟨r.1, r.2.symm ▸ p⟩, r.2⟩,
  end

  lemma mem_compress (𝒜 : finset (finset α)) (i j : α) (A : finset α) :
    A ∈ compress_family i j 𝒜 ↔ (A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, compress i j B = A)) ∨ (A ∈ 𝒜 ∧ compress i j A ∈ 𝒜) :=
  by rw [compress_family, mem_union, mem_compress_remains, mem_compress_motion]

  lemma compress_disjoint (𝒜 : finset (finset α)) (i j : α) : disjoint (compress_motion i j 𝒜) (compress_remains i j 𝒜) :=
  begin
    rw disjoint_left,
    intros A HA HB,
    rw mem_compress_remains at HB,
    rw mem_compress_motion at HA,
    exact HA.1 HB.1
  end

  lemma inj_ish {i j : α} {A B : finset α} (hA : j ∈ A ∧ i ∉ A) (hB : j ∈ B ∧ i ∉ B)
    (Z : insert i (erase A j) = insert i (erase B j)) : A = B :=
  begin
    ext x,
    by_cases h₁: (x=j), rw h₁, simp [hA, hB],
    by_cases h₂: (x=i), rw h₂, simp [hA, hB],
    rw ext at Z, replace Z := Z x,
    simp [mem_insert, mem_erase, h₁, h₂] at Z, assumption
  end

  lemma compressed_size (𝒜 : finset (finset α)) (i j : α) : (compress_family i j 𝒜).card = 𝒜.card :=
  begin
    rw [compress_family, card_disjoint_union (compress_disjoint _ _ _), card_image_of_inj_on],
      rw [← card_disjoint_union, union_comm, filter_union_filter_neg_eq],
      rw [disjoint_iff_inter_eq_empty, inter_comm],
      apply filter_inter_filter_neg_eq,
    intros A HX Y HY Z,
    rw mem_filter at HX HY,
    rw compress at HX Z,
    split_ifs at HX Z,
      rw compress at HY Z,
      split_ifs at HY Z,
        exact inj_ish h h_1 Z,
    all_goals {tauto}
  end

  lemma insert_erase_comm {i j : α} {A : finset α} (h : i ≠ j) : insert i (erase A j) = erase (insert i A) j :=
  begin
    simp only [ext, mem_insert, mem_erase],
    intro x,
    split; intro p,
      cases p, split, rw p,
    all_goals {tauto},
  end

  lemma compress_moved {𝒜 : finset (finset α)} {i j : α} {A : finset α} (h₁ : A ∈ compress_family i j 𝒜) (h₂ : A ∉ 𝒜) :
    i ∈ A ∧ j ∉ A ∧ erase (insert j A) i ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    rcases h₁ with ⟨_, B, H, HB⟩ | _,
      rw compress at HB,
      split_ifs at HB,
        rw ← HB,
        refine ⟨mem_insert_self _ _, _, _⟩,
          rw mem_insert,
          intro,
          rcases a with rfl, tauto,
          exact not_mem_erase j B a,
        have: erase (insert j (insert i (erase B j))) i = B,
          rw [insert_erase_comm, insert_erase (mem_insert_of_mem h.1), erase_insert h.2],
          rintro rfl, tauto,
        rwa this,
      rw HB at H, tauto,
    tauto
  end

  lemma compress_held {𝒜 : finset (finset α)} {i j : α} {A : finset α} (h₁ : j ∈ A) (h₂ : A ∈ compress_family i j 𝒜) : A ∈ 𝒜 :=
  begin
    rw mem_compress at h₂,
    rcases h₂ with ⟨_, B, H, HB⟩ | _,
      rw ← HB at h₁,
      rw compress at HB h₁,
      split_ifs at HB h₁,
        rw mem_insert at h₁,
        rcases h₁ with rfl | h₁, tauto,
        exfalso, exact not_mem_erase _ _ h₁,
      rwa ← HB,
    tauto
  end

  lemma compress_both {𝒜 : finset (finset α)} {i j : α} {A : finset α} (h₁ : A ∈ compress_family i j 𝒜) (h₂ : j ∈ A) (h₃ : i ∉ A) : erase (insert i A) j ∈ 𝒜 :=
  begin
    have: A ∈ 𝒜, apply compress_held h₂ h₁,
    rw mem_compress at h₁,
    replace h₁ : compress i j A ∈ 𝒜, tauto,
    rw compress at h₁,
    have: j ∈ A ∧ i ∉ A := ⟨h₂, h₃⟩,
    split_ifs at h₁,
    rwa ← insert_erase_comm,
    intro, rw a at *, tauto,
  end

  lemma compression_reduces_shadow {𝒜 : finset (finset α)} {i j : α} : (∂ compress_family i j 𝒜).card ≤ (∂𝒜).card :=
  begin
    set 𝒜' := compress_family i j 𝒜,
    suffices: (∂𝒜' \ ∂𝒜).card ≤ (∂𝒜 \ ∂𝒜').card,
      suffices z: card (∂𝒜' \ ∂𝒜 ∪ ∂𝒜' ∩ ∂𝒜) ≤ card (∂𝒜 \ ∂𝒜' ∪ ∂𝒜 ∩ ∂𝒜'),
        rwa [sdiff_union_inter, sdiff_union_inter] at z,
      rw [card_disjoint_union, card_disjoint_union, inter_comm],
      apply add_le_add_right ‹_›,
      any_goals { apply sdiff_inter_inter },

    have q₁: ∀ B ∈ ∂𝒜' \ ∂𝒜, i ∈ B ∧ j ∉ B ∧ erase (insert j B) i ∈ ∂𝒜 \ ∂𝒜',
      intros B HB,
      obtain ⟨k, k'⟩: B ∈ ∂𝒜' ∧ B ∉ ∂𝒜 := mem_sdiff.1 HB,
      have m: ∀ y ∉ B, insert y B ∉ 𝒜,
        intros y _ _,
        apply k',
        rw mem_shadow',
        exact ⟨y, H, a⟩,
      rcases mem_shadow'.1 k with ⟨x, _, _⟩,
      have q := compress_moved ‹insert x B ∈ 𝒜'› (m _ ‹x ∉ B›),
      rw insert.comm at q,
      have: j ∉ B := q.2.1 ∘ mem_insert_of_mem,
      have: i ≠ j, rintro rfl, tauto,
      have: x ≠ i, intro a, rw a at *, rw [erase_insert] at q,
        exact m _ ‹j ∉ B› q.2.2,
        rw mem_insert, tauto,
      have: x ≠ j, intro a, rw a at q, exact q.2.1 (mem_insert_self _ _),
      have: i ∈ B := mem_of_mem_insert_of_ne q.1 ‹x ≠ i›.symm,
      refine ⟨‹_›, ‹_›, _⟩,
      rw mem_sdiff,
      split,
        rw mem_shadow',
        rw ← insert_erase_comm ‹x ≠ i› at q,
        exact ⟨x, λ a, ‹x ∉ B› (mem_of_mem_insert_of_ne (mem_of_mem_erase a) ‹x ≠ j›), q.2.2⟩,

      intro a, rw mem_shadow' at a,
      rcases a with ⟨y, yH, H⟩,
      have: y ≠ i, intro b, rw [b, insert_erase (mem_insert_of_mem ‹i ∈ B›)] at H,
                  exact m _ ‹j ∉ B› (compress_held (mem_insert_self _ _) H),
      have: y ≠ j, simp [‹y ≠ i›, not_or_distrib] at yH, exact yH.1,
      have: y ∉ B, simp [‹y ≠ i›, ‹y ≠ j›] at yH, assumption,
      have: j ∈ insert y (erase (insert j B) i), simp [‹i ≠ j›.symm],
      have: i ∉ insert y (erase (insert j B) i), simp [‹y ≠ i›.symm],
      have := compress_both H ‹_› ‹_›,
      rw [insert.comm, ← insert_erase_comm ‹y ≠ j›, insert_erase (mem_insert_of_mem ‹i ∈ B›), erase_insert ‹j ∉ B›] at this,
      exact m _ ‹y ∉ B› ‹insert y B ∈ 𝒜›,

    set f := (λ (B : finset α), erase (insert j B) i),
    apply card_le_card_of_inj_on f,
      intros _ HB,
      exact (q₁ _ HB).2.2,

    intros B₁ HB₁ B₂ HB₂ f₁,
    have z₁ := q₁ B₁ HB₁,
    have z₂ := q₁ B₂ HB₂,
    have: j ≠ i := (ne_of_mem_of_not_mem z₁.1 z₁.2.1).symm,
    rw ← insert_erase_comm ‹j ≠ i› at z₁ z₂,
    apply inj_ish ⟨z₁.1, z₁.2.1⟩ ⟨z₂.1, z₂.2.1⟩,
    convert f₁, all_goals {rw insert_erase_comm ‹j ≠ i›}
  end
end ij
