/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import data.finite.card

/-!
# Noncomputable Set Cardinality

We define the cardinality `set.ncard s` of a set `s` as a natural number. This function is
noncomputable (being defined in terms of `nat.card`) and takes the value `0` if `s` is infinite.

This can be seen as an API for `nat.card α` in the special case where `α` is a subtype arising from
a set. It is intended as an alternative to `finset.card` and `fintype.card`,  both of which contain
data in their definition that can cause awkwardness when using `set.to_finset`.  Using `set.ncard`
allows cardinality computations to avoid `finset`/`fintype` completely, staying in `set` and letting
finiteness be handled either explicitly or via typeclasses. An ideal use case is when working with
terms in `set α` where a `finite α` instance is present.

## Main Definitions

* `set.ncard s` is the cardinality of the set `s` as a natural number, provided `s` is finite.
  If `s` is infinite, then `set.ncard s = 0`.

## Implementation Notes

The lemmas in this file are very similar to those in `data.finset.card`, but with `set` operations
instead of `finset`; most of the proofs invoke their `finset` analogues. Nearly all the lemmas
require finiteness of one or more of their arguments, which we give as `[finite s]`. Often, where
there are two arguments `s` and `t`, the finiteness of one follows from the other in the context
of the lemma, in which case we only include the ones that are needed, and derive the other inside
the proof.
-/

open_locale classical

variables {α β : Type*} {s t : set α} {a b x y : α} {f : α → β}

namespace set

/-- The cardinality of `s : set α` . Has the junk value `0` if `s` is infinite -/
noncomputable def ncard (s : set α) := nat.card s

lemma ncard_def (s : set α) : s.ncard = nat.card s := rfl

lemma ncard_eq_to_finset_card (s : set α) [finite s] :
  s.ncard = finset.card (@set.to_finset α s (fintype.of_finite s)) :=
begin
  haveI := fintype.of_finite s,
  rw [ncard, nat.card_eq_fintype_card, set.to_finset_card],
  congr',
end

lemma ncard_le_of_subset [finite t] (hst : s ⊆ t) :
  s.ncard ≤ t.ncard :=
finite.card_le_of_embedding $ set.embedding_of_subset _ _ hst

lemma ncard_mono [finite α] :
  @monotone (set α) _ _ _ ncard :=
λ _ _, ncard_le_of_subset

@[simp] lemma ncard_eq_zero [finite s] :
  s.ncard = 0 ↔ s = ∅ :=
by simp [ncard_def, finite.card_eq_zero_iff]

@[simp] lemma ncard_eq_zero_of_infinite (s : set α) [infinite s] :
  s.ncard = 0 :=
nat.card_eq_zero_of_infinite

@[simp] lemma ncard_coe_finset (s : finset α) :
  (s : set α).ncard = s.card :=
by rw [ncard_eq_to_finset_card, finset.to_finset_coe]

@[simp] lemma ncard_empty (α : Type*) :
  (∅ : set α).ncard = 0 :=
by simp only [ncard_eq_zero]

lemma infinite.ncard (hs : s.infinite) :
  s.ncard = 0 :=
by {haveI := hs.to_subtype, exact s.ncard_eq_zero_of_infinite}

lemma ncard_pos [finite s] :
  0 < s.ncard ↔ s.nonempty :=
by simp [ncard_def, finite.card_pos_iff]

lemma ncard_ne_zero_of_mem [finite s] (h : a ∈ s) :
  s.ncard ≠ 0 :=
(ncard_pos.mpr ⟨a,h⟩).ne.symm

lemma finite_of_ncard_ne_zero (hs : s.ncard ≠ 0) :
  s.finite :=
s.finite_or_infinite.elim id (λ h, (hs h.ncard).elim)

lemma finite_of_ncard_pos (hs : 0 < s.ncard) :
  s.finite :=
finite_of_ncard_ne_zero hs.ne.symm

lemma nonempty_of_ncard_ne_zero (hs : s.ncard ≠ 0) :
  s.nonempty :=
by {rw nonempty_iff_ne_empty, rintro rfl, simpa using hs}

@[simp] lemma ncard_singleton (a : α) :
  ({a} : set α).ncard = 1 :=
by simp [ncard_eq_to_finset_card]

lemma ncard_singleton_inter : ({a} ∩ s).ncard ≤ 1 :=
begin
  rw [←inter_self {a}, inter_assoc, ncard_eq_to_finset_card, to_finset_inter, to_finset_singleton],
  apply finset.card_singleton_inter,
end

section insert_erase

@[simp] lemma ncard_insert_of_not_mem [finite s] (h : a ∉ s) :
  (insert a s).ncard = s.ncard + 1 :=
begin
  haveI := fintype.of_finite s,
  rw [ncard_eq_to_finset_card, ncard_eq_to_finset_card, to_finset_insert,
    finset.card_insert_of_not_mem],
  { congr,},
  simpa,
end

lemma ncard_insert_of_mem (h : a ∈ s) :
  ncard (insert a s) = s.ncard :=
by rw insert_eq_of_mem h

lemma card_insert_le (a : α) (s : set α) : (insert a s).ncard ≤ s.ncard + 1 :=
begin
  obtain (hs | hs) := s.finite_or_infinite,
  { haveI := hs.to_subtype,
    exact (em (a ∈ s)).elim (λ h, (ncard_insert_of_mem h).trans_le (nat.le_succ _))
      (λ h, by rw ncard_insert_of_not_mem h)},
  rw (hs.mono (subset_insert a s)).ncard,
  exact nat.zero_le _,
end

lemma ncard_insert_eq_ite [finite s] :
  ncard (insert a s) = if a ∈ s then s.ncard else s.ncard + 1 :=
begin
  by_cases h : a ∈ s,
  { rw [ncard_insert_of_mem h, if_pos h] },
  { rw [ncard_insert_of_not_mem h, if_neg h] }
end

@[simp] lemma card_doubleton (h : a ≠ b) : ({a, b} : set α).ncard = 2 :=
by {rw [ncard_insert_of_not_mem, ncard_singleton], simpa}

@[simp] lemma ncard_diff_singleton_add_one [finite s] (h : a ∈ s) :
  (s \ {a}).ncard + 1 = s.ncard :=
begin
  have h' : a ∉ s \ {a}, by {rw [mem_diff_singleton], tauto},
  rw ←ncard_insert_of_not_mem h', congr', simpa,
end

@[simp] lemma ncard_diff_singleton_of_mem [finite s] (h : a ∈ s) :
  (s \ {a}).ncard = s.ncard - 1 :=
eq_tsub_of_add_eq (ncard_diff_singleton_add_one h)

lemma ncard_diff_singleton_lt_of_mem [finite s] (h : a ∈ s) :
  (s \ {a}).ncard < s.ncard :=
by {rw [←ncard_diff_singleton_add_one h], apply lt_add_one}

lemma ncard_diff_singleton_le (s : set α) (a : α) :
  (s \ {a}).ncard ≤ s.ncard :=
begin
  obtain (hs | hs) := s.finite_or_infinite,
  { haveI := hs.to_subtype,
    apply ncard_le_of_subset (diff_subset _ _), assumption},
  convert zero_le _,
  exact (hs.diff (by simp : set.finite {a})).ncard,
end

lemma pred_ncard_le_ncard_diff_singleton (s : set α) (a : α) :
  s.ncard - 1 ≤ (s \ {a}).ncard :=
begin
  cases s.finite_or_infinite,
  { haveI := h.to_subtype,
    by_cases h : a ∈ s,
    { rw ncard_diff_singleton_of_mem h, },
    rw diff_singleton_eq_self h,
    apply nat.pred_le},
  convert nat.zero_le _,
  rw h.ncard,
end

end insert_erase

lemma ncard_image_le [finite s] :
  (f '' s).ncard ≤ s.ncard :=
begin
  rw ncard_eq_to_finset_card,
  haveI := fintype.of_finite s,
  convert @finset.card_image_le _ _ s.to_finset f _,
  { convert rfl, ext, simp, },
  rw ncard_eq_to_finset_card, congr',
end

lemma ncard_image_of_inj_on (H : set.inj_on f s) :
  (f '' s).ncard = s.ncard :=
begin
  cases s.finite_or_infinite,
  { haveI := @fintype.of_finite s h.to_subtype,
    haveI := @fintype.of_finite _ (h.image f).to_subtype,
    convert card_image_of_inj_on H; simp [ncard_def]},
  rw [h.ncard, ((infinite_image_iff H).mpr h).ncard],
end

lemma inj_on_of_ncard_image_eq [finite s] (H : (f '' s).ncard = s.ncard) :
  set.inj_on f s :=
begin
  haveI := fintype.of_finite s,
  haveI := @fintype.of_finite _ ((to_finite s).image f).to_subtype,
  simp_rw ncard_eq_to_finset_card at H,
  rw ← coe_to_finset s,
  apply finset.inj_on_of_card_image_eq,
  convert H,
  ext,
  simp,
end

lemma ncard_image_iff [finite s] :
  (f '' s).ncard = s.ncard ↔ set.inj_on f s :=
⟨inj_on_of_ncard_image_eq, ncard_image_of_inj_on⟩

lemma ncard_image_of_injective (s : set α) (H : f.injective) :
  (s.image f).ncard = s.ncard :=
ncard_image_of_inj_on $ λ x _ y _ h, H h

lemma fiber_ncard_ne_zero_iff_mem_image [finite s] {y : β}:
  {x | x ∈ s ∧ f x = y}.ncard ≠ 0 ↔ y ∈ f '' s :=
begin
  refine ⟨nonempty_of_ncard_ne_zero, _⟩,
  rintros ⟨y,hy,rfl⟩,
  exact @ncard_ne_zero_of_mem _ _ y _ (by simpa),
end

@[simp] lemma ncard_map (f : α ↪ β) :
  (f '' s).ncard = s.ncard :=
ncard_image_of_injective _ f.injective

@[simp] lemma ncard_subtype (P : α → Prop) (s : set α) :
  {x : subtype P | (x : α) ∈ s}.ncard = (s ∩ (set_of P)).ncard :=
begin
  convert (ncard_image_of_injective _ (@subtype.coe_injective _ P)).symm,
  ext, rw inter_comm, simp,
end

lemma ncard_inter_le_ncard_left (s t : set α) [finite s] :
  (s ∩ t).ncard ≤ s.ncard :=
ncard_le_of_subset (inter_subset_left _ _)

lemma ncard_inter_le_ncard_right (s t : set α) [finite t] :
  (s ∩ t).ncard ≤ t.ncard :=
ncard_le_of_subset (inter_subset_right _ _)

lemma eq_of_subset_of_ncard_le  [finite t] (h : s ⊆ t) (h₂ : t.ncard ≤ s.ncard) :
  s = t :=
begin
  haveI := ((to_finite t).subset h).to_subtype,
  rw ←@to_finset_inj _ _ _ (fintype.of_finite s) (fintype.of_finite t),
  apply finset.eq_of_subset_of_card_le,
  { simpa, },
  rwa [←ncard_eq_to_finset_card, ←ncard_eq_to_finset_card],
end

lemma subset_iff_eq_of_ncard_le [finite t] (h : t.ncard ≤ s.ncard) :
  s ⊆ t ↔ s = t :=
⟨λ hst, eq_of_subset_of_ncard_le hst h, eq.subset'⟩

lemma map_eq_of_subset [finite s] {f : α ↪ α} (hs : f '' s ⊆ s) : f '' s = s :=
  eq_of_subset_of_ncard_le hs (ncard_map _).ge

lemma set_of_ncard_eq {P : α → Prop} [finite s] (h : {x ∈ s | P x}.ncard = s.ncard) (ha : a ∈ s) :
  P a :=
sep_eq_self_iff_mem_true.mp (eq_of_subset_of_ncard_le (by simp) h.symm.le) _ ha

lemma ncard_lt_ncard (h : s ⊂ t) [finite t] : s.ncard < t.ncard :=
begin
  haveI := ((to_finite t).subset h.subset).to_subtype,
  simp_rw [ncard_eq_to_finset_card],
  apply finset.card_lt_card,
  simpa,
end

lemma ncard_strict_mono [finite α] :
  @strict_mono (set α) _ _ _ ncard :=
λ _ _ h, ncard_lt_ncard h

lemma ncard_eq_of_bijective [finite s] {n : ℕ} (f : ∀ i, i < n → α)
  (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a)
  (hf' : ∀ i (h : i < n), f i h ∈ s)
  (f_inj : ∀ i j (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) :
  s.ncard = n :=
begin
  rw ncard_eq_to_finset_card,
  apply finset.card_eq_of_bijective,
  all_goals {simpa},
end

lemma ncard_congr {t : set β} [finite s] (f : Π a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
(h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) :
  s.ncard = t.ncard :=
begin
  set f' : s → t := λ x, ⟨f x.1 x.2, h₁ _ _⟩ with hf',
  have hbij : f'.bijective,
  { split,
    { rintros ⟨x,hx⟩ ⟨y,hy⟩ hxy,
      simp only [hf', subtype.val_eq_coe, subtype.coe_mk, subtype.mk_eq_mk] at hxy ⊢,
      apply h₂ _ _ hx hy hxy},
    rintro ⟨y,hy⟩,
    obtain ⟨a, ha, rfl⟩ := h₃ y hy,
    simp only [subtype.val_eq_coe, subtype.coe_mk, subtype.mk_eq_mk, set_coe.exists],
    exact ⟨_,ha,rfl⟩},
  haveI := @fintype.of_finite _ (finite.of_bijective hbij),
  haveI := fintype.of_finite s,
  convert fintype.card_of_bijective hbij;
  rw [ncard_def, nat.card_eq_fintype_card],
end

lemma ncard_le_ncard_of_inj_on {t : set β} [finite t] (f : α → β) (hf : ∀ a ∈ s, f a ∈ t)
(f_inj : inj_on f s) :
  s.ncard ≤ t.ncard :=
begin
  cases s.finite_or_infinite,
  { haveI := h.to_subtype,
    simp_rw [ncard_eq_to_finset_card],
    exact finset.card_le_card_of_inj_on f (by simpa) (by simpa)},
  convert nat.zero_le _,
  rw h.ncard,
end

lemma exists_ne_map_eq_of_ncard_lt_of_maps_to {t : set β} [finite t] (hc : t.ncard < s.ncard)
{f : α → β} (hf : ∀ a ∈ s, f a ∈ t) :
  ∃ (x ∈ s) (y ∈ s), x ≠ y ∧ f x = f y :=
begin
  by_contra h',
  simp only [ne.def, exists_prop, not_exists, not_and, not_imp_not] at h',
  exact (ncard_le_ncard_of_inj_on f hf h').not_lt hc,
end

lemma le_ncard_of_inj_on_range [finite s] {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
  (f_inj : ∀ (i < n) (j < n), f i = f j → i = j) :
  n ≤ s.ncard :=
by {rw ncard_eq_to_finset_card, apply finset.le_card_of_inj_on_range; simpa}

lemma surj_on_of_inj_on_of_ncard_le {t : set β} [finite t] (f : Π a ∈ s, β)
(hf : ∀ a ha, f a ha ∈ t) (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂)
(hst : t.ncard ≤ s.ncard) :
  ∀ b ∈ t, ∃ a ha, b = f a ha :=
begin
  intros b hb,
  set f' : s → t := λ x, ⟨f x.1 x.2, hf _ _⟩ with hf',
  have finj: f'.injective,
  { rintros ⟨x,hx⟩ ⟨y,hy⟩ hxy,
    simp only [hf', subtype.val_eq_coe, subtype.coe_mk, subtype.mk_eq_mk] at hxy ⊢,
    apply hinj _ _ hx hy hxy},
  haveI := fintype.of_finite t,
  haveI := fintype.of_injective f' finj,
  simp_rw [ncard_eq_to_finset_card] at hst,
  set f'' : ∀ a, a ∈ s.to_finset → β := λ a h, f a (by simpa using h) with hf'',
  convert @finset.surj_on_of_inj_on_of_card_le _ _ _ t.to_finset f'' (by simpa) (by simpa)
    (by convert hst) b (by simpa),
  simp,
end

lemma inj_on_of_surj_on_of_ncard_le [finite s] {t : set β} (f : Π a ∈ s, β)
  (hf : ∀ a ha, f a ha ∈ t) (hsurj : ∀ b ∈ t, ∃ a ha, b = f a ha) (hst : s.ncard ≤ t.ncard)
  ⦃a₁ a₂⦄ (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s) (ha₁a₂: f a₁ ha₁ = f a₂ ha₂) :
  a₁ = a₂ :=
begin
   set f' : s → t := λ x, ⟨f x.1 x.2, hf _ _⟩ with hf',
  have hsurj : f'.surjective,
  { rintro ⟨y,hy⟩,
    obtain ⟨a, ha, rfl⟩ := hsurj y hy,
    simp only [subtype.val_eq_coe, subtype.coe_mk, subtype.mk_eq_mk, set_coe.exists],
    exact ⟨_,ha,rfl⟩},
  haveI := fintype.of_finite s,
  haveI := fintype.of_surjective _ hsurj,
  simp_rw [ncard_eq_to_finset_card] at hst,
  set f'' : ∀ a, a ∈ s.to_finset → β := λ a h, f a (by simpa using h) with hf'',
  exact @finset.inj_on_of_surj_on_of_card_le _ _ _ t.to_finset f'' (by simpa) (by simpa)
    (by convert hst) a₁ a₂ (by simpa) (by simpa) (by simpa),
end

section lattice

lemma ncard_union_add_ncard_inter (s t : set α) [finite s] [finite t] :
  (s ∪ t).ncard + (s ∩ t).ncard = s.ncard + t.ncard :=
begin
  haveI := finite.set.finite_union s t,
  haveI := finite.set.finite_inter_of_left s t,
  haveI := fintype.of_finite s,
  haveI := fintype.of_finite t,
  simp_rw [ncard_eq_to_finset_card, to_finset_union, to_finset_inter],
  convert finset.card_union_add_card_inter _ _,
end

lemma ncard_inter_add_ncard_union (s t : set α) [finite s] [finite t] :
  (s ∩ t).ncard + (s ∪ t).ncard = s.ncard + t.ncard :=
by rw [add_comm, ncard_union_add_ncard_inter]

lemma ncard_union_le (s t : set α) :
  (s ∪ t).ncard ≤ s.ncard + t.ncard :=
begin
  cases (s ∪ t).finite_or_infinite,
  { haveI := h.to_subtype,
    haveI := finite.set.subset _ (subset_union_left s t),
    haveI := finite.set.subset _ (subset_union_right s t),
    haveI := fintype.of_finite s,
    haveI := fintype.of_finite t,
    simp_rw [ncard_eq_to_finset_card, to_finset_union],
    convert finset.card_union_le _ _, },
  convert nat.zero_le _,
  rw h.ncard,
end

lemma ncard_union_eq [finite s] [finite t] (h : disjoint s t) :
  (s ∪ t).ncard = s.ncard + t.ncard :=
begin
  haveI := finite.set.finite_union s t,
  haveI := fintype.of_finite s,
  haveI := fintype.of_finite t,
  simp_rw [ncard_eq_to_finset_card, to_finset_union],
  convert finset.card_union_eq _,
  simpa,
end

lemma ncard_diff_add_ncard_eq_ncard [finite t] (h : s ⊆ t) :
  (t \ s).ncard + s.ncard = t.ncard :=
begin
  have ht := to_finite t,
  haveI := ((to_finite t).subset h).to_subtype,
  haveI := ((to_finite t).diff s).to_subtype,
  haveI := fintype.of_finite s,
  haveI := fintype.of_finite t,
  simp_rw [ncard_eq_to_finset_card],  rw to_finset_diff,
  convert finset.card_sdiff_add_card_eq_card _,
  simpa,
end

lemma ncard_diff [finite t] (h : s ⊆ t) :
  (t \ s).ncard = t.ncard - s.ncard :=
by rw [←ncard_diff_add_ncard_eq_ncard h, add_tsub_cancel_right]

lemma ncard_le_ncard_diff_add_ncard (s t : set α) [finite t] :
  s.ncard ≤ (s \ t).ncard + t.ncard :=
begin
  cases s.finite_or_infinite,
  { haveI := h.to_subtype,
    rw [←diff_inter_self_eq_diff, ←ncard_diff_add_ncard_eq_ncard (inter_subset_right t s),
      add_le_add_iff_left],
    apply ncard_inter_le_ncard_left},
  convert nat.zero_le _,
  rw h.ncard,
end

lemma le_ncard_diff (s t : set α) [finite s] :
  t.ncard - s.ncard ≤ (t \ s).ncard :=
begin
  refine tsub_le_iff_left.mpr _,
  rw add_comm,
  apply ncard_le_ncard_diff_add_ncard,
end

lemma ncard_diff_add_ncard (s t : set α) [finite s] [finite t] :
  (s \ t).ncard + t.ncard = (s ∪ t).ncard :=
begin
  haveI := finite.set.finite_union s t,
  rw [← (by {ext, simp} : (s ∪ t) \ t = s \ t), ncard_diff_add_ncard_eq_ncard],
  apply subset_union_right,
end

lemma diff_nonempty_of_ncard_lt_ncard [finite s] (h : s.ncard < t.ncard) :
  (t \ s).nonempty :=
begin
  rw [set.nonempty_iff_ne_empty, ne.def, diff_eq_empty],
  exact λ h', h.not_le (ncard_le_of_subset h'),
end

lemma exists_mem_not_mem_of_ncard_lt_ncard [finite s] (h : s.ncard < t.ncard) :
  ∃ e, e ∈ t ∧ e ∉ s :=
diff_nonempty_of_ncard_lt_ncard h

@[simp] lemma ncard_inter_add_ncard_diff_eq_ncard (s t : set α) [finite s] [finite t] :
  (s ∩ t).ncard + (s \ t).ncard = s.ncard :=
begin
  convert ncard_diff_add_ncard_eq_ncard (diff_subset s t) using 3,
  rw [sdiff_sdiff_right_self, inf_eq_inter],
end

lemma ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff [finite s] [finite t] :
  s.ncard = t.ncard ↔ (s \ t).ncard = (t \ s).ncard :=
by rw [←ncard_inter_add_ncard_diff_eq_ncard s t, ←ncard_inter_add_ncard_diff_eq_ncard t s,
    inter_comm, add_right_inj]

lemma ncard_le_ncard_iff_ncard_diff_le_ncard_diff [finite s] [finite t] :
  s.ncard ≤ t.ncard ↔ (s \ t).ncard ≤ (t \ s).ncard :=
by rw [←ncard_inter_add_ncard_diff_eq_ncard s t, ←ncard_inter_add_ncard_diff_eq_ncard t s,
     inter_comm, add_le_add_iff_left]

lemma ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff [finite s] [finite t] :
  s.ncard < t.ncard ↔ (s \ t).ncard < (t \ s).ncard :=
by rw [←ncard_inter_add_ncard_diff_eq_ncard s t, ←ncard_inter_add_ncard_diff_eq_ncard t s,
     inter_comm, add_lt_add_iff_left]

end lattice

/-- Given a set `t` and a set `s` inside it, we can shrink `t` to any appropriate size, and keep `s`
    inside it. -/
lemma exists_intermediate_set_ncard (i : ℕ) (h₁ : i + s.ncard ≤ t.ncard) (h₂ : s ⊆ t) :
  ∃ (r : set α), s ⊆ r ∧ r ⊆ t ∧ r.ncard = i + s.ncard :=
begin
  cases t.finite_or_infinite with ht ht,
  { haveI := ht.to_subtype,
    haveI := (ht.subset h₂).to_subtype,
    simp_rw [ncard_eq_to_finset_card] at h₁ ⊢,
    obtain ⟨r', hsr', hr't, hr'⟩ := finset.exists_intermediate_set _ h₁ (by simpa),
    exact ⟨r', by simpa using hsr', by simpa using hr't, by rw [←hr', ncard_coe_finset]⟩},
  rw [ht.ncard] at h₁,
  have h₁' := nat.eq_zero_of_le_zero h₁,
  rw [add_eq_zero_iff] at h₁',
  exact ⟨t, h₂, rfl.subset, by rw [ht.ncard, h₁'.1, h₁'.2]⟩
end

/-- We can shrink `s` to any smaller size. -/
lemma exists_smaller_set (s : set α) (i : ℕ) (h₁ : i ≤ s.ncard) :
  ∃ (t : set α), t ⊆ s ∧ t.ncard = i :=
(exists_intermediate_set_ncard i (by simpa) (empty_subset s)).imp
  (λ t ht, ⟨ht.2.1,by simpa using ht.2.2⟩)

lemma exists_subset_or_subset_of_two_mul_lt_ncard {n : ℕ} (hst : 2 * n < (s ∪ t).ncard) :
  ∃ (r : set α), n < r.ncard ∧ (r ⊆ s ∨ r ⊆ t) :=
begin
  have hfin := (finite_of_ncard_ne_zero ((nat.zero_le _).trans_lt hst).ne.symm),
  haveI := @fintype.of_finite _ (hfin.subset (subset_union_left _ _)).to_subtype,
  haveI := @fintype.of_finite _ (hfin.subset (subset_union_right _ _)).to_subtype,
  rw [ncard_eq_to_finset_card, to_finset_union] at hst,
  obtain ⟨r', hnr', hr'⟩ := finset.exists_subset_or_subset_of_two_mul_lt_card hst,
  exact ⟨r', by simpa , by simpa using hr'⟩,
end

/-! ### Explicit description of a set from its cardinality -/

@[simp] lemma ncard_eq_one : s.ncard = 1 ↔ ∃ a, s = {a} :=
begin
  refine ⟨λ h, _,by {rintro ⟨a,rfl⟩, rw [ncard_singleton]}⟩,
  haveI := (finite_of_ncard_ne_zero (ne_zero_of_eq_one h)).to_subtype,
  rw [ncard_eq_to_finset_card, finset.card_eq_one] at h,
  exact h.imp (λ a ha, by rwa [←to_finset_singleton, to_finset_inj] at ha),
end

lemma exists_eq_insert_iff_ncard [finite s] :
  (∃ a ∉ s, insert a s = t) ↔ s ⊆ t ∧ s.ncard + 1 = t.ncard :=
begin
  split,
  { rintro ⟨a, ha, rfl⟩,
    haveI := fintype.of_finite s,
    haveI := ((to_finite s).insert a).to_subtype,
    simp_rw [ncard_eq_to_finset_card, ←to_finset_subset_to_finset, to_finset_insert],
    convert (@finset.exists_eq_insert_iff _ _ s.to_finset (insert a s.to_finset)).mp _,
    exact ⟨a, by simpa, rfl⟩},
  rintro ⟨hst, h⟩,
  haveI :=
    (finite_of_ncard_ne_zero (calc 0 < s.ncard + 1 : ne_zero.pos _ ... = _ : h).ne.symm).to_subtype,

  simp_rw [ncard_eq_to_finset_card] at h,
  obtain ⟨a,has, ha⟩ := (finset.exists_eq_insert_iff.mpr ⟨by simpa,h⟩),
  haveI := @fintype.of_finite _ ((to_finite s).insert a).to_subtype,
  rw ←to_finset_insert at ha,
  exact ⟨a, by simpa using has, by simpa using ha⟩,
end

lemma ncard_le_one [finite s] :
  s.ncard ≤ 1 ↔ ∀ (a ∈ s) (b ∈ s), a = b :=
by simp_rw [ncard_eq_to_finset_card, finset.card_le_one, mem_to_finset]

lemma ncard_le_one_iff [finite s] :
  s.ncard ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b :=
by { rw ncard_le_one, tauto}

lemma ncard_le_one_iff_subset_singleton [nonempty α] [finite s] :
  s.ncard ≤ 1 ↔ ∃ (x : α), s ⊆ {x} :=
by simp_rw [ncard_eq_to_finset_card, finset.card_le_one_iff_subset_singleton, to_finset_subset,
  finset.coe_singleton]

/-- A `set` of a subsingleton type has cardinality at most one. -/
lemma ncard_le_one_of_subsingleton [subsingleton α] (s : set α) :
  s.ncard ≤ 1 :=
by {rw [ncard_eq_to_finset_card], exact finset.card_le_one_of_subsingleton _}

lemma one_lt_ncard [finite s] :
  1 < s.ncard ↔ ∃ (a ∈ s) (b ∈ s), a ≠ b :=
by simp_rw [ncard_eq_to_finset_card, finset.one_lt_card, mem_to_finset]

lemma one_lt_ncard_iff [finite s] :
  1 < s.ncard ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b :=
by { rw one_lt_ncard, simp only [exists_prop, exists_and_distrib_left] }

lemma two_lt_ncard_iff [finite s] :
  2 < s.ncard ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c :=
by simp_rw [ncard_eq_to_finset_card, finset.two_lt_card_iff, mem_to_finset]

lemma two_lt_card [finite s] : 2 < s.ncard ↔ ∃ (a ∈ s) (b ∈ s) (c ∈ s), a ≠ b ∧ a ≠ c ∧ b ≠ c :=
by simp only [two_lt_ncard_iff, exists_and_distrib_left, exists_prop]

lemma exists_ne_of_one_lt_ncard (hs : 1 < s.ncard) (a : α) : ∃ b, b ∈ s ∧ b ≠ a :=
begin
  haveI := (finite_of_ncard_ne_zero (zero_lt_one.trans hs).ne.symm).to_subtype,
  rw [ncard_eq_to_finset_card] at hs,
  simpa only [mem_to_finset] using finset.exists_ne_of_one_lt_card hs a,
end

lemma eq_insert_of_ncard_eq_succ {n : ℕ} (h : s.ncard = n + 1) :
  ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n :=
begin
  haveI := @fintype.of_finite _ (finite_of_ncard_pos (n.zero_lt_succ.trans_eq h.symm)).to_subtype,
  rw [ncard_eq_to_finset_card, finset.card_eq_succ] at h,
  obtain ⟨a,t,hat,hts,rfl⟩ := h,
  refine ⟨a,t,hat,_,by rw ncard_coe_finset⟩,
  rw [←to_finset_inj],
  convert hts,
  simp only [to_finset_insert, finset.to_finset_coe],
end

lemma ncard_eq_succ [finite s] {n : ℕ} :
  s.ncard = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n :=
begin
  refine ⟨eq_insert_of_ncard_eq_succ, _⟩,
  rintro ⟨a,t,hat,h,rfl⟩,
  haveI := @fintype.of_finite _ ((to_finite s).subset ((subset_insert a t).trans_eq h)).to_subtype,
  rw [← h, ncard_insert_of_not_mem hat],
end

lemma ncard_eq_two :
  s.ncard = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨x,t,hxt,rfl,ht⟩ :=  eq_insert_of_ncard_eq_succ h,
    obtain ⟨y,rfl⟩ := ncard_eq_one.mp ht,
    rw mem_singleton_iff at hxt,
    exact ⟨_,_,hxt,rfl⟩},
  rintro ⟨x,y,hxy,rfl⟩,
  rw [ncard_eq_to_finset_card, finset.card_eq_two],
  exact ⟨x,y,hxy, by {ext, simp}⟩,
end

lemma ncard_eq_three :
  s.ncard = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨x,t,hxt,rfl,ht⟩ :=  eq_insert_of_ncard_eq_succ h,
    obtain ⟨y,z,hyz,rfl⟩ := ncard_eq_two.mp ht,
    rw [mem_insert_iff, mem_singleton_iff, not_or_distrib] at hxt,
    exact ⟨x,y,z,hxt.1,hxt.2,hyz,rfl⟩,
  },
  rintro ⟨x, y, z, xy, xz, yz, rfl⟩,
  rw [ncard_insert_of_not_mem, ncard_insert_of_not_mem, ncard_singleton],
  { rwa mem_singleton_iff},
  rw [mem_insert_iff, mem_singleton_iff],
  tauto,
end

end set
