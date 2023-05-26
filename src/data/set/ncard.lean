/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import data.finite.card
import algebra.big_operators.finprod

/-!
# Noncomputable Set Cardinality

We define the cardinality `set.ncard s` of a set `s` as a natural number. This function is
noncomputable (being defined in terms of `nat.card`) and takes the value `0` if `s` is infinite.

This can be seen as an API for `nat.card α` in the special case where `α` is a subtype arising from
a set. It is intended as an alternative to `finset.card` and `fintype.card`,  both of which contain
data in their definition that can cause awkwardness when using `set.to_finset`.  Using `set.ncard`
allows cardinality computations to avoid `finset`/`fintype` completely, staying in `set` and letting
finiteness be handled explicitly, or (where a `finite α` instance is present and the sets are
in `set α`) via `auto_param`s.

## Main Definitions

* `set.ncard s` is the cardinality of the set `s` as a natural number, provided `s` is finite.
  If `s` is infinite, then `set.ncard s = 0`.
* `to_finite_tac` is a tactic that tries to synthesize an `set.finite s` argument with
  `set.to_finite`. This will work for `s : set α` where there is a `finite α` instance.

## Implementation Notes

The lemmas in this file are very similar to those in `data.finset.card`, but with `set` operations
instead of `finset`; most of the proofs invoke their `finset` analogues. Nearly all the lemmas
require finiteness of one or more of their arguments. We provide this assumption with an
`auto_param` argument of the form `(hs : s.finite . to_finite_tac)`, where `to_finite_tac` will find
a `finite s` term in the cases where `s` is a set in a `finite` type.

Often, where there are two set arguments `s` and `t`, the finiteness of one follows from the other
in the context of the lemma, in which case we only include the ones that are needed, and derive the
other inside the proof. A few of the lemmas, such as `ncard_union_le` do not require finiteness
arguments; they are are true by coincidence due to junk values.
-/

open_locale big_operators

variables {α β : Type*} {s t : set α} {a b x y : α} {f : α → β}

namespace set

/-- The cardinality of `s : set α`. Has the junk value `0` if `s` is infinite -/
noncomputable def ncard (s : set α) := nat.card s

/-- A tactic, for use in `auto_param`s, that finds a `t.finite` term for a set `t`
  whose finiteness can be deduced from typeclasses (eg. in a `finite` type). -/
meta def to_finite_tac : tactic unit := `[exact set.to_finite _]

lemma ncard_def (s : set α) : s.ncard = nat.card s := rfl

lemma ncard_eq_to_finset_card (s : set α) (hs : s.finite . to_finite_tac) :
  s.ncard = hs.to_finset.card :=
by rw [ncard_def, @nat.card_eq_fintype_card _ hs.fintype,
  @finite.card_to_finset _ _ hs.fintype hs]

lemma ncard_le_of_subset (hst : s ⊆ t) (ht : t.finite . to_finite_tac) : s.ncard ≤ t.ncard :=
@finite.card_le_of_embedding _ _ (finite_coe_iff.mpr ht) (set.embedding_of_subset _ _ hst)

lemma ncard_mono [finite α] : @monotone (set α) _ _ _ ncard := λ _ _, ncard_le_of_subset

@[simp] lemma ncard_eq_zero (hs : s.finite . to_finite_tac) : s.ncard = 0 ↔ s = ∅ :=
by simp [ncard_def, @finite.card_eq_zero_iff _ hs.to_subtype]

@[simp] lemma ncard_coe_finset (s : finset α) : (s : set α).ncard = s.card :=
by rw [ncard_eq_to_finset_card, finset.finite_to_set_to_finset]

lemma infinite.ncard (hs : s.infinite) : s.ncard = 0 :=
@nat.card_eq_zero_of_infinite _ hs.to_subtype

lemma ncard_univ (α : Type*) : (univ : set α).ncard = nat.card α :=
begin
  cases finite_or_infinite α with h h,
  { haveI := @fintype.of_finite α h,
    rw [ncard_eq_to_finset_card, finite.to_finset_univ, finset.card_univ,
      nat.card_eq_fintype_card]},
  rw [(@infinite_univ _ h).ncard, @nat.card_eq_zero_of_infinite _ h],
end

@[simp] lemma ncard_empty (α : Type*) : (∅ : set α).ncard = 0 := by simp only [ncard_eq_zero]

lemma ncard_pos (hs : s.finite . to_finite_tac) : 0 < s.ncard ↔ s.nonempty :=
by rw [pos_iff_ne_zero, ne.def, ncard_eq_zero hs, nonempty_iff_ne_empty]

lemma ncard_ne_zero_of_mem (h : a ∈ s) (hs : s.finite . to_finite_tac) : s.ncard ≠ 0 :=
((ncard_pos hs).mpr ⟨a,h⟩).ne.symm

lemma finite_of_ncard_ne_zero (hs : s.ncard ≠ 0) : s.finite :=
s.finite_or_infinite.elim id (λ h, (hs h.ncard).elim)

lemma finite_of_ncard_pos (hs : 0 < s.ncard) : s.finite :=
finite_of_ncard_ne_zero hs.ne.symm

lemma nonempty_of_ncard_ne_zero (hs : s.ncard ≠ 0) : s.nonempty :=
by {rw nonempty_iff_ne_empty, rintro rfl, simpa using hs}

@[simp] lemma ncard_singleton (a : α) : ({a} : set α).ncard = 1 := by simp [ncard_eq_to_finset_card]

lemma ncard_singleton_inter : ({a} ∩ s).ncard ≤ 1 :=
begin
  classical,
  rw [←inter_self {a}, inter_assoc, ncard_eq_to_finset_card,
    finite.to_finset_inter, finite.to_finset_singleton],
  { apply finset.card_singleton_inter},
  all_goals {apply to_finite},
end

section insert_erase

@[simp] lemma ncard_insert_of_not_mem (h : a ∉ s) (hs : s.finite . to_finite_tac) :
  (insert a s).ncard = s.ncard + 1 :=
begin
  classical,
  haveI := hs.fintype,
  rw [ncard_eq_to_finset_card, ncard_eq_to_finset_card, finite.to_finset_insert,
    finset.card_insert_of_not_mem],
  rwa [finite.mem_to_finset],
end

lemma ncard_insert_of_mem (h : a ∈ s) : ncard (insert a s) = s.ncard := by rw insert_eq_of_mem h

lemma ncard_insert_le (a : α) (s : set α) : (insert a s).ncard ≤ s.ncard + 1 :=
begin
  classical,
  obtain (hs | hs) := s.finite_or_infinite,
  { exact (em (a ∈ s)).elim (λ h, (ncard_insert_of_mem h).trans_le (nat.le_succ _))
      (λ h, by rw ncard_insert_of_not_mem h hs)},
  rw (hs.mono (subset_insert a s)).ncard,
  exact nat.zero_le _,
end

lemma ncard_insert_eq_ite [decidable (a ∈ s)] (hs : s.finite . to_finite_tac) :
  ncard (insert a s) = if a ∈ s then s.ncard else s.ncard + 1 :=
begin
  by_cases h : a ∈ s,
  { rw [ncard_insert_of_mem h, if_pos h] },
  { rw [ncard_insert_of_not_mem h hs, if_neg h] }
end

lemma ncard_le_ncard_insert (a : α) (s : set α) [decidable (a ∈ s)] :
  s.ncard ≤ (insert a s).ncard :=
begin
  classical,
  refine s.finite_or_infinite.elim (λ h, _) (λ h, by { rw h.ncard, exact nat.zero_le _ }),
  rw [@ncard_insert_eq_ite _ _ _ ‹_› h],
  split_ifs; simp,
end

lemma ncard_pair (h : a ≠ b) : ({a, b} : set α).ncard = 2 :=
by {rw [ncard_insert_of_not_mem, ncard_singleton], simpa}

lemma ncard_diff_singleton_add_one (h : a ∈ s) (hs : s.finite . to_finite_tac) :
  (s \ {a}).ncard + 1 = s.ncard :=
begin
  have h' : a ∉ s \ {a}, by {rw [mem_diff_singleton], tauto},
  rw ←ncard_insert_of_not_mem h' (hs.diff {a}),
  congr',
  simpa,
end

lemma ncard_diff_singleton_of_mem (h : a ∈ s) (hs : s.finite . to_finite_tac) :
  (s \ {a}).ncard = s.ncard - 1 :=
eq_tsub_of_add_eq (ncard_diff_singleton_add_one h hs)

lemma ncard_diff_singleton_lt_of_mem (h : a ∈ s) (hs : s.finite . to_finite_tac) :
  (s \ {a}).ncard < s.ncard :=
by {rw [←ncard_diff_singleton_add_one h hs], apply lt_add_one}

lemma ncard_diff_singleton_le (s : set α) (a : α) : (s \ {a}).ncard ≤ s.ncard :=
begin
  obtain (hs | hs) := s.finite_or_infinite,
  { apply ncard_le_of_subset (diff_subset _ _) hs},
  convert zero_le _,
  exact (hs.diff (by simp : set.finite {a})).ncard,
end

lemma pred_ncard_le_ncard_diff_singleton (s : set α) (a : α) : s.ncard - 1 ≤ (s \ {a}).ncard :=
begin
  cases s.finite_or_infinite with hs hs,
  { by_cases h : a ∈ s,
    { rw ncard_diff_singleton_of_mem h hs, },
    rw diff_singleton_eq_self h,
    apply nat.pred_le},
  convert nat.zero_le _,
  rw hs.ncard,
end

lemma ncard_exchange (ha : a ∉ s) (hb : b ∈ s) : (insert a (s \ {b})).ncard = s.ncard :=
begin
  cases s.finite_or_infinite with h h,
  { haveI := h.to_subtype,
    rw [ncard_insert_of_not_mem, ncard_diff_singleton_add_one hb],
    simpa only [mem_diff, not_and] using ha},
  rw [((h.diff (set.to_finite {b})).mono (subset_insert _ _)).ncard, h.ncard],
end

lemma ncard_exchange' (ha : a ∉ s) (hb : b ∈ s) :
  ((insert a s) \ {b}).ncard = s.ncard :=
by rw [←ncard_exchange ha hb, ←singleton_union, ←singleton_union, union_diff_distrib,
  @diff_singleton_eq_self _ b {a} (λ h, ha (by rwa ← mem_singleton_iff.mp h) )]

end insert_erase

lemma ncard_image_le (hs : s.finite . to_finite_tac) : (f '' s).ncard ≤ s.ncard :=
begin
  classical,
  rw ncard_eq_to_finset_card s hs,
  haveI := hs.fintype,
  convert @finset.card_image_le _ _ s.to_finset f _,
  rw [ncard_eq_to_finset_card, finite.to_finset_image _ hs],
  { congr', rw [←finset.coe_inj, finite.coe_to_finset, coe_to_finset]},
  { apply_instance},
  rw [←finset.coe_inj, finite.coe_to_finset, coe_to_finset],
end

lemma ncard_image_of_inj_on (H : set.inj_on f s) : (f '' s).ncard = s.ncard :=
begin
  cases s.finite_or_infinite,
  { haveI := @fintype.of_finite s h.to_subtype,
    haveI := @fintype.of_finite _ (h.image f).to_subtype,
    convert card_image_of_inj_on H; simp [ncard_def]},
  rw [h.ncard, ((infinite_image_iff H).mpr h).ncard],
end

lemma inj_on_of_ncard_image_eq (h : (f '' s).ncard = s.ncard)
  (hs : s.finite . to_finite_tac) :
  set.inj_on f s :=
begin
  classical,
  haveI := hs.fintype,
  haveI := ((to_finite s).image f).fintype,
  simp_rw ncard_eq_to_finset_card at h,
  rw ← coe_to_finset s,
  apply finset.inj_on_of_card_image_eq,
  convert h,
  ext,
  simp,
end

lemma ncard_image_iff (hs : s.finite . to_finite_tac) : (f '' s).ncard = s.ncard ↔ set.inj_on f s :=
⟨λ h, inj_on_of_ncard_image_eq h hs, ncard_image_of_inj_on⟩

lemma ncard_image_of_injective (s : set α) (H : f.injective) : (f '' s).ncard = s.ncard :=
ncard_image_of_inj_on $ λ x _ y _ h, H h

lemma ncard_preimage_of_injective_subset_range {s : set β} (H : f.injective)
  (hs : s ⊆ set.range f) : (f ⁻¹' s).ncard = s.ncard :=
by rw [←ncard_image_of_injective _ H, image_preimage_eq_iff.mpr hs]

lemma fiber_ncard_ne_zero_iff_mem_image {y : β} (hs : s.finite . to_finite_tac) :
  {x ∈ s | f x = y}.ncard ≠ 0 ↔ y ∈ f '' s :=
begin
  refine ⟨nonempty_of_ncard_ne_zero, _⟩,
  rintros ⟨z,hz,rfl⟩,
  exact @ncard_ne_zero_of_mem _ {x ∈ s | f x = f z} z (mem_sep hz rfl)
    (hs.subset (sep_subset _ _)),
end

@[simp] lemma ncard_map (f : α ↪ β) : (f '' s).ncard = s.ncard :=
ncard_image_of_injective _ f.injective

@[simp] lemma ncard_subtype (P : α → Prop) (s : set α) :
  {x : subtype P | (x : α) ∈ s}.ncard = (s ∩ (set_of P)).ncard :=
begin
  convert (ncard_image_of_injective _ (@subtype.coe_injective _ P)).symm,
  ext, rw inter_comm, simp,
end

@[simp] lemma nat.card_coe_set_eq (s : set α) : nat.card s = s.ncard :=
begin
  convert (ncard_image_of_injective univ subtype.coe_injective).symm using 1,
  { rw ncard_univ, refl },
  simp,
end

lemma ncard_inter_le_ncard_left (s t : set α) (hs : s.finite . to_finite_tac) :
  (s ∩ t).ncard ≤ s.ncard :=
ncard_le_of_subset (inter_subset_left _ _) hs

lemma ncard_inter_le_ncard_right (s t : set α) (ht : t.finite . to_finite_tac) :
  (s ∩ t).ncard ≤ t.ncard :=
ncard_le_of_subset (inter_subset_right _ _) ht

lemma eq_of_subset_of_ncard_le (h : s ⊆ t) (h' : t.ncard ≤ s.ncard)
  (ht : t.finite . to_finite_tac) :
  s = t :=
begin
  haveI := ht.fintype,
  haveI := (ht.subset h).fintype,
  rw ←@to_finset_inj,
  apply finset.eq_of_subset_of_card_le,
  { simpa, },
  rw [ncard_eq_to_finset_card _ ht, ncard_eq_to_finset_card _ (ht.subset h)] at h',
  convert h',
end

lemma subset_iff_eq_of_ncard_le (h : t.ncard ≤ s.ncard) (ht : t.finite . to_finite_tac) :
  s ⊆ t ↔ s = t :=
⟨λ hst, eq_of_subset_of_ncard_le hst h ht, eq.subset'⟩

lemma map_eq_of_subset {f : α ↪ α} (h : f '' s ⊆ s) (hs : s.finite . to_finite_tac) : f '' s = s :=
eq_of_subset_of_ncard_le h (ncard_map _).ge hs

lemma sep_of_ncard_eq {P : α → Prop} (h : {x ∈ s | P x}.ncard = s.ncard) (ha : a ∈ s)
  (hs : s.finite . to_finite_tac) :
P a :=
sep_eq_self_iff_mem_true.mp (eq_of_subset_of_ncard_le (by simp) h.symm.le hs) _ ha

lemma ncard_lt_ncard (h : s ⊂ t) (ht : t.finite . to_finite_tac) : s.ncard < t.ncard :=
begin
  rw [ncard_eq_to_finset_card _ (ht.subset h.subset), ncard_eq_to_finset_card t ht],
  refine finset.card_lt_card _,
  rwa [finite.to_finset_ssubset_to_finset],
end

lemma ncard_strict_mono [finite α] : @strict_mono (set α) _ _ _ ncard :=
λ _ _ h, ncard_lt_ncard h

lemma ncard_eq_of_bijective {n : ℕ} (f : ∀ i, i < n → α)
  (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a)
  (hf' : ∀ i (h : i < n), f i h ∈ s)
  (f_inj : ∀ i j (hi : i < n) (hj : j < n), f i hi = f j hj → i = j)
  (hs : s.finite . to_finite_tac) :
  s.ncard = n :=
begin
  rw ncard_eq_to_finset_card _ hs,
  apply finset.card_eq_of_bijective,
  all_goals {simpa},
end

lemma ncard_congr {t : set β} (f : Π a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
  (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b)
  (hs : s.finite . to_finite_tac) :
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
  haveI := hs.to_subtype,
  haveI := @fintype.of_finite _ (finite.of_bijective hbij),
  haveI := fintype.of_finite s,
  convert fintype.card_of_bijective hbij,
  rw [ncard_def, nat.card_eq_fintype_card],
  rw [ncard_def, nat.card_eq_fintype_card],
end

lemma ncard_le_ncard_of_inj_on {t : set β} (f : α → β) (hf : ∀ a ∈ s, f a ∈ t)
  (f_inj : inj_on f s) (ht : t.finite . to_finite_tac) :
  s.ncard ≤ t.ncard :=
begin
  cases s.finite_or_infinite,
  { haveI := h.to_subtype,
    rw [ncard_eq_to_finset_card _ ht, ncard_eq_to_finset_card _ (to_finite s)],
    exact finset.card_le_card_of_inj_on f (by simpa) (by simpa)},
  convert nat.zero_le _,
  rw h.ncard,
end

lemma exists_ne_map_eq_of_ncard_lt_of_maps_to {t : set β} (hc : t.ncard < s.ncard)
  {f : α → β} (hf : ∀ a ∈ s, f a ∈ t) (ht : t.finite . to_finite_tac) :
  ∃ (x ∈ s) (y ∈ s), x ≠ y ∧ f x = f y :=
begin
  by_contra h',
  simp only [ne.def, exists_prop, not_exists, not_and, not_imp_not] at h',
  exact (ncard_le_ncard_of_inj_on f hf h' ht).not_lt hc,
end

lemma le_ncard_of_inj_on_range {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
  (f_inj : ∀ (i < n) (j < n), f i = f j → i = j) (hs : s.finite . to_finite_tac):
  n ≤ s.ncard :=
by {rw ncard_eq_to_finset_card _ hs, apply finset.le_card_of_inj_on_range; simpa}

lemma surj_on_of_inj_on_of_ncard_le {t : set β} (f : Π a ∈ s, β)
  (hf : ∀ a ha, f a ha ∈ t) (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂)
  (hst : t.ncard ≤ s.ncard) (ht : t.finite . to_finite_tac) :
  ∀ b ∈ t, ∃ a ha, b = f a ha :=
begin
  intros b hb,
  set f' : s → t := λ x, ⟨f x.1 x.2, hf _ _⟩ with hf',
  have finj: f'.injective,
  { rintros ⟨x,hx⟩ ⟨y,hy⟩ hxy,
    simp only [hf', subtype.val_eq_coe, subtype.coe_mk, subtype.mk_eq_mk] at hxy ⊢,
    apply hinj _ _ hx hy hxy},
  haveI := ht.fintype,
  haveI := fintype.of_injective f' finj,
  simp_rw [ncard_eq_to_finset_card] at hst,
  set f'' : ∀ a, a ∈ s.to_finset → β := λ a h, f a (by simpa using h) with hf'',
  convert @finset.surj_on_of_inj_on_of_card_le _ _ _ t.to_finset f'' (by simpa) (by simpa)
    (by convert hst) b (by simpa),
  simp,
end

lemma inj_on_of_surj_on_of_ncard_le {t : set β} (f : Π a ∈ s, β)
  (hf : ∀ a ha, f a ha ∈ t) (hsurj : ∀ b ∈ t, ∃ a ha, b = f a ha) (hst : s.ncard ≤ t.ncard)
  ⦃a₁ a₂⦄ (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s) (ha₁a₂: f a₁ ha₁ = f a₂ ha₂)
  (hs : s.finite . to_finite_tac) :
  a₁ = a₂ :=
begin
  classical,
   set f' : s → t := λ x, ⟨f x.1 x.2, hf _ _⟩ with hf',
  have hsurj : f'.surjective,
  { rintro ⟨y,hy⟩,
    obtain ⟨a, ha, rfl⟩ := hsurj y hy,
    simp only [subtype.val_eq_coe, subtype.coe_mk, subtype.mk_eq_mk, set_coe.exists],
    exact ⟨_,ha,rfl⟩},
  haveI := hs.fintype,
  haveI := fintype.of_surjective _ hsurj,
  simp_rw [ncard_eq_to_finset_card] at hst,
  set f'' : ∀ a, a ∈ s.to_finset → β := λ a h, f a (by simpa using h) with hf'',
  exact @finset.inj_on_of_surj_on_of_card_le _ _ _ t.to_finset f'' (by simpa) (by simpa)
    (by convert hst) a₁ a₂ (by simpa) (by simpa) (by simpa),
end

section lattice

lemma ncard_union_add_ncard_inter (s t : set α) (hs : s.finite . to_finite_tac)
  (ht : t.finite . to_finite_tac) :
  (s ∪ t).ncard + (s ∩ t).ncard = s.ncard + t.ncard :=
begin
  classical,
  have hu := hs.union ht,
  have hi := (hs.subset (inter_subset_left s t)),
  rw [ncard_eq_to_finset_card _ hs, ncard_eq_to_finset_card _ ht, ncard_eq_to_finset_card _ hu,
    ncard_eq_to_finset_card _ hi, finite.to_finset_union, finite.to_finset_inter],
  { exact finset.card_union_add_card_inter _ _},
end

lemma ncard_inter_add_ncard_union (s t : set α) (hs : s.finite . to_finite_tac)
  (ht : t.finite . to_finite_tac) :
  (s ∩ t).ncard + (s ∪ t).ncard = s.ncard + t.ncard :=
by rw [add_comm, ncard_union_add_ncard_inter _ _ hs ht]

lemma ncard_union_le (s t : set α) : (s ∪ t).ncard ≤ s.ncard + t.ncard :=
begin
  classical,
  cases (s ∪ t).finite_or_infinite,
  { have hs := h.subset (subset_union_left s t),
    have ht := h.subset (subset_union_right s t),
    rw [ncard_eq_to_finset_card _ hs, ncard_eq_to_finset_card _ ht, ncard_eq_to_finset_card _ h,
      finite.to_finset_union],
    exact finset.card_union_le _ _},
  convert nat.zero_le _,
  rw h.ncard,
end

lemma ncard_union_eq (h : disjoint s t) (hs : s.finite . to_finite_tac)
  (ht : t.finite . to_finite_tac) :
  (s ∪ t).ncard = s.ncard + t.ncard :=
begin
  classical,
  rw [ncard_eq_to_finset_card _ hs, ncard_eq_to_finset_card _ ht,
    ncard_eq_to_finset_card _ (hs.union ht),finite.to_finset_union],
  refine finset.card_union_eq _,
  rwa [finite.disjoint_to_finset],
end

lemma ncard_diff_add_ncard_eq_ncard (h : s ⊆ t) (ht : t.finite . to_finite_tac) :
  (t \ s).ncard + s.ncard = t.ncard :=
begin
  classical,
  rw [ncard_eq_to_finset_card _ ht, ncard_eq_to_finset_card _ (ht.subset h),
      ncard_eq_to_finset_card _ (ht.diff s), finite.to_finset_diff],
  refine finset.card_sdiff_add_card_eq_card _,
  rwa finite.to_finset_subset_to_finset,
end

lemma ncard_diff (h : s ⊆ t) (ht : t.finite . to_finite_tac) :
  (t \ s).ncard = t.ncard - s.ncard :=
by rw [←ncard_diff_add_ncard_eq_ncard h ht, add_tsub_cancel_right]

lemma ncard_le_ncard_diff_add_ncard (s t : set α) (ht : t.finite . to_finite_tac) :
  s.ncard ≤ (s \ t).ncard + t.ncard :=
begin
  cases s.finite_or_infinite,
  { rw [←diff_inter_self_eq_diff, ←ncard_diff_add_ncard_eq_ncard (inter_subset_right t s) h,
      add_le_add_iff_left],
    apply ncard_inter_le_ncard_left _ _ ht,},
  convert nat.zero_le _,
  rw h.ncard,
end

lemma le_ncard_diff (s t : set α) (hs : s.finite . to_finite_tac) :
  t.ncard - s.ncard ≤ (t \ s).ncard :=
begin
  refine tsub_le_iff_left.mpr _,
  rw add_comm,
  apply ncard_le_ncard_diff_add_ncard _ _ hs,
end

lemma ncard_diff_add_ncard (s t : set α) (hs : s.finite . to_finite_tac)
  (ht : t.finite . to_finite_tac) :
  (s \ t).ncard + t.ncard = (s ∪ t).ncard :=
by rw [←union_diff_right,ncard_diff_add_ncard_eq_ncard (subset_union_right s t) (hs.union ht)]

lemma diff_nonempty_of_ncard_lt_ncard (h : s.ncard < t.ncard) (hs : s.finite . to_finite_tac) :
  (t \ s).nonempty :=
begin
  rw [set.nonempty_iff_ne_empty, ne.def, diff_eq_empty],
  exact λ h', h.not_le (ncard_le_of_subset h' hs),
end

lemma exists_mem_not_mem_of_ncard_lt_ncard (h : s.ncard < t.ncard) (hs : s.finite . to_finite_tac) :
  ∃ e, e ∈ t ∧ e ∉ s :=
diff_nonempty_of_ncard_lt_ncard h hs

@[simp] lemma ncard_inter_add_ncard_diff_eq_ncard (s t : set α)
  (hs : s.finite . to_finite_tac) :
  (s ∩ t).ncard + (s \ t).ncard = s.ncard :=
by rw [←ncard_diff_add_ncard_eq_ncard (diff_subset s t) hs, sdiff_sdiff_right_self, inf_eq_inter]

lemma ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff (hs : s.finite . to_finite_tac)
  (ht : t.finite . to_finite_tac) :
  s.ncard = t.ncard ↔ (s \ t).ncard = (t \ s).ncard :=
by rw [←ncard_inter_add_ncard_diff_eq_ncard s t hs, ←ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_right_inj]

lemma ncard_le_ncard_iff_ncard_diff_le_ncard_diff (hs : s.finite . to_finite_tac)
  (ht : t.finite . to_finite_tac)  :
  s.ncard ≤ t.ncard ↔ (s \ t).ncard ≤ (t \ s).ncard :=
by rw [←ncard_inter_add_ncard_diff_eq_ncard s t hs, ←ncard_inter_add_ncard_diff_eq_ncard t s ht,
     inter_comm, add_le_add_iff_left]

lemma ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff (hs : s.finite . to_finite_tac)
  (ht : t.finite . to_finite_tac)  :
  s.ncard < t.ncard ↔ (s \ t).ncard < (t \ s).ncard :=
by rw [←ncard_inter_add_ncard_diff_eq_ncard s t hs, ←ncard_inter_add_ncard_diff_eq_ncard t s ht,
     inter_comm, add_lt_add_iff_left]

lemma ncard_add_ncard_compl (s : set α) (hs : s.finite . to_finite_tac)
  (hsc : sᶜ.finite . to_finite_tac) :
  s.ncard + sᶜ.ncard = nat.card α :=
by rw [←ncard_univ, ←ncard_union_eq (@disjoint_compl_right _ _ s) hs hsc, union_compl_self]

end lattice

/-- Given a set `t` and a set `s` inside it, we can shrink `t` to any appropriate size, and keep `s`
    inside it. -/
lemma exists_intermediate_set (i : ℕ) (h₁ : i + s.ncard ≤ t.ncard) (h₂ : s ⊆ t) :
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

lemma exists_intermediate_set' {m : ℕ} (hs : s.ncard ≤ m) (ht : m ≤ t.ncard) (h : s ⊆ t) :
  ∃ (r : set α), s ⊆ r ∧ r ⊆ t ∧ r.ncard = m :=
begin
  obtain ⟨r,hsr,hrt,hc⟩ :=
    exists_intermediate_set (m - s.ncard) (by rwa [tsub_add_cancel_of_le hs]) h,
  rw tsub_add_cancel_of_le hs at hc,
  exact ⟨r,hsr,hrt,hc⟩,
end

/-- We can shrink `s` to any smaller size. -/
lemma exists_smaller_set (s : set α) (i : ℕ) (h₁ : i ≤ s.ncard) :
  ∃ (t : set α), t ⊆ s ∧ t.ncard = i :=
(exists_intermediate_set i (by simpa) (empty_subset s)).imp (λ t ht, ⟨ht.2.1,by simpa using ht.2.2⟩)

lemma infinite.exists_subset_ncard_eq {s : set α} (hs : s.infinite) (k : ℕ) :
  ∃ t, t ⊆ s ∧ t.finite ∧ t.ncard = k :=
begin
  haveI := hs.to_subtype,
  obtain ⟨t', -, rfl⟩ := @infinite.exists_subset_card_eq s univ infinite_univ k,
  refine ⟨coe '' (t' : set s), by simp, finite.image _ (by simp), _⟩,
  rw [ncard_image_of_injective _ subtype.coe_injective],
  simp,
end

lemma infinite.exists_supset_ncard_eq {s t : set α} (ht : t.infinite) (hst : s ⊆ t)
  (hs : s.finite) {k : ℕ} (hsk : s.ncard ≤ k) :
  ∃ s', s ⊆ s' ∧ s' ⊆ t ∧ s'.ncard = k :=
begin
  obtain ⟨s₁, hs₁, hs₁fin, hs₁card⟩ := (ht.diff hs).exists_subset_ncard_eq (k - s.ncard),
  refine ⟨s ∪ s₁, subset_union_left _ _, union_subset hst (hs₁.trans (diff_subset _ _)), _⟩,
  rwa [ncard_union_eq (disjoint_of_subset_right hs₁ disjoint_sdiff_right) hs hs₁fin, hs₁card,
    add_tsub_cancel_of_le],
end

lemma exists_subset_or_subset_of_two_mul_lt_ncard {n : ℕ}
  (hst : 2 * n < (s ∪ t).ncard) :
  ∃ (r : set α), n < r.ncard ∧ (r ⊆ s ∨ r ⊆ t) :=
begin
  classical,
  have hu := (finite_of_ncard_ne_zero ((nat.zero_le _).trans_lt hst).ne.symm),
  rw [ncard_eq_to_finset_card _ hu, finite.to_finset_union
    (hu.subset (subset_union_left _ _)) (hu.subset (subset_union_right _ _))] at hst,
  obtain ⟨r', hnr', hr'⟩ := finset.exists_subset_or_subset_of_two_mul_lt_card hst,
  exact ⟨r', by simpa , by simpa using hr'⟩,
end

/-! ### Explicit description of a set from its cardinality -/

@[simp] lemma ncard_eq_one : s.ncard = 1 ↔ ∃ a, s = {a} :=
begin
  refine ⟨λ h, _,by {rintro ⟨a,rfl⟩, rw [ncard_singleton]}⟩,
  haveI := (finite_of_ncard_ne_zero (ne_zero_of_eq_one h)).to_subtype,
  rw [ncard_eq_to_finset_card, finset.card_eq_one] at h,
  exact h.imp (λ a ha, by rwa [←finite.to_finset_singleton, finite.to_finset_inj] at ha),
end

lemma exists_eq_insert_iff_ncard (hs : s.finite . to_finite_tac) :
  (∃ a ∉ s, insert a s = t) ↔ s ⊆ t ∧ s.ncard + 1 = t.ncard :=
begin
  classical,
  split,
  { rintro ⟨a, ha, rfl⟩,
    rw [ncard_eq_to_finset_card _ hs, ncard_eq_to_finset_card _ (hs.insert a),
      finite.to_finset_insert, ←@finite.to_finset_subset_to_finset _ _ _ hs (hs.insert a),
      finite.to_finset_insert],
    refine (@finset.exists_eq_insert_iff _ _ hs.to_finset (insert a hs.to_finset)).mp _,
    exact ⟨a, by rwa finite.mem_to_finset, rfl⟩},
  rintro ⟨hst, h⟩,
  have ht := @finite_of_ncard_pos _ t (by {rw ←h, apply nat.zero_lt_succ}),

  rw [ncard_eq_to_finset_card _ hs, ncard_eq_to_finset_card _ ht] at h,
  obtain ⟨a,has, ha⟩ := (finset.exists_eq_insert_iff.mpr ⟨by {simpa},h⟩),
  have hsa := hs.insert a,
  rw ←finite.to_finset_insert at ha,
  exact ⟨a, by {rwa finite.mem_to_finset at has}, by {rwa ←@finite.to_finset_inj _ _ _ hsa ht}⟩,
end

lemma ncard_le_one (hs : s.finite . to_finite_tac) :
  s.ncard ≤ 1 ↔ ∀ (a ∈ s) (b ∈ s), a = b :=
by simp_rw [ncard_eq_to_finset_card _ hs, finset.card_le_one, finite.mem_to_finset]

lemma ncard_le_one_iff (hs : s.finite . to_finite_tac) :
  s.ncard ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b :=
by { rw ncard_le_one hs, tauto}

lemma ncard_le_one_iff_eq (hs : s.finite . to_finite_tac) :
  s.ncard ≤ 1 ↔ s = ∅ ∨ ∃ a, s = {a} :=
begin
  obtain (rfl | ⟨x,hx⟩) := s.eq_empty_or_nonempty,
  { exact iff_of_true (by simp) (or.inl rfl), },
  rw [ncard_le_one_iff hs],
  refine ⟨λ h, or.inr ⟨x,(singleton_subset_iff.mpr hx).antisymm' (λ y hy, h hy hx)⟩, _⟩,
  rintro (rfl | ⟨a,rfl⟩),
  { exact (not_mem_empty _ hx).elim },
  simp_rw mem_singleton_iff at hx ⊢, subst hx,
  exact λ a b h h', h.trans h'.symm,
end

lemma ncard_le_one_iff_subset_singleton [nonempty α] (hs : s.finite . to_finite_tac) :
  s.ncard ≤ 1 ↔ ∃ (x : α), s ⊆ {x} :=
by simp_rw [ncard_eq_to_finset_card _ hs, finset.card_le_one_iff_subset_singleton,
  finite.to_finset_subset, finset.coe_singleton]

/-- A `set` of a subsingleton type has cardinality at most one. -/
lemma ncard_le_one_of_subsingleton [subsingleton α] (s : set α) :
  s.ncard ≤ 1 :=
by {rw [ncard_eq_to_finset_card], exact finset.card_le_one_of_subsingleton _}

lemma one_lt_ncard (hs : s.finite . to_finite_tac) :
  1 < s.ncard ↔ ∃ (a ∈ s) (b ∈ s), a ≠ b :=
by simp_rw [ncard_eq_to_finset_card _ hs, finset.one_lt_card, finite.mem_to_finset]

lemma one_lt_ncard_iff (hs : s.finite . to_finite_tac) :
  1 < s.ncard ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b :=
by { rw one_lt_ncard hs, simp only [exists_prop, exists_and_distrib_left] }

lemma two_lt_ncard_iff (hs : s.finite . to_finite_tac) :
  2 < s.ncard ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c :=
by simp_rw [ncard_eq_to_finset_card _ hs, finset.two_lt_card_iff, finite.mem_to_finset]

lemma two_lt_card (hs : s.finite . to_finite_tac) :
  2 < s.ncard ↔ ∃ (a ∈ s) (b ∈ s) (c ∈ s), a ≠ b ∧ a ≠ c ∧ b ≠ c :=
by simp only [two_lt_ncard_iff hs, exists_and_distrib_left, exists_prop]

lemma exists_ne_of_one_lt_ncard (hs : 1 < s.ncard) (a : α) : ∃ b, b ∈ s ∧ b ≠ a :=
begin
  haveI := (finite_of_ncard_ne_zero (zero_lt_one.trans hs).ne.symm).to_subtype,
  rw [ncard_eq_to_finset_card] at hs,
  simpa only [finite.mem_to_finset] using finset.exists_ne_of_one_lt_card hs a,
end

lemma eq_insert_of_ncard_eq_succ {n : ℕ} (h : s.ncard = n + 1) :
  ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n :=
begin
  classical,
  haveI := @fintype.of_finite _ (finite_of_ncard_pos (n.zero_lt_succ.trans_eq h.symm)).to_subtype,
  rw [ncard_eq_to_finset_card, finset.card_eq_succ] at h,
  obtain ⟨a,t,hat,hts,rfl⟩ := h,
  refine ⟨a,t,hat,_,by rw ncard_coe_finset⟩,
  rw [←to_finset_inj],
  convert hts,
  simp only [to_finset_insert, finset.to_finset_coe],
end

lemma ncard_eq_succ {n : ℕ} (hs : s.finite . to_finite_tac) :
  s.ncard = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n :=
begin
  classical,
  refine ⟨eq_insert_of_ncard_eq_succ, _⟩,
  rintro ⟨a,t,hat,h,rfl⟩,
  rw [← h, ncard_insert_of_not_mem hat (hs.subset ((subset_insert a t).trans_eq h))]
end

lemma ncard_eq_two : s.ncard = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} :=
begin
  classical,
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
  classical,
  refine ⟨λ h, _, _⟩,
  { obtain ⟨x,t,hxt,rfl,ht⟩ :=  eq_insert_of_ncard_eq_succ h,
    obtain ⟨y,z,hyz,rfl⟩ := ncard_eq_two.mp ht,
    rw [mem_insert_iff, mem_singleton_iff, not_or_distrib] at hxt,
    exact ⟨x,y,z,hxt.1,hxt.2,hyz,rfl⟩},
  rintro ⟨x, y, z, xy, xz, yz, rfl⟩,
  rw [ncard_insert_of_not_mem, ncard_insert_of_not_mem, ncard_singleton],
  { rwa mem_singleton_iff},
  rw [mem_insert_iff, mem_singleton_iff],
  tauto,
end

end set
