import tactic
import .num_lemmas .set .single finsum.fin_api  .induction

open_locale classical big_operators
noncomputable theory

universes u v w

/-!
This file contains an API for `size`, which is the noncomputable function assigning each finite
set to its size as an integer, and each infinite set to zero. Also `type_size` is defined similarly
for types. Most lemmas are only true in a finite setting, and have two versions, one with explicit
finiteness assumptions, and one in which they are derived from a `fintype` instance . Lemmas of the
former type are usually less useful for us, and go in the `finite` namespace.
-/

section defs

/-- The size of a set, as an integer. Zero if the set is infinite -/
def size {α : Type*} (s : set α) : ℤ := (fincard s)

/-- The size of a type, as an integer. Zero if the type is infinite -/
def type_size (α : Type* ) : ℤ := size (set.univ : set α)

end defs

/-! Basic lemmas about size.  -/

section basic

variables {α : Type*} {s t : set α} {e f : α}

lemma size_def (s : set α) :
  size s = fincard s :=
rfl

lemma type_size_eq (α : Type*) : type_size α = size (set.univ : set α) := rfl

lemma type_size_eq_fincard_t (α : Type*) : type_size α = fincard_t α :=
by {rw [type_size, size_def], norm_num, refl,  }

lemma type_size_coe_set_eq_size (s : set α) :
  type_size s = size s :=
by rw [type_size_eq_fincard_t, size, fincard_t_subtype_eq_fincard]

lemma type_size_type_of_eq_size_set_of (P : α → Prop):
  type_size {x // P x} = size {x | P x} :=
type_size_coe_set_eq_size P

@[simp] lemma size_empty (α : Type*) : size (∅ : set α) = 0 :=
by simp [size]

@[simp] lemma size_singleton (e : α) : size ({e} : set α) = 1 :=
by simp [size]

lemma size_nonneg (s : set α) : 0 ≤ size s :=
by {simp only [size], norm_cast, apply zero_le}

lemma type_size_nonneg (α : Type*) : 0 ≤ type_size α :=
size_nonneg _

lemma size_zero_of_infinite (hs : s.infinite) :
  size s = 0 :=
by rw [size, fincard_of_infinite hs, int.coe_nat_zero]

lemma finite_of_size_pos (hs : 0 < size s) :
  s.finite :=
by {rw size at hs, norm_num at hs, exact finite_of_fincard_pos hs, }

/-- a positive type size gives rise to a fintype -/
def fintype_of_type_size_pos {α : Type*} (hα : 0 < type_size α) :
  fintype α :=
set.fintype_of_univ_finite (by {rw [type_size_eq] at hα, exact finite_of_size_pos hα,})

lemma nonempty_of_size_pos (hs : 0 < size s) :
  s.nonempty :=
by {rw ← set.ne_empty_iff_nonempty, rintro rfl, linarith [size_empty α], }

lemma nonempty_of_type_size_pos (hα : 0 < type_size α):
  nonempty α :=
by {rw set.nonempty_iff_univ_nonempty, rw type_size_eq at hα, exact nonempty_of_size_pos hα, }

lemma contains_singleton {s : set α} : s.nonempty → (∃ t, t ⊆ s ∧ size t = 1) :=
λ ⟨e,he⟩, ⟨{e},⟨set.singleton_subset_iff.mpr he, size_singleton e⟩⟩

lemma exists_mem_of_size_pos (h : 0 < size s) :
  ∃ e, e ∈ s :=
(ne_empty_iff_has_mem.mp (λ hs, lt_irrefl _ (by {rwa [hs, size_empty] at h})))

@[simp] lemma finsum_ones_eq_size (s : set α) :
  ∑ᶠ x in s, (1 : ℤ) = size s :=
by {rw [size, fincard, nat.coe_int_distrib_finsum_in], refl}

@[simp] lemma finsum_ones_eq_type_size (α : Type*) :
  ∑ᶠ (x : α), (1 : ℤ) = type_size α :=
by {rw [finsum_eq_finsum_in_univ, finsum_ones_eq_size], refl}

lemma size_set_of_eq_size_subtype (P : α → Prop):
  size {x | P x} = type_size {x // P x} :=
by rw [← finsum_ones_eq_size, ← finsum_ones_eq_type_size, ← finsum_subtype_eq_finsum_in_set_of]

lemma size_set_of_push (P Q : α → Prop) :
  size {x : {y // P y} | Q (x : α)} = size { x | P x ∧ Q x } :=
by {rw [← finsum_ones_eq_size, ← finsum_ones_eq_size],
    convert finsum_set_subtype_eq_finsum_set (1 : α → ℤ) P Q,  }


end basic

/-! The lemmas in this section are true without any finiteness assumptions -/
section general

variables {α : Type*} {s t : set α} {e f : α}

lemma size_one_iff_eq_singleton :
  size s = 1 ↔ ∃ e, s = {e} :=
begin
  refine ⟨λ h, _, λ h, _⟩, swap,
    cases h with e he, rw he, apply size_singleton,

  have hs := finite_of_size_pos (by linarith : 0 < size s),
  obtain ⟨e,he⟩ := exists_mem_of_size_pos (by linarith : 0 < size s),
  use e,
  ext,
  simp only [set.mem_singleton_iff],
  refine ⟨λ h', _, λ h', by {rwa ← h' at he}⟩,
  rw ← finsum_ones_eq_size at h,
  have hs' := finsum_in_subset_le_finsum_in_of_nonneg hs
    (_ : {e,x} ⊆ s) (λ x hx, (by norm_num: (0 : ℤ ) ≤ 1)),
  { by_contra hxe,
    rw [finsum_pair (ne.symm hxe), h, add_le_iff_nonpos_right] at hs',
    norm_num at hs'},
  rw ← set.singleton_subset_iff at he h',
  convert set.union_subset he h',
end

lemma eq_of_mems_size_one (hs : size s = 1) (he : e ∈ s) (hf : f ∈ s):
  e = f :=
begin
  obtain ⟨x, rfl⟩ := size_one_iff_eq_singleton.mp hs,
  rw set.mem_singleton_iff at he hf,
  rw [he,hf],
end

lemma size_pair (hef : e ≠ f) :
  size ({e,f} : set α) = 2 :=
by {rw [← finsum_ones_eq_size, finsum_pair hef], refl}


end general

/-! Lemmas about the relationship between size and finsumming ones -/

section sums

variables {α : Type*}

@[simp] lemma int.finsum_const_eq_mul_type_size (α : Type*) (b : ℤ) :
  ∑ᶠ (x : α), b = b * type_size α :=
by rw [← mul_one b, ← finsum_ones_eq_type_size, ← mul_distrib_finsum, mul_one]

@[simp] lemma int.finsum_in_const_eq_mul_size (s : set α) (b : ℤ) :
  ∑ᶠ x in s, b = b * size s :=
by rw [← mul_one b, ← finsum_ones_eq_size, ← mul_distrib_finsum_in, mul_one]

lemma finite.sum_size_fiber_eq_size {ι : Type*} {s : set α} (hs : s.finite) (f : α → ι) :
  ∑ᶠ (i : ι), size {a ∈ s | f a = i} = size s :=
by simp_rw [size_def, ← nat.coe_int_distrib_finsum, sum_fincard_fiber_eq_fincard f hs]

lemma size_set_subtype_eq_size_set (P Q : α → Prop) :
  size {x : {y // P y} | Q (coe x)} = size { x | P x ∧ Q x } :=
by {simp_rw ← finsum_ones_eq_size, apply finsum_set_subtype_eq_finsum_set (1 : α → ℤ)}

end sums

/-!
This section contains lemmas that require finiteness of sets to be true. These versions
all have explicit set.finite assumptions; the versions that use an instance are later.
-/

section finite

variables {α : Type*} {s t : set α} {e f : α}

open set

namespace set.finite

lemma size_modular (s t : set α) (hs : s.finite) (ht : t.finite) :
  size (s ∪ t) + size (s ∩ t) = size s + size t :=
by {simp_rw size, norm_cast, apply fincard_modular; assumption}

lemma size_union (s t : set α) (hs : s.finite) (ht : t.finite) :
  size (s ∪ t) = size s + size t - size (s ∩ t) :=
by linarith [size_modular s t hs ht]

lemma size_monotone (ht : t.finite) (hst : s ⊆ t) : size s ≤ size t :=
begin
  have hs := subset ht hst,
  have := size_modular s (t \ s) hs (ht.diff s),
  rw [union_diff_of_subset hst, inter_diff] at this,
  linarith [size_nonneg (t \ s), size_empty α],
end

lemma ssubset_size (hs : s.finite) (ht : t.finite) (hst : s ⊆ t) (hst' : size s < size t) :
  s ⊂ t :=
by {rw set.ssubset_iff_subset_ne, from ⟨hst, λ hn, by {rw hn at hst', exact lt_irrefl _ hst'}⟩}

lemma size_subadditive (hs : s.finite) (ht : t.finite) : size (s ∪ t) ≤ size s + size t :=
  by linarith [size_modular s t hs ht, size_nonneg (s ∩ t)]

lemma compl_inter_size (s t : set α) (ht : t.finite) :
  size (s ∩ t) + size (sᶜ ∩ t) = size t :=
by {rw [←size_modular, ←inter_distrib_right, union_compl_self, univ_inter,
  ←inter_distrib_inter_left, inter_compl_self, empty_inter, size_empty, add_zero];
  exact inter_right (by assumption) _, }

lemma compl_inter_size_subset (ht : t.finite) (hst : s ⊆ t) :
  size (sᶜ ∩ t) = size t - size s :=
by {have := compl_inter_size s t ht, rw subset_iff_inter_eq_left.mp hst at this, linarith}

lemma diff_size (ht : t.finite) (hst : s ⊆ t) : size (t \ s) = size t - size s :=
by rw [diff_eq, inter_comm, compl_inter_size_subset ht hst]

lemma size_diff_le_size (s t : set α) (hs : s.finite) : size (s \ t) ≤ size s :=
  size_monotone hs (diff_subset _ _)
-- the above lemma is also true if just `s ∩ t` is finite

lemma size_union_of_inter_empty (hs : s.finite) (ht : t.finite) (hst : s ∩ t = ∅) :
  size (s ∪ t) = size s + size t :=
by {have := size_modular s t hs ht, rw [hst, size_empty] at this, linarith}

lemma size_union_of_disjoint (hs : s.finite) (ht : t.finite) (hst : disjoint s t) :
  size (s ∪ t) = size s + size t :=
size_union_of_inter_empty hs ht (disjoint_iff_inter_eq_empty.mp hst)

lemma size_modular_diff (s t : set α) (hs : s.finite) (ht : t.finite) :
  size (s ∪ t) = size (s \ t) + size (t \ s) + size (s ∩ t) :=
begin
  rw [←size_union_of_inter_empty _ _ (inter_diffs_eq_empty s t)],
  { have := (symm_diff_alt s t),
    unfold symm_diff at this,
    rw this,
    linarith [diff_size (union hs ht) (inter_subset_union s t)]},
  repeat {apply diff, assumption},
end

lemma size_induced_partition (s t : set α) (hs : s.finite)  :
  size s = size (s ∩ t) + size (s \ t) :=
begin
  nth_rewrite 0 ←diff_union s t,
  refine size_union_of_inter_empty (inter_left hs _) (diff hs _) (partition_inter _ _),
end

lemma size_induced_partition_inter (s t : set α) (hs : s.finite) :
  size s = size (s ∩ t) + size (s ∩ tᶜ) :=
by {rw ←diff_eq, apply size_induced_partition _ _ hs, }

lemma size_mono_inter_left (s t : set α) (hs : s.finite) : size (s ∩ t) ≤ size s :=
size_monotone hs (inter_subset_left _ _)

lemma size_mono_inter_right (s t : set α) (ht : t.finite) : size (s ∩ t) ≤ size t :=
size_monotone ht (inter_subset_right _ _)

lemma size_mono_union_left (s t : set α) (ht : t.finite) : size s ≤ size (s ∪ t)  :=
begin
  by_cases hs : s.finite,
  apply size_monotone (union hs ht) (subset_union_left _ _),
  rw [size_zero_of_infinite hs, size_zero_of_infinite],
  exact infinite_mono (subset_union_left _ _) hs,
end

lemma size_mono_union_right (s t : set α) (hs : s.finite) : size t ≤ size (s ∪ t) :=
by {rw union_comm, apply size_mono_union_left _ _ hs}

lemma empty_of_size_zero (hs : s.finite) (hsize : size s = 0) : s = ∅ :=
begin
  rw eq_empty_iff_forall_not_mem, intros x hx,
  have h' := size_monotone hs (singleton_subset_iff.mpr hx),
  rw [hsize, size_singleton] at h',
  linarith,
end

lemma size_zero_iff_empty (hs : s.finite) : (size s = 0) ↔ (s = ∅) :=
  by {split, apply empty_of_size_zero hs, intros h, rw h, exact size_empty α}

lemma size_le_zero_iff_eq_empty (hs : s.finite) :
  size s ≤ 0 ↔ s = ∅ :=
by {rw [← size_zero_iff_empty hs], exact ⟨λ h, le_antisymm h (size_nonneg _), λ h, le_of_eq h⟩}

lemma size_nonempty (hs : s.finite) (hne : s.nonempty) : 0 < size s  :=
begin
  suffices h' : 0 ≠ size s, exact lt_of_le_of_ne (size_nonneg _) h',
  rw [←set.ne_empty_iff_nonempty] at hne,
  exact λ h, hne (empty_of_size_zero hs h.symm),
end

lemma nonempty_iff_size_pos (hs : s.finite) : s.nonempty ↔ 0 < size s :=
begin
  refine ⟨λ h, size_nonempty hs h, λ h, _⟩,
  rw ←set.ne_empty_iff_nonempty,
  exact λ h', by {rw [h', size_empty] at h, from lt_irrefl 0 h},
end

lemma one_le_size_iff_nonempty (hs : s.finite) : s.nonempty ↔ 1 ≤ size s :=
  nonempty_iff_size_pos hs


lemma one_le_size_of_nonempty (hs : s.nonempty) (hs' : s.finite) : 1 ≤ size s :=
  (one_le_size_iff_nonempty hs').mp hs

lemma size_strict_monotone (ht : t.finite) (hst : s ⊂ t) : size s < size t :=
begin
  rw [size_induced_partition t s ht, inter_comm, subset_iff_inter_eq_left.mp hst.1],
  linarith [size_nonempty (diff ht _) (ssubset_diff_nonempty hst)],
end

lemma eq_of_eq_size_subset (ht : t.finite) (hst : s ⊆ t) (hsize : size s = size t) :
  s = t :=
begin
  unfreezingI {rcases subset_ssubset_or_eq hst with (hst' | rfl)},
    swap, refl,
  have := size_strict_monotone ht hst', rw hsize at this,
  exact false.elim (lt_irrefl _ this),
end

lemma eq_of_eq_size_subset_iff (ht : t.finite) (hst : s ⊆ t) :
  ((size s = size t) ↔ s = t) :=
⟨λ h, eq_of_eq_size_subset ht hst h, λ h, by {rw h}⟩

lemma eq_of_le_size_subset (ht : t.finite) (hst : s ⊆ t) (hsize : size t ≤ size s) :
  s = t :=
by {apply eq_of_eq_size_subset ht hst, exact le_antisymm (size_monotone ht hst) hsize}

lemma size_eq_of_supset (ht : t.finite) (hst : s ⊆ t) (hsize : size t ≤ size s) :
  size s = size t :=
by linarith [size_monotone ht hst]

lemma size_pos_iff_has_mem (hs : s.finite) :
  0 < size s ↔ ∃ e, e ∈ s :=
by rw [← nonempty_iff_size_pos hs, set.nonempty_def]

lemma one_le_size_iff_has_mem (hs : s.finite) :
  1 ≤ size s ↔ ∃ e, e ∈ s :=
by {convert size_pos_iff_has_mem hs}

lemma size_zero_iff_has_no_mem (hs : s.finite) :
  size s = 0 ↔ ¬ ∃ e, e ∈ s :=
begin
  rw [iff.comm, ←not_iff, ←(size_pos_iff_has_mem hs), not_iff],
  refine ⟨λ h, _, λ h, by linarith ⟩ ,
  linarith [size_nonneg s, not_lt.mp h],
end

lemma size_le_zero_iff_has_no_mem (hs : s.finite) :
  size s ≤ 0 ↔ ¬ ∃ e, e ∈ s :=
by {rw ←(size_zero_iff_has_no_mem hs), split, { intro, linarith [size_nonneg s]}, intro h, rw h}

lemma mem_diff_of_size_lt (hs : s.finite) (hst : size s < size t) :
  ∃ (e : α), e ∈ t ∧ e ∉ s :=
begin
  suffices h' : 0 < size (t \ s),
    obtain ⟨e, he⟩ := exists_mem_of_size_pos h', tauto,
  have ht := finite_of_size_pos (lt_of_le_of_lt (size_nonneg _) hst),
  linarith [size_induced_partition t s ht, size_mono_inter_right t s hs],
end

lemma size_union_singleton_compl (hs : s.finite) (hes : e ∈ sᶜ) :
  size (s ∪ {e}) = size s + 1 :=
begin
  have := size_modular s {e} hs (finite_singleton e),
  rwa [inter_comm s, nonmem_disjoint (by rwa ←mem_compl_iff), size_singleton,
  size_empty, add_zero] at this,
end

lemma size_union_nonmem_singleton (hs : s.finite) (he : e ∉ s) :
  size (s ∪ {e}) = size s + 1 :=
by {apply size_union_singleton_compl hs, rwa ←mem_compl_iff at he, }

lemma size_insert_nonmem (hs : s.finite) (he : e ∉ s) :
  size (has_insert.insert e s) = size s + 1 :=
by {convert size_union_nonmem_singleton hs he, rw union_singleton}

lemma size_remove_mem (hs : s.finite) (he : e ∈ s) :
  size (s \ {e}) = size s - 1 :=
begin
  have h' : has_insert.insert e (s \ {e}) = s,
  { ext, simp, rintro rfl, assumption},
  nth_rewrite 1 ← h',
  rw [size_insert_nonmem],
    ring,
  apply diff hs _,
  simp,
end

lemma has_sub_one_size_ssubset_of_ne_empty (hs : s.finite) (hne : s ≠ ∅) :
  ∃ t, t ⊂ s ∧ size t = size s - 1 :=
by {cases ne_empty_has_mem hne with e he,
exact ⟨s \ {e}, ⟨ssubset_of_remove_mem he, size_remove_mem hs he⟩ ⟩}

lemma has_sub_one_size_ssubset_of_nonempty (hs : s.finite) (hne : s.nonempty) :
  ∃ t, t ⊂ s ∧ size t = size s - 1 :=
has_sub_one_size_ssubset_of_ne_empty hs (ne_empty_iff_nonempty.mpr hne)

lemma ne_univ_has_add_one_size_ssupset (hs : s.finite) (hne : s ≠ univ) :
  ∃ t, s ⊂ t ∧ size t = size s + 1 :=
let ⟨e,he⟩ := ne_univ_iff_has_nonmem.mp hne in
  ⟨has_insert.insert e s, ssubset_insert he, size_insert_nonmem hs he⟩

lemma ne_univ_has_add_one_size_ssupset_element (hs : s.finite) (hne : s ≠ univ) :
  ∃ e, s ⊂ s ∪ {e} ∧ size (s ∪ {e}) = size s + 1 :=
let ⟨e,he⟩ := ne_univ_iff_has_nonmem.mp hne in
   ⟨e, by {rw union_singleton, exact ssubset_insert he}, size_union_nonmem_singleton hs he⟩

lemma eq_or_exists_mem_diff_of_size_eq (ht : t.finite) (hst : size s = size t) :
  s = t ∨ ∃ e, e ∈ s \ t :=
begin
  by_contra h, rw not_or_distrib at h, cases h with h1 h2,
  rw ←ne_empty_iff_has_mem at h2, push_neg at h2,
  rw diff_empty_iff_subset at h2,
  refine h1 (eq_of_eq_size_subset ht h2 hst),
end

lemma size_le_one_iff_empty_or_singleton (hs : s.finite) :
  size s ≤ 1 ↔ s = ∅ ∨ ∃ e, s = {e} :=
begin
  refine ⟨λ h, _, λ h, _⟩, swap,
  { unfreezingI {rcases h with (rfl | ⟨e, rfl⟩)};
  simp only [size_singleton, size_empty], norm_num,},
  by_cases h' : size s ≤ 0,
  { left, rw ←size_zero_iff_empty hs, linarith [size_nonneg s],},
  right, rw ←size_one_iff_eq_singleton,
  exact le_antisymm h (by linarith),
end

lemma two_le_size_iff_has_distinct (hs : s.finite) :
  2 ≤ size s ↔ ∃ e f ∈ s, e ≠ f :=
begin
  split,
  { intro h,
    obtain ⟨e,he⟩ := @exists_mem_of_size_pos _ s (by linarith),
    obtain ⟨f,hf⟩ := @exists_mem_of_size_pos _ (s \ {e}) (by linarith [size_remove_mem hs he]),
    refine ⟨e,f,he,mem_of_mem_of_subset hf (diff_subset _ _), _⟩,
    rintro rfl, simpa using hf,},
  rintro ⟨e,f,he,hf,hef⟩,
  rw ← size_pair hef,
  apply size_monotone hs (pair_subset_iff.mpr ⟨he, hf⟩),
end

lemma size_le_one_iff_mem_unique (hs : s.finite) :
  size s ≤ 1 ↔ ∀ e f ∈ s, e = f :=
begin
  split,
  { rw [size_le_one_iff_empty_or_singleton hs],
    unfreezingI {rintros (rfl | ⟨e,rfl⟩)},
      simp [mem_singleton_iff],
    simp only [mem_singleton_iff],
    unfreezingI {rintros e f rfl rfl},
    refl,},
  refine λ h, by_contra (λ hn, _),
  rw [not_le] at hn, replace hn := int.add_one_le_of_lt hn, norm_num at hn,
  rw two_le_size_iff_has_distinct hs at hn,
  obtain ⟨e,f,he,hf,hef⟩ := hn,
  exact hef (h e f he hf),
end

variables {k : set (set α)}

lemma size_sUnion (hk : k.finite) (hk' : ∀ s ∈ k, set.finite s) (hdisj : pairwise_disjoint k) :
  size (⋃₀ k) = ∑ᶠ s in k, size s :=
by {convert finsum_in_sUnion' (1 : α → ℤ) hk hk' hdisj; {simp_rw ← finsum_ones_eq_size, refl}}

lemma size_collection_le_size_union (hk : ∀ s ∈ k, set.finite s)
(hk' : ∀ s ∈ k, set.nonempty s) (hdisj : pairwise_disjoint k):
  (size k ≤ size (⋃₀ k)) :=
begin
  by_cases hk'' : k.finite, swap,
  { convert size_nonneg _, rw size_zero_of_infinite hk''},
  rw [size_sUnion hk'' hk hdisj, ← finsum_ones_eq_size],
  refine finsum_in_le_finsum_in hk'' (λ x hx, _),
  rw ← (one_le_size_iff_nonempty (hk x hx)),
  exact hk' x hx,
end

lemma singletons_of_size_collection_eq_size_union (hk : k.finite) (hk' : ∀ s ∈ k, set.finite s)
(hk'' : ∀ s ∈ k, set.nonempty s) (hdisj : pairwise_disjoint k) (hsize : size k = size (⋃₀ k)):
  ∀ s ∈ k, size s = 1 :=
begin
  rw [size_sUnion hk hk' hdisj, ← finsum_ones_eq_size] at hsize,
  conv in (_ = _) {rw eq_comm},
  convert (finsum_in_eq_finsum_in_iff_of_le hk (λ x hx, _)).mp hsize,
  apply one_le_size_of_nonempty (hk'' _ hx) (hk' _ hx),
end

lemma size_collection_eq_size_union_iff (hk : k.finite) (hk' : ∀ s ∈ k, set.finite s)
(hk'' : ∀ s ∈ k, set.nonempty s) (hdisj : pairwise_disjoint k) :
  size k = size (⋃₀ k) ↔ ∀ s ∈ k, size s = 1 :=
begin
  refine ⟨λ h, singletons_of_size_collection_eq_size_union hk hk' hk'' hdisj h, λ h, _⟩,
  rw [size_sUnion hk hk' hdisj, ← finsum_ones_eq_size, eq_comm],
  exact finsum_in_eq_of_eq h,
end



end set.finite

end finite

/-! Lemmas that don't need any finiteness assumptions. Some are proved by splitting into
finite and infinite cases, which is why these lemmas need to appear after the previous
section.  -/
section general

variables {α : Type*} {s t : set α} {e f : α}

open set

lemma compl_nonempty_of_size_lt_type_size (hs : size s < type_size α):
  sᶜ.nonempty :=
begin
  rw type_size_eq at hs,
  refine nonempty_compl.mpr (λ h, lt_irrefl (size s) (by {rwa ← h at hs})),
end

lemma size_union_singleton_ub :
  size (s ∪ {e}) ≤ size s + 1 :=
begin
  by_cases hs : s.finite,
    linarith [size_nonneg (s ∩ {e}),
      finite.size_modular s {e} hs (finite_singleton e),
      size_singleton e],
  rw [size_zero_of_infinite (infinite_mono (subset_union_left s {e}) hs)],
  linarith [size_nonneg s],
end

lemma size_insert_ub :
  size (insert e s) ≤ size s + 1 :=
by {rw ← union_singleton, apply size_union_singleton_ub, }

lemma single_subset' (hs : s.nonempty) :
  (∃ t t', t ∩ t' = ∅ ∧ t ∪ t' = s ∧ size t = 1) :=
begin
  obtain ⟨t,ht⟩ := contains_singleton hs,
  refine ⟨t, s \ t, set.inter_diff _ _,  _, ht.2⟩,
  rw [set.union_diff_self, set.subset_iff_union_eq_left.mp ht.1],
end

lemma single_subset (hs : s.nonempty) :
  (∃ t t', disjoint t t' ∧ t ∪ t' = s ∧ size t = 1) :=
by {simp_rw set.disjoint_iff_inter_eq_empty, exact single_subset' hs}

lemma size_remove_union_singleton (he : e ∈ s) (hf : f ∉ s) :
  size ((s \ {e}) ∪ {f}) = size s :=
begin
  by_cases hs : s.finite,
  { have h1 := hs.size_remove_mem he,
    have h2 := finite.size_union_nonmem_singleton
      (hs.diff _)
      (nonmem_diff_of_nonmem {e} hf),
    linarith},
  rw [size_zero_of_infinite hs, size_zero_of_infinite _],
  apply infinite_of_union,
  exact infinite_of_finite_diff (finite_singleton e) hs,
end

lemma size_union_singleton_remove (he : e ∈ s) (hf : f ∉ s) :
  size ((s ∪ {f}) \ {e}) = size s :=
begin
  convert size_remove_union_singleton he hf,
  rw [union_diff_distrib],
  convert rfl,
  rw remove_nonmem,
  simp only [mem_singleton_iff],
  rintro rfl,
  exact hf he,
end

lemma exchange_pair_sizes (hst : size s = size t) (he : e ∈ s \ t) (hf : f ∈ t \ s) :
  size (s \ {e} ∪ {f}) = size (t \ {f} ∪ {e}) :=
begin
  rw mem_diff_iff at he hf,
  rwa [size_remove_union_singleton hf.1 he.2, size_remove_union_singleton he.1 hf.2],
end

lemma eq_of_pair_size_one (h : size ({e,f} : set α) = 1) :
  e = f :=
by_contra (λ hn, by {rw size_pair hn at h, norm_num at h})

lemma size_eq_one_iff_nonempty_unique_mem :
  size s = 1 ↔ s.nonempty ∧ ∀ x y ∈ s, x = y :=
begin
  rw size_one_iff_eq_singleton,
  split, { rintros ⟨e,rfl⟩, tidy, }, rintros ⟨⟨e,he⟩, h⟩, use e, tidy,
end

lemma size_eq_two_iff_pair {s : set α} :
  size s = 2 ↔ ∃ (e f : α), e ≠ f ∧ s = {e,f} :=
begin
  refine ⟨λ h, _, λ h, _⟩, swap,
  { rcases h with ⟨e,f,hef,rfl⟩, apply size_pair hef},
  by_cases hs : s.finite,
  { obtain ⟨e,he⟩ := exists_mem_of_size_pos (by {rw h, norm_num} : 0 < size s),
    obtain ⟨f,hf⟩ := exists_mem_of_size_pos
      (by {rw [finite.size_remove_mem hs he,h], norm_num } : 0 < size (s \ {e})),
    refine ⟨e,f,ne.symm (ne_of_mem_diff hf), _⟩,
    rw eq_comm, apply finite.eq_of_eq_size_subset hs,
    { rw ←union_singletons_eq_pair,
      apply union_subset (singleton_subset_iff.mpr he),
      simp only [set.mem_diff, set.mem_singleton_iff] at hf,
      exact singleton_subset_iff.mpr hf.1, },
    rwa [eq_comm, size_pair  (ne.symm (ne_of_mem_diff hf))]},
  rw size_zero_of_infinite hs at h,
  norm_num at h,
end

lemma size_pair_lb (e f : α) :
  1 ≤ size ({e,f} : set α) :=
by {rcases em (e = f) with (rfl | hef), simp, rw size_pair hef, norm_num}

lemma size_pair_ub (e f : α) :
  size ({e,f} : set α) ≤ 2 :=
begin
  rcases em (e = f) with (rfl | hef),
  { simp only [pair_eq_singleton, size_singleton], norm_num},
  rw size_pair hef,
end

lemma has_distinct_of_two_le_size (hs : 2 ≤ size s):
  ∃ e f ∈ s, e ≠ f :=
(finite.two_le_size_iff_has_distinct (finite_of_size_pos (by linarith))).mp hs

lemma has_distinct_of_one_lt_size (hs : 1 < size s):
  ∃ e f ∈ s, e ≠ f :=
(finite.two_le_size_iff_has_distinct (finite_of_size_pos (by linarith))).mp hs

lemma has_subset_of_size {n : ℤ} (hn : 0 ≤ n) (hnx : n ≤ size t) :
  ∃ s ⊆ t, size s = n :=
begin
  rcases eq_or_lt_of_le hn with (rfl | hn'),
    exact ⟨∅, empty_subset _, size_empty _⟩,
  have hfin := finite_of_size_pos (lt_of_lt_of_le hn' hnx), clear hn',
  revert t, revert n,
  refine nonneg_int_induction _
    (λ _ _ _, ⟨∅, empty_subset _, size_empty _⟩)
    (λ n hn ih t ht ht', _),
  obtain ⟨e,he⟩ := exists_mem_of_size_pos (by linarith : 0 < size t),
  obtain ⟨s, hst, hs⟩ := @ih (t \ {e}) _ (finite.diff ht' _), swap,
  { rw finite.size_remove_mem ht' he, exact le_sub_iff_add_le.mpr ht },
  refine ⟨has_insert.insert e s, λ x, _, _⟩,
  { simp only [mem_insert_iff],
    rintros (rfl | hxs), assumption,
    exact mem_of_mem_of_subset hxs (subset.trans hst (diff_subset _ _)),  },
  rw finite.size_insert_nonmem (finite.subset ht' (subset.trans hst (diff_subset _ _))),
    simpa,
  exact nonmem_of_nonmem_supset (nonmem_removal _ _) hst,
end

lemma has_set_of_size {n : ℤ} (h : 0 ≤ n) (h' : n ≤ type_size α) :
  ∃ (Y : set α), size Y = n :=
by {rw type_size_eq at h', obtain ⟨Y,-,hY⟩ := has_subset_of_size h h', tauto}

lemma has_subset_of_size_of_infinite {n : ℤ} (hn : 0 ≤ n) (ht : t.infinite) :
  ∃ s ⊆ t, size s = n :=
begin
  revert n,
  refine nonneg_int_induction _ ⟨∅, empty_subset _, size_empty _⟩ _,
  rintros n hn ⟨s, hs, hs'⟩,
  by_cases hf : s.finite,
  { obtain ⟨e, he⟩ := set.infinite.nonempty (set.infinite_of_finite_diff hf ht),
    refine ⟨s ∪ {e}, union_singleton_subset_of_subset_mem hs (mem_of_mem_diff he), _⟩,
    rw ← hs', refine finite.size_union_nonmem_singleton hf (not_mem_of_mem_diff he)},
  obtain ⟨e,he⟩ := set.infinite.nonempty ht,
  refine ⟨{e}, singleton_subset_iff.mpr he, _⟩,
  rw [size_singleton, ← hs', size_zero_of_infinite hf],
  refl,
end

lemma has_distinct_mems_of_infinite (ht : t.infinite) :
  ∃ e f ∈ t, e ≠ f :=
begin
  obtain ⟨s,hst, hs⟩ := has_subset_of_size_of_infinite (by norm_num : (0 : ℤ) ≤ 2) ht,
  obtain ⟨e, f, hef, rfl⟩ := size_eq_two_iff_pair.mp hs,
  refine ⟨e,f,_,_,hef⟩,
  { rw [← singleton_subset_iff], apply subset.trans (singleton_subset_pair_left _ _) hst},
  rw [← singleton_subset_iff], apply subset.trans (singleton_subset_pair_right _ _) hst,
end



end general


/-!
This section (nearly) contains only copies of lemmas above, but with the finiteness assumptions
wrapped in a `fintype` instance, as well as a couple of lemmas about type sizes which need
`fintype` for the statement to even be sensible. All lemmas fail without finiteness, and
nearly all are proved by just grabbing finiteness assumptions from the instance and invoking
the versions with explicit assumptions.
-/

section fintype

open set

variables {α β : Type*} [fintype α] [fintype β] {s t : set α} {e f : α}

lemma size_monotone (hst : s ⊆ t) :
  size s ≤ size t :=
by {apply finite.size_monotone _ hst, apply finite.of_fintype, }

lemma size_le_type_size (s : set α):
  size s ≤ type_size α :=
size_monotone (subset_univ _)

lemma sum_size_fiber_eq_size {ι : Type*} (s : set α) (f : α → ι) :
  ∑ᶠ (i : ι), size {a ∈ s | f a = i} = size s :=
by simp_rw [size_def, ← nat.coe_int_distrib_finsum, fin.sum_fincard_fiber_eq_fincard s f]

lemma size_modular (s t : set α) :
  size (s ∪ t) + size (s ∩ t) = size s + size t :=
by {apply finite.size_modular; apply finite.of_fintype, }

lemma compl_size (s : set α) :
  size sᶜ = size (univ : set α) - size s :=
begin
  have := size_modular s sᶜ,
  simp only [add_zero, size_empty, union_compl_self, inter_compl_self] at this,
  rw this,
  ring,
end

lemma size_compl (s : set α) :
  size s = size (univ : set α) - size sᶜ :=
by linarith [compl_size s]

lemma size_union (s t : set α) :
  size (s ∪ t) = size s + size t - size (s ∩ t) :=
by {apply finite.size_union; apply finite.of_fintype,}

lemma ssubset_size (hst : s ⊆ t) (hst' : size s < size t) :
  s ⊂ t :=
by {apply finite.ssubset_size _ _ hst hst'; apply finite.of_fintype,  }

lemma size_subadditive (s t : set α) : size (s ∪ t) ≤ size s + size t :=
by {apply finite.size_subadditive; apply finite.of_fintype }

lemma compl_inter_size (s t : set α) : size (s ∩ t) + size (sᶜ ∩ t) = size t :=
by {apply finite.compl_inter_size, apply finite.of_fintype,}

lemma compl_inter_size_subset (hst : s ⊆ t) :
  size (sᶜ ∩ t) = size t - size s :=
by {apply finite.compl_inter_size_subset _ hst, apply finite.of_fintype, }

lemma diff_size (hst : s ⊆ t) : size (t \ s) = size t - size s :=
by {apply finite.diff_size _ hst, apply finite.of_fintype }

lemma size_diff_le_size (s t : set α) : size (s \ t) ≤ size s :=
by {apply finite.size_diff_le_size, apply finite.of_fintype}

lemma size_union_of_inter_empty (hst : s ∩ t = ∅) :
  size (s ∪ t) = size s + size t :=
by {apply finite.size_union_of_inter_empty _ _ hst ; apply finite.of_fintype}

lemma size_union_of_disjoint (hst : disjoint s t) :
  size (s ∪ t) = size s + size t :=
by {apply finite.size_union_of_disjoint _ _ hst ; apply finite.of_fintype}

lemma size_modular_diff (s t : set α) :
  size (s ∪ t) = size (s \ t) + size (t \ s) + size (s ∩ t) :=
by {apply finite.size_modular_diff; apply finite.of_fintype }

lemma size_induced_partition (s t : set α) :
  size s = size (s ∩ t) + size (s \ t) :=
by {apply finite.size_induced_partition, apply finite.of_fintype}

lemma size_induced_partition_inter (s t : set α) :
  size s = size (s ∩ t) + size (s ∩ tᶜ) :=
by {apply finite.size_induced_partition, apply finite.of_fintype}

lemma size_mono_inter_left (s t : set α) : size (s ∩ t) ≤ size s :=
by {apply finite.size_mono_inter_left, apply finite.of_fintype}

lemma size_mono_inter_right (s t : set α) : size (s ∩ t) ≤ size t :=
by {apply finite.size_mono_inter_right, apply finite.of_fintype}

lemma size_mono_union_left (s t : set α) : size s ≤ size (s ∪ t)  :=
by {apply finite.size_mono_union_left, apply finite.of_fintype}

lemma size_mono_union_right (s t : set α) : size t ≤ size (s ∪ t) :=
by {apply finite.size_mono_union_right, apply finite.of_fintype}

lemma empty_of_size_zero (hsize : size s = 0) : s = ∅ :=
by {apply finite.empty_of_size_zero _ hsize, apply finite.of_fintype, }

@[simp] lemma size_zero_iff_empty : (size s = 0) ↔ (s = ∅) :=
by {apply finite.size_zero_iff_empty, apply finite.of_fintype, }

@[simp] lemma size_le_zero_iff_eq_empty : size s ≤ 0 ↔ s = ∅ :=
by {apply finite.size_le_zero_iff_eq_empty, apply finite.of_fintype, }

lemma size_nonempty (hne : s.nonempty) : 0 < size s  :=
by {apply finite.size_nonempty _ hne, apply finite.of_fintype, }

lemma nonempty_iff_size_pos : s.nonempty ↔ 0 < size s :=
by {apply finite.nonempty_iff_size_pos, apply finite.of_fintype, }

lemma one_le_size_iff_nonempty : s.nonempty ↔ 1 ≤ size s :=
nonempty_iff_size_pos

lemma one_le_size_univ_of_nonempty (hα : nonempty α) : 1 ≤ size (univ : set α) :=
by rwa [nonempty_iff_univ_nonempty, one_le_size_iff_nonempty] at hα

lemma one_le_type_size_of_nonempty (hα: nonempty α) : 1 ≤ type_size α  :=
one_le_size_univ_of_nonempty hα

lemma size_strict_monotone (hst : s ⊂ t) : size s < size t :=
by {apply finite.size_strict_monotone _ hst; apply finite.of_fintype }

lemma eq_of_eq_size_subset (hst : s ⊆ t) (hsize : size s = size t) : s = t :=
by {apply finite.eq_of_eq_size_subset _ hst hsize, apply finite.of_fintype }

lemma eq_of_eq_size_subset_iff (hst : s ⊆ t) :
  ((size s = size t) ↔ s = t) :=
by {apply finite.eq_of_eq_size_subset_iff _ hst; apply finite.of_fintype }

lemma eq_of_le_size_subset (hst : s ⊆ t) (hsize : size t ≤ size s) :
  s = t :=
by {apply finite.eq_of_le_size_subset _ hst hsize, apply finite.of_fintype }

lemma size_eq_of_supset (hst : s ⊆ t) (hsize : size t ≤ size s) :
  size s = size t :=
by {apply finite.size_eq_of_supset _ hst hsize, apply finite.of_fintype }

lemma size_pos_iff_has_mem :
  0 < size s ↔ ∃ e, e ∈ s :=
by rw [← nonempty_iff_size_pos, set.nonempty_def]

lemma one_le_size_iff_has_mem :
  1 ≤ size s ↔ ∃ e, e ∈ s :=
by {convert size_pos_iff_has_mem, apply_instance}

lemma size_zero_iff_has_no_mem :
  size s = 0 ↔ ¬ ∃ e, e ∈ s :=
by {rw finite.size_zero_iff_has_no_mem, apply finite.of_fintype}

lemma size_le_zero_iff_has_no_mem :
  size s ≤ 0 ↔ ¬ ∃ e, e ∈ s :=
by {rw finite.size_le_zero_iff_has_no_mem, apply finite.of_fintype}

lemma mem_diff_of_size_lt (h : size s < size t) :
  ∃ (e : α), e ∈ t ∧ e ∉ s :=
by {apply finite.mem_diff_of_size_lt _ h, apply finite.of_fintype}

lemma size_union_singleton_compl (he : e ∈ sᶜ) :
  size (s ∪ {e}) = size s + 1 :=
by {apply finite.size_union_singleton_compl _ he, apply finite.of_fintype}

lemma size_union_nonmem_singleton (hes : e ∉ s) :
  size (s ∪ {e}) = size s + 1 :=
by {apply finite.size_union_singleton_compl _ hes, apply finite.of_fintype}

lemma size_remove_mem (he : e ∈ s) :
  size (s \ {e}) = size s - 1 :=
by {apply finite.size_remove_mem _ he, apply finite.of_fintype}

lemma size_insert_nonmem (he : e ∉ s):
  size (has_insert.insert e s) = size s + 1 :=
by {apply finite.size_insert_nonmem _ he, apply finite.of_fintype, }

lemma has_sub_one_size_ssubset_of_ne_empty (hne : s ≠ ∅) :
  ∃ t, t ⊂ s ∧ size t = size s - 1 :=
by {apply finite.has_sub_one_size_ssubset_of_ne_empty _ hne, apply finite.of_fintype}

lemma has_sub_one_size_ssubset_of_nonempty (hne : s.nonempty) :
  ∃ t, t ⊂ s ∧ size t = size s - 1 :=
by {apply finite.has_sub_one_size_ssubset_of_nonempty _ hne, apply finite.of_fintype}

lemma ne_univ_has_add_one_size_ssupset (hne : s ≠ univ) :
  ∃ t, s ⊂ t ∧ size t = size s + 1 :=
by {apply finite.ne_univ_has_add_one_size_ssupset _ hne, apply finite.of_fintype}

lemma ne_univ_has_add_one_size_ssupset_element (hne : s ≠ univ) :
  ∃ e, s ⊂ s ∪ {e} ∧ size (s ∪ {e}) = size s + 1 :=
by {apply finite.ne_univ_has_add_one_size_ssupset_element _ hne, apply finite.of_fintype}

lemma eq_or_exists_mem_diff_of_size_eq (hst : size s = size t) :
  s = t ∨ ∃ e, e ∈ s \ t :=
by {apply finite.eq_or_exists_mem_diff_of_size_eq _ hst, apply finite.of_fintype}

lemma size_le_one_iff_empty_or_singleton :
  size s ≤ 1 ↔ s = ∅ ∨ ∃ e, s = {e} :=
by {apply finite.size_le_one_iff_empty_or_singleton, apply finite.of_fintype,}

lemma size_le_one_iff_mem_unique :
  size s ≤ 1 ↔ ∀ e f ∈ s, e = f :=
by {apply finite.size_le_one_iff_mem_unique, apply finite.of_fintype}

lemma size_sUnion {k : set (set α)} (hdisj : pairwise_disjoint k) :
  size (⋃₀ k) = ∑ᶠ s in k, size s :=
by {apply finite.size_sUnion _ (λ b hb, _) hdisj; apply finite.of_fintype, }

lemma size_Union {t : β → set α} (h : ∀ x y, x ≠ y → disjoint (t x) (t y)) :
  size (⋃ x : β, t x) = ∑ᶠ i, (size (t i)) :=
by {simp_rw [← finsum_ones_eq_size], apply fin.finsum_in_Union h, }

lemma size_bUnion {t : β → set α} {b : set β} (h : ∀ x y ∈ b, x ≠ y → disjoint (t x) (t y)):
  size (⋃ (x : β) (H : x ∈ b), t x) = ∑ᶠ i in b, size (t i) :=
begin
  rw [← finsum_subtype_eq_finsum_in, ← size_Union], simp,
  rintros ⟨x,hx⟩ ⟨y,hy⟩ hxy,
  refine h x y hx hy _,
  simpa using hxy,
end


lemma eq_univ_of_size_eq_type_size (hs : size s = type_size α) : s = univ :=
begin
  rw [← finsum_ones_eq_size, ← finsum_ones_eq_type_size, finsum_eq_finsum_in_univ] at hs,
  have h := fin.eq_zero_of_finsum_in_subset_eq_finsum_in_of_nonneg
    (subset_univ s) (λ _ _, int.zero_lt_one.le) hs.symm.le,
  simp only [one_ne_zero, univ_diff, mem_compl_eq, imp_false, not_not] at h,
  ext,
  tauto,
end



variables {k : set (set α)}

lemma size_collection_le_size_union (hk : ∀ s ∈ k, set.nonempty s) (hdisj : pairwise_disjoint k):
  (size k ≤ size (⋃₀ k)) :=
finite.size_collection_le_size_union (λ _ _, finite.of_fintype _) hk hdisj

lemma singletons_of_size_collection_eq_size_union (hk : ∀ s ∈ k, set.nonempty s)
(hdisj : pairwise_disjoint k) (hsize : size k = size (⋃₀ k)):
  ∀ s ∈ k, size s = 1 :=
by apply finite.singletons_of_size_collection_eq_size_union _ (λ _ _, _) hk hdisj hsize;
   apply finite.of_fintype

lemma size_collection_eq_size_union_iff
(hk : ∀ s ∈ k, set.nonempty s) (hdisj : pairwise_disjoint k):
  size k = size (⋃₀ k) ↔ ∀ s ∈ k, size s = 1 :=
by apply finite.size_collection_eq_size_union_iff _ (λ _ _, _) hk hdisj; apply finite.of_fintype

lemma size_disjoint_collection_le_type_size {k : set (set α)} (hk' : ∀ s ∈ k, set.nonempty s)
(hdisj : pairwise_disjoint k):
  size k ≤ type_size α :=
le_trans (size_collection_le_size_union hk' hdisj) (size_le_type_size _)

lemma size_disjoint_collection_eq_type_size_iff (hk : ∀ s ∈ k, set.nonempty s)
(hdisj : pairwise_disjoint k):
  size k = type_size α ↔ ⋃₀ k = univ ∧ ∀ s ∈ k, size s = 1 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {  obtain ⟨h₁, h₂⟩ := squeeze_le_trans
      (size_collection_le_size_union hk hdisj)
      (size_le_type_size _)
      h,
    exact ⟨eq_univ_of_size_eq_type_size h₂,
            singletons_of_size_collection_eq_size_union hk hdisj h₁⟩},
  rw [(size_collection_eq_size_union_iff hk hdisj).mpr h.2, h.1, type_size_eq],
end


end fintype


/-! This section deals with fin', an analogue of fin that is defined for all n; it is
an empty type whenever `n ≤ 0`. -/

section fin'

/-- the same as fin, but defined for all integers (empty if `n < 0`)-/
def fin' (n : ℤ) : Type := fin (n.to_nat)

lemma fin'_eq_fin {n : ℕ} :
  fin' n = fin n :=
rfl

lemma fin'_neg_elim {n : ℤ} (hn : n < 0) (x : fin' n) :
  false :=
by {cases x with x hx, rw int.to_nat_zero_of_neg hn at hx, exact nat.not_lt_zero _ hx,  }

lemma fin'_le_zero_elim {n : ℤ} (hn : n ≤ 0) (x : fin' n) :
  false :=
begin
  cases x with x hx,
  rcases eq_or_lt_of_le hn with (rfl | hn),
  { exact nat.not_lt_zero _ hx, },
  rw int.to_nat_zero_of_neg hn at hx,
  exact nat.not_lt_zero _ hx,
end

instance {n : ℤ} : fintype (fin' n) := by {unfold fin', apply_instance}

@[simp] lemma size_fin (n : ℕ) :
  type_size (fin n) = n :=
by {rw [type_size_eq_fincard_t], norm_num}

@[simp] lemma size_fin' (n : ℤ) (hn : 0 ≤ n) :
  type_size (fin' n) = n :=
by {convert size_fin (n.to_nat), exact (int.to_nat_of_nonneg hn).symm}

@[simp] lemma size_fin'_univ (n : ℤ) (hn : 0 ≤ n) :
  size (set.univ : set (fin' n)) = n :=
by {convert size_fin (n.to_nat), exact (int.to_nat_of_nonneg hn).symm}

lemma type_size_eq_iff_equiv_fin' {α : Type*} [fintype α] {n : ℤ} (hn : 0 ≤ n) :
  type_size α = n ↔ nonempty (equiv α (fin' n)) :=
begin
  obtain ⟨m,rfl⟩ := int.eq_coe_of_zero_le hn,
  rw [fin'_eq_fin, ← fincard_t_eq_iff_fin_equiv, type_size_eq_fincard_t, int.coe_nat_inj'],
end

/-- choose an equivalence between a finite type and the appropriate `fin'` -/
def choose_equiv_to_fin' (α : Type*) [fintype α] :
  equiv α (fin' (type_size α)) :=
classical.choice ((type_size_eq_iff_equiv_fin' (type_size_nonneg α)).mp rfl)

lemma type_size_le_zero_elim {α : Type*} [fintype α] (hα : type_size α ≤ 0) (e : α):
  false :=
begin
  let bij := choose_equiv_to_fin' α,
  apply nat.not_lt_zero (bij e).val,
  convert (bij e).property,
  rw int.to_nat_zero_of_nonpos hα,
end

lemma type_size_lt_zero_elim {α : Type*} (hα : type_size α < 0) (e : α):
  false :=
by linarith [type_size_nonneg α]

end fin'


/-! This section covers the relationship between size and functions between sets (mostly embeddings
and bijections) . -/

section embeddings

open set

variables {α : Type*}{β : Type*}

lemma size_image_emb (f : α ↪ β) (s : set α) :
  size (f '' s) = size s :=
by {simp_rw [size], norm_cast, apply fincard_img_emb, }

lemma type_size_le_type_size_inj [fintype β] (f : α ↪ β) :
  type_size α ≤ type_size β :=
begin
  rw [type_size, type_size, ← size_image_emb f],
  apply size_monotone,
  apply subset_univ,
end

lemma size_image_inj {f : α → β} (hf : function.injective f) (s : set α) :
  size (f '' s) = size s :=
size_image_emb ⟨f , hf⟩ s

lemma size_image_equiv (f : α ≃ β) (s : set α) :
  size (f '' s) = size s :=
size_image_emb (f.to_embedding) s

lemma size_range_emb (f : α ↪ β):
  size (range f) = type_size α :=
by {rw [← image_univ, size_image_emb], refl,  }

lemma size_range_inj (f : α → β)(hf : function.injective f):
  size (range f) = type_size α :=
by {rw [← image_univ, size_image_inj hf], refl,  }

lemma type_size_eq_type_size_equiv (f : α ≃ β) :
  type_size α = type_size β :=
by rw [type_size, type_size, ← size_image_equiv f, ← f.range_eq_univ, image_univ]

lemma type_size_eq_iff_equiv [fintype α] [fintype β]:
  type_size α = type_size β ↔ nonempty (α ≃ β) :=
begin
  simp_rw [type_size_eq_fincard_t],
  norm_num,
  simp_rw [fincard_t_eq_fintype_card, fintype.card_eq],
end

/-- Gives an equivalence between two types of equal size -/
def equiv_of_type_size_eq [fintype α] [fintype β] (h : type_size α = type_size β ): α ≃ β :=
classical.choice (type_size_eq_iff_equiv.mp h)

@[simp] lemma equiv.image_mem_image_iff_mem {f : α ≃ β} {x : α} {s : set α} :
  f x ∈ f '' s ↔ x ∈ s :=
begin
  rw mem_image, split,
  { rintros ⟨y, hy, hyx⟩, rw equiv.apply_eq_iff_eq at hyx, rwa ←hyx},
  exact λ hx, ⟨x, hx, rfl⟩,
end

@[simp] lemma size_preimage_equiv (f : α ≃ β) (s : set β) :
  size (f ⁻¹' s) = size s :=
begin
  unfold_coes,
  rw ←set.image_eq_preimage_of_inverse f.right_inv f.left_inv,
  convert size_image_emb (f.symm.to_embedding) s,
end

lemma size_preimage_embed_subset_range (f : α ↪ β) (s : set β) (hs : s ⊆ range f) :
  size (f ⁻¹' s) = size s :=
begin
  suffices h: f '' (f ⁻¹' s) = s,
  { rw eq_comm, nth_rewrite 0 ← h, apply size_image_emb},
  apply image_preimage_eq_of_subset hs,
end

lemma size_subtype_image {E : set α} (s : set E) :
  size (subtype.val '' s) = size s :=
begin
  let f : E ↪ α := ⟨subtype.val, λ x y hxy,
    by {cases x, cases y, simp only [subtype.mk_eq_mk], exact hxy}⟩,
  apply size_image_emb f,
end

@[simp] lemma size_image_coe {E : set α} (s : set E) :
  size (coe '' s : set α) = size s :=
size_subtype_image s

@[simp] lemma size_preimage_coe {E : set α} (s : set α) :
  size (coe ⁻¹' s : set E) = size (s ∩ E) :=
by {rw ← size_image_coe (coe ⁻¹' s : set E), simp, }


lemma nonempty_fin'_emb_of_type_size {n : ℤ} (hα : n ≤ type_size α ) :
  nonempty ((fin' n) ↪ α) :=
begin
  by_cases hn : n ≤ 0,
  { exact ⟨⟨λ x, false.elim (fin'_le_zero_elim hn x), λ x, false.elim (fin'_le_zero_elim hn x)⟩⟩},
  push_neg at hn,
  obtain ⟨m,rfl⟩ := int.eq_coe_of_zero_le (le_of_lt hn),
  rw fin'_eq_fin,

  obtain ⟨s,hs⟩ := has_set_of_size (le_of_lt hn) hα,
  rw [size_def, int.coe_nat_inj'] at hs,
  subst hs,
  letI := fintype_of_type_size_pos (lt_of_lt_of_le hn hα),
  have bij := (@choose_fin_bij ↥s _).symm,
  exact ⟨⟨
    λ x, (bij ⟨x, by {rw fincard_t_subtype_eq_fincard, exact x.property,}⟩).val ,
    λ x y hxy, by {convert subtype.val_injective hxy, tidy,}⟩⟩,
end

/-- an embedding from `fin' n` into `α`, provided that `n ≤ type_size α` -/
def choose_fin'_inj_of_type_size {n : ℤ} (hα : n ≤ type_size α) :
  (fin' n) ↪ α :=
classical.choice (nonempty_fin'_emb_of_type_size hα)

def emb_nonempty_of_size_le_size {α : Type*} {β : Type*} [fintype α]
(hsize : type_size α ≤ type_size β ) :
  nonempty (α ↪ β) :=
⟨(choose_equiv_to_fin' α).to_embedding.trans (@choose_fin'_inj_of_type_size β _ hsize)⟩


lemma type_size_le_iff_emb {α β : Type* } [fintype α] [fintype β] :
  type_size α ≤ type_size β ↔ nonempty (α ↪ β) :=
⟨ λ h, emb_nonempty_of_size_le_size h,
  λ ⟨emb⟩, eq.trans_le (size_range_emb emb).symm (size_le_type_size (range emb)), ⟩

/-- an embedding from `α` into `β`, provided that `type_size α ≤ type_size β` and `α` is finite.
A little scary as this takes a `fintype` and outputs data, so could cause instance issues. Maybe
the `nonempty` version is safer. -/
def choose_emb_of_size_le_size {α : Type*} {β : Type*} [fintype α]
(hsize : type_size α ≤ type_size β ) :
  (α ↪ β) :=
(choose_equiv_to_fin' α).to_embedding.trans (@choose_fin'_inj_of_type_size β _ hsize)

lemma exists_emb_of_type_size_le_size_set {α : Type*} [fintype α] {β : Type*} {s : set β}
(hsize : type_size α ≤ size s ) :
  ∃ (emb : α ↪ β), set.range emb ⊆ s :=
begin
  rw ← type_size_coe_set_eq_size at hsize,
  let emb := choose_emb_of_size_le_size hsize,
  exact ⟨emb.trans ⟨subtype.val, subtype.val_injective ⟩, λ x, by tidy⟩,
end

lemma set.finite.exists_emb_of_type_size_eq_size_set {α : Type*} [fintype α] {β : Type*}
{s : set β} (hs : s.finite) (hsize : type_size α = size s ) :
  ∃ (emb : α ↪ β), set.range emb = s :=
begin
  convert exists_emb_of_type_size_le_size_set (le_of_eq hsize),
  ext emb,
  split,
  { unfreezingI {rintro rfl}, exact subset_refl _, },
  intros hss,
  apply finite.eq_of_eq_size_subset hs hss,
  rw [← image_univ, size_image_emb],
  convert hsize,
end

lemma exists_emb_of_type_size_eq_size_set {α : Type*} [fintype α] {β : Type*} [fintype β]
{s : set β} (hsize : type_size α = size s ) :
  ∃ (emb : α ↪ β), set.range emb = s :=
by {apply set.finite.exists_emb_of_type_size_eq_size_set _ hsize, apply finite.of_fintype }

lemma type_size_lt_of_nonmem_range_emb {α β : Type* } [fintype β] (emb : α ↪ β) {b : β}
(hb : b ∉ range emb):
  type_size α < type_size β :=
begin
  refine lt_of_le_of_ne (by { rw [← size_range_emb emb], apply size_le_type_size, }) (λ h, _),
  letI : fintype α := fintype.of_injective _ (emb.injective),
  let eq := equiv_of_type_size_eq h.symm,
  have h' := size_image_equiv eq (has_insert.insert b (range emb)),
  rw [size_insert_nonmem hb, size_range_emb] at h',
  linarith [size_le_type_size (eq '' insert b (range ⇑emb))],
end

lemma type_size_lt_iff_exists_proper_emb {α β : Type*} [fintype α] [fintype β] :
  type_size α < type_size β ↔ ∃ (emb : α ↪ β) (b : β), b ∉ range emb :=
begin
  refine ⟨λ h, _, λ ⟨emb, b, hb⟩, type_size_lt_of_nonmem_range_emb emb hb⟩,
  obtain ⟨emb⟩ := emb_nonempty_of_size_le_size (le_of_lt h),
  refine ⟨emb, compl_nonempty_iff_exists_nonmem.mp (compl_nonempty_of_size_lt_type_size _)⟩,
  rwa size_range_emb,
end



end embeddings
