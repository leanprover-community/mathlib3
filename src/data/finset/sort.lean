/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.finset.lattice
import data.multiset.sort
import data.list.nodup_equiv_fin

/-!
# Construct a sorted list from a finset.
-/

namespace finset

open multiset nat
variables {α β : Type*}

/-! ### sort -/
section sort
variables (r : α → α → Prop) [decidable_rel r]
  [is_trans α r] [is_antisymm α r] [is_total α r]

/-- `sort s` constructs a sorted list from the unordered set `s`.
  (Uses merge sort algorithm.) -/
def sort (s : finset α) : list α := sort r s.1

@[simp] theorem sort_sorted (s : finset α) : list.sorted r (sort r s) :=
sort_sorted _ _

@[simp] theorem sort_eq (s : finset α) : ↑(sort r s) = s.1 :=
sort_eq _ _

@[simp] theorem sort_nodup (s : finset α) : (sort r s).nodup :=
(by rw sort_eq; exact s.2 : @multiset.nodup α (sort r s))

@[simp] theorem sort_to_finset [decidable_eq α] (s : finset α) : (sort r s).to_finset = s :=
list.to_finset_eq (sort_nodup r s) ▸ eq_of_veq (sort_eq r s)

@[simp] theorem mem_sort {s : finset α} {a : α} : a ∈ sort r s ↔ a ∈ s :=
multiset.mem_sort _

@[simp] theorem length_sort {s : finset α} : (sort r s).length = s.card :=
multiset.length_sort _

end sort

set_option trace.class_instances false

section sort_linear_order

variables [linear_order α]

theorem sort_sorted_lt (s : finset α) : list.sorted (<) (sort (≤) s) :=
(sort_sorted _ _).imp₂ (@lt_of_le_of_ne _ _) (sort_nodup _ _)

lemma sorted_zero_eq_min'_aux (s : finset α) (h : 0 < (s.sort (≤)).length) (H : s.nonempty) :
  (s.sort (≤)).nth_le 0 h = s.min' H :=
begin
  let l := s.sort (≤),
  apply le_antisymm,
  { have : s.min' H ∈ l := (finset.mem_sort (≤)).mpr (s.min'_mem H),
    obtain ⟨i, i_lt, hi⟩ : ∃ i (hi : i < l.length), l.nth_le i hi = s.min' H :=
      list.mem_iff_nth_le.1 this,
    rw ← hi,
    exact list.nth_le_of_sorted_of_le (s.sort_sorted (≤)) (nat.zero_le i) },
  { have : l.nth_le 0 h ∈ s := (finset.mem_sort (≤)).1 (list.nth_le_mem l 0 h),
    exact s.min'_le _ this }
end

lemma sorted_zero_eq_min' {s : finset α} {h : 0 < (s.sort (≤)).length} :
  (s.sort (≤)).nth_le 0 h = s.min' (card_pos.1 $ by rwa length_sort at h) :=
sorted_zero_eq_min'_aux _ _ _

lemma min'_eq_sorted_zero {s : finset α} {h : s.nonempty} :
  s.min' h = (s.sort (≤)).nth_le 0 (by { rw length_sort, exact card_pos.2 h }) :=
(sorted_zero_eq_min'_aux _ _ _).symm

lemma sorted_last_eq_max'_aux (s : finset α) (h : (s.sort (≤)).length - 1 < (s.sort (≤)).length)
  (H : s.nonempty) : (s.sort (≤)).nth_le ((s.sort (≤)).length - 1) h = s.max' H :=
begin
  let l := s.sort (≤),
  apply le_antisymm,
  { have : l.nth_le ((s.sort (≤)).length - 1) h ∈ s :=
      (finset.mem_sort (≤)).1 (list.nth_le_mem l _ h),
    exact s.le_max' _ this },
  { have : s.max' H ∈ l := (finset.mem_sort (≤)).mpr (s.max'_mem H),
    obtain ⟨i, i_lt, hi⟩ : ∃ i (hi : i < l.length), l.nth_le i hi = s.max' H :=
      list.mem_iff_nth_le.1 this,
    rw ← hi,
    have : i ≤ l.length - 1 := nat.le_pred_of_lt i_lt,
    exact list.nth_le_of_sorted_of_le (s.sort_sorted (≤)) (nat.le_pred_of_lt i_lt) },
end

lemma sorted_last_eq_max' {s : finset α} {h : (s.sort (≤)).length - 1 < (s.sort (≤)).length} :
  (s.sort (≤)).nth_le ((s.sort (≤)).length - 1) h =
  s.max' (by { rw length_sort at h, exact card_pos.1 (lt_of_le_of_lt bot_le h) }) :=
sorted_last_eq_max'_aux _ _ _

lemma max'_eq_sorted_last {s : finset α} {h : s.nonempty} :
  s.max' h = (s.sort (≤)).nth_le ((s.sort (≤)).length - 1)
    (by simpa using sub_lt (card_pos.mpr h) zero_lt_one) :=
(sorted_last_eq_max'_aux _ _ _).symm

/-- Given a finset `s` of cardinal `k` in a linear order `α`, the map `mono_of_fin s h`
is the increasing bijection between `fin k` and `s` as an `α`-valued map. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of a map `fin s.card → α` to avoid
casting issues in further uses of this function. -/
def mono_of_fin (s : finset α) {k : ℕ} (h : s.card = k) : fin k ≃o (s : set α) :=
order_iso.trans (fin.cast ((length_sort (≤)).trans h).symm) $
  (s.sort_sorted_lt.nth_le_iso _).trans $ order_iso.set_congr _ _ $
    set.ext $ λ x, mem_sort _

lemma mono_of_fin_apply (s : finset α) {k : ℕ} (h : s.card = k) (i : fin k) :
  ↑(s.mono_of_fin h i) = (s.sort (≤)).nth_le i (by { rw [length_sort, h], exact i.2 }) :=
rfl

lemma mono_of_fin_symm_apply (s : finset α) {k : ℕ} (h : s.card = k) (x : (s : set α)) :
  ↑((s.mono_of_fin h).symm x) = (s.sort (≤)).index_of x :=
rfl

/-- The bijection `mono_of_fin s h` sends `0` to the minimum of `s`. -/
lemma mono_of_fin_zero {s : finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
  ↑(mono_of_fin s h ⟨0, hz⟩) = s.min' (card_pos.mp (h.symm ▸ hz)) :=
by simp only [mono_of_fin_apply, subtype.coe_mk, sorted_zero_eq_min']

/-- The bijection `mono_of_fin s h` sends `k-1` to the maximum of `s`. -/
lemma mono_of_fin_last {s : finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
  ↑(mono_of_fin s h ⟨k-1, buffer.lt_aux_2 hz⟩) = s.max' (card_pos.mp (h.symm ▸ hz)) :=
by simp [mono_of_fin_apply, max'_eq_sorted_last, h]

/-- `mono_of_fin {a} h` sends any argument to `a`. -/
@[simp] lemma mono_of_fin_singleton (a : α) (i : fin 1) :
  ↑(mono_of_fin {a} (card_singleton a) i) = a :=
by rw [subsingleton.elim i ⟨0, zero_lt_one⟩, mono_of_fin_zero _ zero_lt_one, min'_singleton]

/-- Any increasing bijection between `fin k` and a finset of cardinality `k` has to coincide with
the increasing bijection `mono_of_fin s h`. For a statement assuming only that `f` maps `univ` to
`s`, see `mono_of_fin_unique'`.-/
lemma mono_of_fin_unique {s : finset α} {k : ℕ} (h : s.card = k) {f : fin k → α}
  (hbij : set.bij_on f set.univ ↑s) (hmono : strict_mono f) : f = coe ∘ s.mono_of_fin h :=
begin

end

/-- Any increasing map between `fin k` and a finset of cardinality `k` has to coincide with
the increasing bijection `mono_of_fin s h`. -/
lemma mono_of_fin_unique' {s : finset α} {k : ℕ} (h : s.card = k)
  {f : fin k → α} (fmap : set.maps_to f set.univ ↑s) (hmono : strict_mono f) :
  f = s.mono_of_fin h :=
begin
  have finj : set.inj_on f set.univ := hmono.injective.inj_on _,
  apply mono_of_fin_unique h (set.bij_on.mk fmap finj (λ y hy, _)) hmono,
  simp only [set.image_univ, set.mem_range],
  rcases surj_on_of_inj_on_of_card_le (λ i (hi : i ∈ finset.fin_range k), f i)
    (λ i hi, fmap (set.mem_univ i)) (λ i j hi hj hij, finj (set.mem_univ i) (set.mem_univ j) hij)
    (by simp [h]) y hy with ⟨x, _, hx⟩,
  exact ⟨x, hx.symm⟩
end

/-- Two parametrizations `mono_of_fin` of the same set take the same value on `i` and `j` if and
only if `i = j`. Since they can be defined on a priori not defeq types `fin k` and `fin l` (although
necessarily `k = l`), the conclusion is rather written `(i : ℕ) = (j : ℕ)`. -/
@[simp] lemma mono_of_fin_eq_mono_of_fin_iff
  {k l : ℕ} {s : finset α} {i : fin k} {j : fin l} {h : s.card = k} {h' : s.card = l} :
  s.mono_of_fin h i = s.mono_of_fin h' j ↔ (i : ℕ) = (j : ℕ) :=
begin
  have A : k = l, by rw [← h', ← h],
  have : s.mono_of_fin h = (s.mono_of_fin h') ∘ (λ j : (fin k), ⟨j, A ▸ j.is_lt⟩) := rfl,
  rw [this, function.comp_app, (s.mono_of_fin_injective h').eq_iff, fin.ext_iff, fin.coe_mk]
end

/-- Given a finset `s` of cardinal `k` in a linear order `α`, the equiv `mono_equiv_of_fin s h`
is the increasing bijection between `fin k` and `s` as an `s`-valued map. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of a map `fin s.card → α` to avoid
casting issues in further uses of this function. -/
noncomputable def mono_equiv_of_fin (s : finset α) {k : ℕ} (h : s.card = k) :
  fin k ≃ {x // x ∈ s} :=
(equiv.set.univ _).symm.trans $ (s.mono_of_fin_bij_on h).equiv _

end sort_linear_order

instance [has_repr α] : has_repr (finset α) := ⟨λ s, repr s.1⟩

end finset
