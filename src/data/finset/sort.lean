/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import order.rel_iso.set
import data.fintype.lattice
import data.multiset.sort
import data.list.nodup_equiv_fin

/-!
# Construct a sorted list from a finset.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
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

@[simp] theorem sort_empty : sort r ∅ = [] :=
multiset.sort_zero r

@[simp] theorem sort_singleton (a : α) : sort r {a} = [a] :=
multiset.sort_singleton r a

lemma sort_perm_to_list (s : finset α) : sort r s ~ s.to_list :=
by { rw ←multiset.coe_eq_coe, simp only [coe_to_list, sort_eq] }

end sort

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
    exact (s.sort_sorted (≤)).rel_nth_le_of_le _ _ (nat.zero_le i) },
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
    exact (s.sort_sorted (≤)).rel_nth_le_of_le _ _ (nat.le_pred_of_lt i_lt) },
end

lemma sorted_last_eq_max' {s : finset α} {h : (s.sort (≤)).length - 1 < (s.sort (≤)).length} :
  (s.sort (≤)).nth_le ((s.sort (≤)).length - 1) h =
  s.max' (by { rw length_sort at h, exact card_pos.1 (lt_of_le_of_lt bot_le h) }) :=
sorted_last_eq_max'_aux _ _ _

lemma max'_eq_sorted_last {s : finset α} {h : s.nonempty} :
  s.max' h = (s.sort (≤)).nth_le ((s.sort (≤)).length - 1)
    (by simpa using nat.sub_lt (card_pos.mpr h) zero_lt_one) :=
(sorted_last_eq_max'_aux _ _ _).symm

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `order_iso_of_fin s h`
is the increasing bijection between `fin k` and `s` as an `order_iso`. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of an iso `fin s.card ≃o s` to avoid
casting issues in further uses of this function. -/
def order_iso_of_fin (s : finset α) {k : ℕ} (h : s.card = k) : fin k ≃o s :=
order_iso.trans (fin.cast ((length_sort (≤)).trans h).symm) $
  (s.sort_sorted_lt.nth_le_iso _).trans $ order_iso.set_congr _ _ $
    set.ext $ λ x, mem_sort _

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `order_emb_of_fin s h` is
the increasing bijection between `fin k` and `s` as an order embedding into `α`. Here, `h` is a
proof that the cardinality of `s` is `k`. We use this instead of an embedding `fin s.card ↪o α` to
avoid casting issues in further uses of this function. -/
def order_emb_of_fin (s : finset α) {k : ℕ} (h : s.card = k) : fin k ↪o α :=
(order_iso_of_fin s h).to_order_embedding.trans (order_embedding.subtype _)

@[simp] lemma coe_order_iso_of_fin_apply (s : finset α) {k : ℕ} (h : s.card = k) (i : fin k) :
  ↑(order_iso_of_fin s h i) = order_emb_of_fin s h i :=
rfl

lemma order_iso_of_fin_symm_apply (s : finset α) {k : ℕ} (h : s.card = k) (x : s) :
  ↑((s.order_iso_of_fin h).symm x) = (s.sort (≤)).index_of x :=
rfl

lemma order_emb_of_fin_apply (s : finset α) {k : ℕ} (h : s.card = k) (i : fin k) :
  s.order_emb_of_fin h i = (s.sort (≤)).nth_le i (by { rw [length_sort, h], exact i.2 }) :=
rfl

@[simp] lemma order_emb_of_fin_mem (s : finset α) {k : ℕ} (h : s.card = k) (i : fin k) :
  s.order_emb_of_fin h i ∈ s :=
(s.order_iso_of_fin h i).2

@[simp] lemma range_order_emb_of_fin (s : finset α) {k : ℕ} (h : s.card = k) :
  set.range (s.order_emb_of_fin h) = s :=
by simp only [order_emb_of_fin, set.range_comp coe (s.order_iso_of_fin h), rel_embedding.coe_trans,
 set.image_univ,
 finset.order_emb_of_fin.equations._eqn_1,
 rel_iso.range_eq,
 order_embedding.subtype_apply,
 order_iso.coe_to_order_embedding,
 eq_self_iff_true,
 subtype.range_coe_subtype,
 finset.set_of_mem,
 finset.coe_inj]

/-- The bijection `order_emb_of_fin s h` sends `0` to the minimum of `s`. -/
lemma order_emb_of_fin_zero {s : finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
  order_emb_of_fin s h ⟨0, hz⟩ = s.min' (card_pos.mp (h.symm ▸ hz)) :=
by simp only [order_emb_of_fin_apply, fin.coe_mk, sorted_zero_eq_min']

/-- The bijection `order_emb_of_fin s h` sends `k-1` to the maximum of `s`. -/
lemma order_emb_of_fin_last {s : finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
  order_emb_of_fin s h ⟨k-1, buffer.lt_aux_2 hz⟩ = s.max' (card_pos.mp (h.symm ▸ hz)) :=
by simp [order_emb_of_fin_apply, max'_eq_sorted_last, h]

/-- `order_emb_of_fin {a} h` sends any argument to `a`. -/
@[simp] lemma order_emb_of_fin_singleton (a : α) (i : fin 1) :
  order_emb_of_fin {a} (card_singleton a) i = a :=
by rw [subsingleton.elim i ⟨0, zero_lt_one⟩, order_emb_of_fin_zero _ zero_lt_one, min'_singleton]

/-- Any increasing map `f` from `fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `order_emb_of_fin s h`. -/
lemma order_emb_of_fin_unique {s : finset α} {k : ℕ} (h : s.card = k) {f : fin k → α}
  (hfs : ∀ x, f x ∈ s) (hmono : strict_mono f) : f = s.order_emb_of_fin h :=
begin
  apply fin.strict_mono_unique hmono (s.order_emb_of_fin h).strict_mono,
  rw [range_order_emb_of_fin, ← set.image_univ, ← coe_univ, ← coe_image, coe_inj],
  refine eq_of_subset_of_card_le (λ x hx, _) _,
  { rcases mem_image.1 hx with ⟨x, hx, rfl⟩, exact hfs x },
  { rw [h, card_image_of_injective _ hmono.injective, card_univ, fintype.card_fin] }
end

/-- An order embedding `f` from `fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `order_emb_of_fin s h`. -/
lemma order_emb_of_fin_unique' {s : finset α} {k : ℕ} (h : s.card = k) {f : fin k ↪o α}
  (hfs : ∀ x, f x ∈ s) : f = s.order_emb_of_fin h :=
rel_embedding.ext $ function.funext_iff.1 $ order_emb_of_fin_unique h hfs f.strict_mono

/-- Two parametrizations `order_emb_of_fin` of the same set take the same value on `i` and `j` if
and only if `i = j`. Since they can be defined on a priori not defeq types `fin k` and `fin l`
(although necessarily `k = l`), the conclusion is rather written `(i : ℕ) = (j : ℕ)`. -/
@[simp] lemma order_emb_of_fin_eq_order_emb_of_fin_iff
  {k l : ℕ} {s : finset α} {i : fin k} {j : fin l} {h : s.card = k} {h' : s.card = l} :
  s.order_emb_of_fin h i = s.order_emb_of_fin h' j ↔ (i : ℕ) = (j : ℕ) :=
begin
  substs k l,
  exact (s.order_emb_of_fin rfl).eq_iff_eq.trans fin.ext_iff
end

/-- Given a finset `s` of size at least `k` in a linear order `α`, the map `order_emb_of_card_le`
is an order embedding from `fin k` to `α` whose image is contained in `s`. Specifically, it maps
`fin k` to an initial segment of `s`. -/
def order_emb_of_card_le (s : finset α) {k : ℕ} (h : k ≤ s.card) : fin k ↪o α :=
(fin.cast_le h).trans (s.order_emb_of_fin rfl)

lemma order_emb_of_card_le_mem (s : finset α) {k : ℕ} (h : k ≤ s.card) (a) :
  order_emb_of_card_le s h a ∈ s :=
by simp only [order_emb_of_card_le, rel_embedding.coe_trans, finset.order_emb_of_fin_mem]

end sort_linear_order

meta instance [has_repr α] : has_repr (finset α) := ⟨λ s, repr s.1⟩

end finset
