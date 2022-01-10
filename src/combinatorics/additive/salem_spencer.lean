/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.asymptotics.asymptotics

/-!
# Salem-Spencer sets and Roth numbers

This file defines Salem-Spencer sets and the Roth number of a set.

A Salem-Spencer set is a set without arithmetic progressions of length `3`. Equivalently, the
average of any two distinct elements is not in the set.

The Roth number of a finset is the size of its biggest Salem-Spencer subset. This is a more general
definition than the one often found in mathematical litterature, where the `n`-th Roth number is
the size of the biggest Salem-Spencer subset of `{0, ..., n - 1}`.

## Main declarations

* `mul_salem_spencer`: Predicate for a set to be multiplicative Salem-Spencer.
* `add_salem_spencer`: Predicate for a set to be additive Salem-Spencer.
* `mul_roth_number`: The multiplicative Roth number of a finset.
* `add_roth_number`: The additive Roth number of a finset.
* `roth_number_nat`: The Roth number of a natural. This corresponds to
  `add_roth_number (finset.range n)`.

## TODO

Can `add_salem_spencer_iff_eq_right` be made more general?

## Tags

Salem-Spencer, Roth, arithmetic progression, average, three-free
-/

open finset nat

variables {α β : Type*}

section salem_spencer
section monoid
variables [monoid α] [monoid β] (s t : set α)

/-- A multiplicative Salem-Spencer, aka non averaging, set `s` in a monoid is a set such that the
multiplicative average of any two distinct elements is not in the set. -/
@[to_additive "A Salem-Spencer, aka non averaging, set `s` in an additive monoid
is a set such that the average of any two distinct elements is not in the set."]
def mul_salem_spencer : Prop := ∀ ⦃a b c⦄, a ∈ s → b ∈ s → c ∈ s → a * b = c * c → a = b

/-- Whether a given finset is Salem-Spencer is decidable. -/
@[to_additive]
instance {α : Type*} [decidable_eq α] [monoid α] {s : finset α} :
  decidable (mul_salem_spencer (s : set α)) :=
decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a * b = c * c → a = b)
  ⟨λ h a b c ha hb hc, h a ha b hb c hc, λ h a ha b hb c hc, h ha hb hc⟩

variables {s t}

@[to_additive]
lemma mul_salem_spencer.mono (h : t ⊆ s) (hs : mul_salem_spencer s) : mul_salem_spencer t :=
λ a b c ha hb hc, hs (h ha) (h hb) (h hc)

@[simp, to_additive]
lemma mul_salem_spencer_empty : mul_salem_spencer (∅ : set α) := λ a _ _ ha, ha.elim

@[to_additive]
lemma set.subsingleton.mul_salem_spencer (hs : s.subsingleton) : mul_salem_spencer s :=
λ a b _ ha hb _ _, hs ha hb

@[simp, to_additive]
lemma mul_salem_spencer_singleton (a : α) : mul_salem_spencer ({a} : set α) :=
set.subsingleton_singleton.mul_salem_spencer

@[to_additive]
lemma mul_salem_spencer.prod {t : set β} (hs : mul_salem_spencer s) (ht : mul_salem_spencer t) :
  mul_salem_spencer (s.prod t) :=
λ a b c ha hb hc h,
  prod.ext (hs ha.1 hb.1 hc.1 (prod.ext_iff.1 h).1) (ht ha.2 hb.2 hc.2 (prod.ext_iff.1 h).2)

@[to_additive]
lemma mul_salem_spencer_pi {ι : Type*} {α : ι → Type*} [Π i, monoid (α i)] {s : Π i, set (α i)}
  (hs : ∀ i, mul_salem_spencer (s i)) :
  mul_salem_spencer ((set.univ : set ι).pi s) :=
λ a b c ha hb hc h, funext $ λ i, hs i (ha i trivial) (hb i trivial) (hc i trivial) $ congr_fun h i

end monoid

section cancel_comm_monoid
variables [cancel_comm_monoid α] {s : set α} {a : α}

@[to_additive]
lemma mul_salem_spencer_insert :
  mul_salem_spencer (insert a s) ↔ mul_salem_spencer s ∧
    (∀ ⦃b c⦄, b ∈ s → c ∈ s → a * b = c * c → a = b) ∧
    ∀ ⦃b c⦄, b ∈ s → c ∈ s → b * c = a * a → b = c :=
begin
  refine ⟨λ hs, ⟨hs.mono (set.subset_insert _ _),
    λ b c hb hc, hs (or.inl rfl) (or.inr hb) (or.inr hc),
    λ b c hb hc, hs (or.inr hb) (or.inr hc) (or.inl rfl)⟩, _⟩,
  rintro ⟨hs, ha, ha'⟩ b c d hb hc hd h,
  rw set.mem_insert_iff at hb hc hd,
  obtain rfl | hb := hb;
  obtain rfl | hc := hc,
  { refl },
  all_goals { obtain rfl | hd := hd },
  { exact (mul_left_cancel h).symm },
  { exact ha hc hd h },
  { exact mul_right_cancel h },
  { exact (ha hb hd $ (mul_comm _ _).trans h).symm },
  { exact ha' hb hc h },
  { exact hs hb hc hd h }
end

@[simp, to_additive]
lemma mul_salem_spencer_pair (a b : α) : mul_salem_spencer ({a, b} : set α) :=
begin
  rw mul_salem_spencer_insert,
  refine ⟨mul_salem_spencer_singleton _, _, _⟩,
  { rintro c d (rfl : c = b) (rfl : d = c),
    exact mul_right_cancel },
  { rintro c d (rfl : c = b) (rfl : d = c) _,
    refl }
end

@[to_additive]
lemma mul_salem_spencer.mul_left (hs : mul_salem_spencer s) : mul_salem_spencer ((*) a '' s) :=
begin
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h,
  rw [mul_mul_mul_comm, mul_mul_mul_comm a d] at h,
  rw hs hb hc hd (mul_left_cancel h),
end

@[to_additive]
lemma mul_salem_spencer.mul_right (hs : mul_salem_spencer s) : mul_salem_spencer ((* a) '' s) :=
begin
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h,
  rw [mul_mul_mul_comm, mul_mul_mul_comm d] at h,
  rw hs hb hc hd (mul_right_cancel h),
end

@[to_additive]
lemma mul_salem_spencer_mul_left_iff : mul_salem_spencer ((*) a '' s) ↔ mul_salem_spencer s :=
⟨λ hs b c d hb hc hd h, mul_left_cancel (hs (set.mem_image_of_mem _ hb) (set.mem_image_of_mem _ hc)
  (set.mem_image_of_mem _ hd) $ by rw [mul_mul_mul_comm, h, mul_mul_mul_comm]),
  mul_salem_spencer.mul_left⟩

@[to_additive]
lemma mul_salem_spencer_mul_right_iff :
  mul_salem_spencer ((* a) '' s) ↔ mul_salem_spencer s :=
⟨λ hs b c d hb hc hd h, mul_right_cancel (hs (set.mem_image_of_mem _ hb) (set.mem_image_of_mem _ hc)
  (set.mem_image_of_mem _ hd) $ by rw [mul_mul_mul_comm, h, mul_mul_mul_comm]),
  mul_salem_spencer.mul_right⟩

end cancel_comm_monoid

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid α] {s : set α} {a : α}

@[to_additive]
lemma mul_salem_spencer_insert_of_lt (hs : ∀ i ∈ s, i < a) :
  mul_salem_spencer (insert a s) ↔ mul_salem_spencer s ∧
    ∀ ⦃b c⦄, b ∈ s → c ∈ s → a * b = c * c → a = b :=
begin
  refine mul_salem_spencer_insert.trans _,
  rw ←and_assoc,
  exact and_iff_left (λ b c hb hc h, ((mul_lt_mul''' (hs _ hb) (hs _ hc)).ne h).elim),
end

end ordered_cancel_comm_monoid

section cancel_comm_monoid_with_zero
variables [cancel_comm_monoid_with_zero α] [no_zero_divisors α] {s : set α} {a : α}

lemma mul_salem_spencer.mul_left₀ (hs : mul_salem_spencer s) (ha : a ≠ 0) :
  mul_salem_spencer ((*) a '' s) :=
begin
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h,
  rw [mul_mul_mul_comm, mul_mul_mul_comm a d] at h,
  rw hs hb hc hd (mul_left_cancel₀ (mul_ne_zero ha ha) h),
end

lemma mul_salem_spencer.mul_right₀ (hs : mul_salem_spencer s) (ha : a ≠ 0) :
  mul_salem_spencer ((* a) '' s) :=
begin
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h,
  rw [mul_mul_mul_comm, mul_mul_mul_comm d] at h,
  rw hs hb hc hd (mul_right_cancel₀ (mul_ne_zero ha ha) h),
end

lemma mul_salem_spencer_mul_left_iff₀ (ha : a ≠ 0) :
  mul_salem_spencer ((*) a '' s) ↔ mul_salem_spencer s :=
⟨λ hs b c d hb hc hd h, mul_left_cancel₀ ha
  (hs (set.mem_image_of_mem _ hb) (set.mem_image_of_mem _ hc) (set.mem_image_of_mem _ hd) $
  by rw [mul_mul_mul_comm, h, mul_mul_mul_comm]),
  λ hs, hs.mul_left₀ ha⟩

lemma mul_salem_spencer_mul_right_iff₀ (ha : a ≠ 0) :
  mul_salem_spencer ((* a) '' s) ↔ mul_salem_spencer s :=
⟨λ hs b c d hb hc hd h, mul_right_cancel₀ ha
  (hs (set.mem_image_of_mem _ hb) (set.mem_image_of_mem _ hc) (set.mem_image_of_mem _ hd) $
  by rw [mul_mul_mul_comm, h, mul_mul_mul_comm]),
  λ hs, hs.mul_right₀ ha⟩

end cancel_comm_monoid_with_zero

section nat

lemma add_salem_spencer_iff_eq_right {s : set ℕ} :
  add_salem_spencer s ↔ ∀ ⦃a b c⦄, a ∈ s → b ∈ s → c ∈ s → a + b = c + c → a = c :=
begin
  refine forall_congr (λ a, forall_congr $ λ b, forall_congr $ λ c, forall_congr $
    λ _, forall_congr $ λ _, forall_congr $ λ _,  forall_congr $ λ habc, ⟨_, _⟩),
  { rintro rfl,
    simp_rw ←two_mul at habc,
    exact mul_left_cancel₀ two_ne_zero habc },
  { rintro rfl,
    exact (add_left_cancel habc).symm }
end

end nat
end salem_spencer

section roth_number
variables [decidable_eq α]

section monoid
variables [monoid α] [decidable_eq β] [monoid β] (s t : finset α)

/-- The multiplicative Roth number of a finset is the cardinality of its biggest multiplicative
Salem-Spencer subset. -/
@[to_additive "The additive Roth number of a finset is the cardinality of its biggest additive
Salem-Spencer subset. The usual Roth number corresponds to `roth_number (finset.range n)`, see
`roth_number_nat`. "]
def mul_roth_number : finset α →o ℕ :=
⟨λ s, nat.find_greatest (λ m, ∃ t ⊆ s, t.card = m ∧ mul_salem_spencer (t : set α)) s.card,
begin
  rintro t u htu,
  refine nat.find_greatest_mono (λ m, _) (card_le_of_subset htu),
  rintro ⟨v, hvt, hv⟩,
  exact ⟨v, hvt.trans htu, hv⟩,
end⟩

@[to_additive]
lemma mul_roth_number_le : mul_roth_number s ≤ s.card := by convert nat.find_greatest_le s.card

@[to_additive]
lemma mul_roth_number_spec : ∃ t ⊆ s, t.card = mul_roth_number s ∧ mul_salem_spencer (t : set α) :=
@nat.find_greatest_spec _ (λ m, ∃ t ⊆ s, t.card = m ∧ mul_salem_spencer (t : set α)) _ _
  (nat.zero_le _) ⟨∅, empty_subset _, card_empty, mul_salem_spencer_empty⟩

variables {s t} {n : ℕ}

@[to_additive]
lemma mul_salem_spencer.le_mul_roth_number (hs : mul_salem_spencer (s : set α)) (h : s ⊆ t) :
  s.card ≤ mul_roth_number t :=
le_find_greatest (card_le_of_subset h) ⟨s, h, rfl, hs⟩

@[to_additive]
lemma mul_salem_spencer.roth_number_eq (hs : mul_salem_spencer (s : set α)) :
  mul_roth_number s = s.card :=
(mul_roth_number_le _).antisymm $ hs.le_mul_roth_number $ subset.refl _

@[simp, to_additive]
lemma mul_roth_number_empty : mul_roth_number (∅ : finset α) = 0 :=
nat.eq_zero_of_le_zero $ (mul_roth_number_le _).trans card_empty.le

@[simp, to_additive]
lemma mul_roth_number_singleton (a : α) : mul_roth_number ({a} : finset α) = 1 :=
begin
  convert mul_salem_spencer.roth_number_eq _,
  rw coe_singleton,
  exact mul_salem_spencer_singleton a,
end

@[to_additive]
lemma mul_roth_number_union_le (s t : finset α) :
  mul_roth_number (s ∪ t) ≤ mul_roth_number s + mul_roth_number t :=
let ⟨u, hus, hcard, hu⟩ := mul_roth_number_spec (s ∪ t) in
calc
  mul_roth_number (s ∪ t)
      = u.card : hcard.symm
  ... = (u ∩ s ∪ u ∩ t).card
      : by rw [←inter_distrib_left, (inter_eq_left_iff_subset _ _).2 hus]
  ... ≤ (u ∩ s).card + (u ∩ t).card : card_union_le _ _
  ... ≤ mul_roth_number s + mul_roth_number t
      : add_le_add ((hu.mono $ inter_subset_left _ _).le_mul_roth_number $ inter_subset_right _ _)
          ((hu.mono $ inter_subset_left _ _).le_mul_roth_number $ inter_subset_right _ _)

@[to_additive]
lemma le_mul_roth_number_product (s : finset α) (t : finset β) :
  mul_roth_number s * mul_roth_number t ≤ mul_roth_number (s.product t) :=
begin
  obtain ⟨u, hus, hucard, hu⟩ := mul_roth_number_spec s,
  obtain ⟨v, hvt, hvcard, hv⟩ := mul_roth_number_spec t,
  rw [←hucard, ←hvcard, ←card_product],
  refine mul_salem_spencer.le_mul_roth_number _ (product_subset_product hus hvt),
  rw coe_product,
  exact hu.prod hv,
end

@[to_additive]
lemma mul_roth_number_lt_of_forall_not_mul_salem_spencer
  (h : ∀ t ∈ powerset_len n s, ¬mul_salem_spencer ((t : finset α) : set α)) :
  mul_roth_number s < n :=
begin
  obtain ⟨t, hts, hcard, ht⟩ := mul_roth_number_spec s,
  rw [←hcard, ←not_le],
  intro hn,
  obtain ⟨u, hut, rfl⟩ := exists_smaller_set t n hn,
  exact h _ (mem_powerset_len.2 ⟨hut.trans hts, rfl⟩) (ht.mono hut),
end

end monoid

section cancel_comm_monoid
variables [cancel_comm_monoid α] (s : finset α) (a : α)

@[simp, to_additive] lemma mul_roth_number_map_mul_left :
  mul_roth_number (s.map $ mul_left_embedding a) = mul_roth_number s :=
begin
  refine le_antisymm _ _,
  { obtain ⟨u, hus, hcard, hu⟩ := mul_roth_number_spec (s.map $ mul_left_embedding a),
    rw subset_map_iff at hus,
    obtain ⟨u, hus, rfl⟩ := hus,
    rw coe_map at hu,
    rw [←hcard, card_map],
    exact (mul_salem_spencer_mul_left_iff.1 hu).le_mul_roth_number hus },
  { obtain ⟨u, hus, hcard, hu⟩ := mul_roth_number_spec s,
    have h : mul_salem_spencer (u.map $ mul_left_embedding a : set α),
    { rw coe_map,
      exact hu.mul_left },
    convert h.le_mul_roth_number (map_subset_map.2 hus),
    rw [card_map, hcard] }
end

@[simp, to_additive] lemma mul_roth_number_map_mul_right :
  mul_roth_number (s.map $ mul_right_embedding a) = mul_roth_number s :=
by rw [←mul_left_embedding_eq_mul_right_embedding, mul_roth_number_map_mul_left s a]

end cancel_comm_monoid
end roth_number

section roth_number_nat
variables {s : finset ℕ} {k n : ℕ}

/-- The Roth number of a natural `N` is the largest integer `m` for which there is a subset of
`range N` of size `m` with no arithmetic progression of length 3.
Trivially, `roth_number N ≤ N`, but Roth's theorem (proved in 1953) shows that
`roth_number N = o(N)` and the construction by Behrend gives a lower bound of the form
`N * exp(-C sqrt(log(N))) ≤ roth_number N`.
A significant refinement of Roth's theorem by Bloom and Sisask announced in 2020 gives
`roth_number N = O(N / (log N)^(1+c))` for an absolute constant `c`. -/
def roth_number_nat : ℕ →o ℕ :=
⟨λ n, add_roth_number (range n), add_roth_number.mono.comp range_mono⟩

lemma roth_number_nat_def (n : ℕ) : roth_number_nat n = add_roth_number (range n) := rfl

lemma roth_number_nat_le (N : ℕ) : roth_number_nat N ≤ N :=
(add_roth_number_le _).trans (card_range _).le

lemma roth_number_nat_spec (n : ℕ) :
  ∃ t ⊆ range n, t.card = roth_number_nat n ∧ add_salem_spencer (t : set ℕ) :=
add_roth_number_spec _

/-- A verbose specialization of `add_salem_spencer.le_add_roth_number`, sometimes convenient in
practice. -/
lemma add_salem_spencer.le_roth_number_nat (s : finset ℕ) (hs : add_salem_spencer (s : set ℕ))
  (hsn : ∀ x ∈ s, x < n) (hsk : s.card = k) :
  k ≤ roth_number_nat n :=
hsk.ge.trans $ hs.le_add_roth_number $ λ x hx, mem_range.2 $ hsn x hx

/-- The Roth number is a subadditive function. Note that by Fekete's lemma this shows that
the limit `roth_number N / N` exists, but Roth's theorem gives the stronger result that this
limit is actually `0`. -/
lemma roth_number_nat_add_le (M N : ℕ) :
  roth_number_nat (M + N) ≤ roth_number_nat M + roth_number_nat N :=
begin
  simp_rw roth_number_nat_def,
  rw [range_add_eq_union, ←add_roth_number_map_add_left (range N) M],
  exact add_roth_number_union_le _ _,
end

@[simp] lemma roth_number_nat_zero : roth_number_nat 0 = 0 := rfl

lemma add_roth_number_Ico (a b : ℕ) : add_roth_number (Ico a b) = roth_number_nat (b - a) :=
begin
  obtain h | h := le_total b a,
  { rw [tsub_eq_zero_of_le h, Ico_eq_empty_of_le h, roth_number_nat_zero, add_roth_number_empty] },
  convert add_roth_number_map_add_left _ a,
  rw [range_eq_Ico, map_eq_image],
  convert (image_add_left_Ico 0 (b - a) _).symm,
  exact (add_tsub_cancel_of_le h).symm,
end

open asymptotics filter

lemma roth_number_nat_is_O_with_id :
  is_O_with 1 (λ N, (roth_number_nat N : ℝ)) (λ N, (N : ℝ)) at_top :=
is_O_with.of_bound $ by simpa only [one_mul, real.norm_coe_nat, nat.cast_le]
  using eventually_of_forall roth_number_nat_le

/-- The Roth number has the trivial bound `roth_number N = O(N)`. -/
lemma roth_number_nat_is_O_id : is_O (λ N, (roth_number_nat N : ℝ)) (λ N, (N : ℝ)) at_top :=
roth_number_nat_is_O_with_id.is_O

end roth_number_nat
