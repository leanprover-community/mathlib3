/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.asymptotics.asymptotics

/-!
# Salem-Spencer sets and Roth numbers

This file defines Salem-Spencer sets, the Roth number of a set and calculates small Roth numbers.

A Salem-Spencer set is a set without arithmetic progressions of length `3`. Equivalently, the
average of any two distinct elements is not in the set.

The Roth number of a finset is the size of its biggest Salem-Spencer subset. This is a more general
definition than the one often found in mathematical litterature, where the `n`-th Roth number is
the size of the biggest Salem-Spencer subset of `{0, ..., n - 1}`.

## Main declarations

* `mul_salem_spencer`: Predicate for a set to be multiplicative Salem-Spencer.
* `add_salem_spencer`: Predicate for a set to be Salem-Spencer.
* `roth_number`: The Roth number of a finset.
* `roth_number_nat`: The Roth number of a natural. This corresponds to
  `roth_number (finset.range n)`.

## Tags

Salem-Spencer, Roth, arithmetic progression, average
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

@[to_additive, simp]
lemma mul_salem_spencer_empty : mul_salem_spencer (∅ : set α) := λ x _ _ hx, hx.elim

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
  mul_salem_spencer ((λ x, x * a) '' s) ↔ mul_salem_spencer s :=
⟨λ hs b c d hb hc hd h, mul_right_cancel (hs (set.mem_image_of_mem _ hb) (set.mem_image_of_mem _ hc)
  (set.mem_image_of_mem _ hd) $ by rw [mul_mul_mul_comm, h, mul_mul_mul_comm]),
  mul_salem_spencer.mul_right⟩

end cancel_comm_monoid

section comm_cancel_monoid_with_zero
variables [comm_cancel_monoid_with_zero α] [no_zero_divisors α] {s : set α} {a : α}

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

lemma mul_salem_spencer_mul_left_iff₀ (ha : a ≠ 0) : mul_salem_spencer ((*) a '' s) ↔ mul_salem_spencer s :=
⟨λ hs b c d hb hc hd h, mul_left_cancel₀ ha
  (hs (set.mem_image_of_mem _ hb) (set.mem_image_of_mem _ hc) (set.mem_image_of_mem _ hd) $
  by rw [mul_mul_mul_comm, h, mul_mul_mul_comm]),
  λ hs, hs.mul_left₀ ha⟩

lemma mul_salem_spencer_mul_right_iff₀ (ha : a ≠ 0) :
  mul_salem_spencer ((λ x, x * a) '' s) ↔ mul_salem_spencer s :=
⟨λ hs b c d hb hc hd h, mul_right_cancel₀ ha
  (hs (set.mem_image_of_mem _ hb) (set.mem_image_of_mem _ hc) (set.mem_image_of_mem _ hd) $
  by rw [mul_mul_mul_comm, h, mul_mul_mul_comm]),
  λ hs, hs.mul_right₀ ha⟩

end comm_cancel_monoid_with_zero

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

/-- The Roth number of a finset is the cardinality of its biggest Salem-Spencer subset. The usual
Roth number corresponds to `roth_number (finset.range n)`, see `roth_number_nat`. -/
@[to_additive]
def mul_roth_number : finset α →ₘ ℕ :=
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
begin
  convert le_find_greatest (card_le_of_subset h) _,
  exact ⟨s, h, rfl, hs⟩,
end

@[to_additive]
lemma mul_salem_spencer.roth_number_eq (hs : mul_salem_spencer (s : set α)) :
  mul_roth_number s = s.card :=
(mul_roth_number_le _).antisymm $ hs.le_mul_roth_number $ subset.refl _

@[to_additive]
lemma mul_roth_number_union_le (s t : finset α) :
  mul_roth_number (s ∪ t) ≤ mul_roth_number s + mul_roth_number t :=
let ⟨u, hus, hcard, hu⟩ := mul_roth_number_spec (s ∪ t) in
calc
  mul_roth_number (s ∪ t)
      = u.card : hcard.symm
  ... = (u ∩ s ∪ u ∩ t).card
      : by rw [←finset.inter_distrib_left, (inter_eq_left_iff_subset _ _).2 hus]
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
  rw finset.coe_product,
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
begin
  convert mul_roth_number_map_mul_left s a,
  ext,
  exact mul_comm _ _,
end

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
def roth_number_nat : ℕ →ₘ ℕ :=
⟨λ n, add_roth_number (range n), add_roth_number.mono.comp range_mono⟩

lemma roth_number_nat_def (n : ℕ) : roth_number_nat n = add_roth_number (range n) := rfl

lemma roth_number_nat_le (N : ℕ) : roth_number_nat N ≤ N :=
(add_roth_number_le _).trans (card_range _).le

/-- A verbose specialization of `add_salem_spencer.le_add_roth_number`, sometimes convenient in
practice. -/
lemma add_salem_spencer.le_roth_number_nat (s : finset ℕ) (hs : add_salem_spencer (s : set ℕ))
  (hsn : ∀ x ∈ s, x < n) (hsk : s.card = k) :
  k ≤ roth_number_nat n :=
begin
  rw ←hsk,
  exact hs.le_add_roth_number (λ x hx, mem_range.2 $ hsn x hx),
end

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

open asymptotics filter

lemma trivial_roth_bound' : is_O_with 1 (λ N, (roth_number_nat N : ℝ)) (λ N, (N : ℝ)) at_top :=
is_O_with.of_bound $ by simpa only [one_mul, real.norm_coe_nat, nat.cast_le]
  using eventually_of_forall roth_number_nat_le

/-- The Roth number has the trivial bound `roth_number N = O(N)`. -/
lemma trivial_roth_bound : is_O (λ N, (roth_number_nat N : ℝ)) (λ N, (N : ℝ)) at_top :=
is_O_iff_is_O_with.2 ⟨1, trivial_roth_bound'⟩

end roth_number_nat

/-!
### Explicit values

Some lemmas and calculations of the Roth number for (very) small naturals.

Sequence [A003002](http://oeis.org/A003002) in the OEIS.
-/

section explicit_values

/-- A simpler `decidable` instance for Salem-Spencer sets of naturals. We use it to prove small
values of the Roth number by `rfl`/`dec_trivial`. -/
def add_salem_spencer.decidable_nat {s : finset ℕ} : decidable (add_salem_spencer (s : set ℕ)) :=
decidable_of_iff (∀ (a ∈ s) (b ∈ s), a < b → b + (b - a) ∉ s) begin
  rw add_salem_spencer_iff_eq_right,
  refine ⟨λ hs a b c ha hb hc habc, _, λ hs a ha b hb hab h, _⟩,
  { by_contra h,
    obtain hac | hac := lt_or_gt_of_ne h,
    { refine hs _ ha _ hc hac _,
      rwa [←add_tsub_assoc_of_le hac.le, ←habc, add_tsub_cancel_left] },
    { have hbc : b < c := lt_of_not_ge' (λ h, (add_lt_add_of_lt_of_le hac h).ne' habc),
      refine hs _ hb _ hc hbc _,
      rwa [←add_tsub_assoc_of_le hbc.le, ←habc, add_tsub_cancel_right] } },
  { refine hab.ne (hs ha h hb _),
    rw [←add_tsub_assoc_of_le hab.le, add_tsub_cancel_of_le (le_add_left hab.le)] }
end

local attribute [instance] add_salem_spencer.decidable_nat

lemma roth_number_nat_succ_le {m n : ℕ} (hn : roth_number_nat n ≤ m)
  (h : ∀ s ∈ (powerset_len m (range n)).filter (λ (s : finset ℕ), add_salem_spencer (s : set ℕ)),
          ∃ z ∈ s, n ≤ z + z ∧ z + z - n ∈ s) :
  roth_number_nat (n + 1) ≤ m :=
begin
  apply nat.le_of_lt_succ,
  change roth_number_nat (n + 1) < m.succ,
  apply add_roth_number_lt_of_forall_not_add_salem_spencer,
  simp only [range_succ, powerset_len_succ_insert not_mem_range_self, mem_union, mem_image,
    or_imp_distrib, forall_and_distrib, and_imp, coe_insert, forall_exists_index,
    forall_apply_eq_imp_iff₂],
  refine ⟨_, λ s hs hsN, _⟩,
  { simp only [mem_powerset_len, and_imp],
    rw ←not_lt at hn,
    exact λ x hx₁ hx₂ h, hn (h.le_roth_number_nat _ (λ x hx, mem_range.1 (hx₁ hx)) hx₂) },
  simp only [and_imp, exists_prop, mem_filter, exists_and_distrib_left] at h,
  obtain ⟨a, hNa, ha, haN⟩ := h s hs (hsN.mono $ set.subset_insert _ _),
  rw [mem_powerset_len] at hs,
  replace hs := hs.1 haN,
  rw hsN (set.mem_insert_of_mem _ haN) (set.mem_insert _ _) (set.mem_insert_of_mem _ ha) _ at hs,
  exact not_mem_range_self hs,
  { rw [tsub_add_cancel_of_le hNa] }
end

/-- In conjunction with `dec_trivial`, this allows quick computation of small Roth numbers. -/
lemma roth_number_nat_succ_eq {m n : ℕ} (hn : roth_number_nat n = m)
  (h : ∀ s ∈ (powerset_len m (range n)).filter (λ (s : finset ℕ), add_salem_spencer (s : set ℕ)),
          ∃ z ∈ s, n ≤ z + z ∧ z + z - n ∈ s) :
  roth_number_nat (n + 1) = m :=
(roth_number_nat_succ_le hn.le h).antisymm $ hn.ge.trans $ roth_number_nat.mono n.le_succ

@[simp] lemma roth_number_nat_zero : roth_number_nat 0 = 0 := rfl
@[simp] lemma roth_number_nat_one : roth_number_nat 1 = 1 := rfl
@[simp] lemma roth_number_nat_two : roth_number_nat 2 = 2 := rfl
@[simp] lemma roth_number_nat_three : roth_number_nat 3 = 2 := rfl
@[simp] lemma roth_number_nat_four : roth_number_nat 4 = 3 := rfl
@[simp] lemma roth_number_nat_five : roth_number_nat 5 = 4 := rfl
@[simp] lemma roth_number_nat_six : roth_number_nat 6 = 4 := rfl
@[simp] lemma roth_number_nat_seven : roth_number_nat 7 = 4 := rfl
@[simp] lemma roth_number_nat_eight : roth_number_nat 8 = 4 := rfl
@[simp] lemma roth_number_nat_nine : roth_number_nat 9 = 5 := rfl
@[simp] lemma roth_number_nat_ten : roth_number_nat 10 = 5 := dec_trivial
@[simp] lemma roth_number_nat_eleven : roth_number_nat 11 = 6 :=
begin
  apply le_antisymm,
  { simpa using roth_number_nat_add_le 3 8 },
  apply add_salem_spencer.le_roth_number_nat {0, 1, 3, 7, 8, 10},
  { dec_trivial },
  { simp },
  { simp }
end

@[simp] lemma roth_number_twelve : roth_number_nat 12 = 6 :=
roth_number_nat_succ_eq roth_number_nat_eleven $ by dec_trivial

@[simp] lemma roth_number_nat_thirteen : roth_number_nat 13 = 7 :=
begin
  apply le_antisymm,
  { simpa using roth_number_nat_add_le 10 3 },
  apply add_salem_spencer.le_roth_number_nat {0, 1, 3, 4, 9, 10, 12},
  { dec_trivial },
  { simp },
  { simp }
end

@[simp] lemma roth_number_nat_fourteen : roth_number_nat 14 = 8 :=
begin
  apply le_antisymm,
  { simpa using roth_number_nat_add_le 11 3 },
  apply add_salem_spencer.le_roth_number_nat {0, 1, 3, 4, 9, 10, 12, 13}, -- unique example
  { dec_trivial },
  { simp },
  { simp }
end

end explicit_values
