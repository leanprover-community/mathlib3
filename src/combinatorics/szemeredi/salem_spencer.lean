/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib
import analysis.asymptotics.asymptotics
import data.complex.exponential_bounds
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import data.nat.digits

/-!
# Salem-Spencer sets and the Roth number

This file defines Salem-Spencer sets, the Roth number of a set and calculate small Roth numbers.

A Salem-Spencer set is a set without arithmetic progressions of length `3`. Equivalently, the
average of any two distinct elements is not in the set.

The Roth number of a finset is the size of its biggest Salem-Spencer subset. This is a more general
definition than the one often found in mathematical litterature, where the `n`-th Roth number is
the size of the biggest Salem-Spencer subset of `{0, ..., n - 1}`.

## Main declarations

* `is_salem_spencer`: Predicate for a set to be Salem-Spencer.
* `roth_number`: The Roth number of a finset.
* `roth_number_nat`: The Roth number of a natural. This corresponds to
  `roth_number (finset.range n)`.

## Tags

Salem-Spencer, Roth, arithmetic progression, average
-/

open finset nat

variables {α β : Type*}

section salem_spencer
section add_monoid
variables [add_monoid α] [add_monoid β] (s t : set α)

/-- A Salem-Spencer, aka non averaging, set `s` in an additive monoid is a set such that the
average of any two distinct elements is not in the set. -/
def is_salem_spencer : Prop := ∀ ⦃a b c⦄, a ∈ s → b ∈ s → c ∈ s → a + b = 2 • c → a = b

/-- Whether a given finset is Salem-Spencer is decidable. -/
instance {α : Type*} [decidable_eq α] [add_monoid α] {s : finset α} :
  decidable (is_salem_spencer (s : set α)) :=
decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a + b = 2 • c → a = b)
  ⟨λ h a b c ha hb hc, h a ha b hb c hc, λ h a ha b hb c hc, h ha hb hc⟩

variables {s t}

lemma is_salem_spencer.mono (h : t ⊆ s) (hs : is_salem_spencer s) : is_salem_spencer t :=
λ a b c ha hb hc, hs (h ha) (h hb) (h hc)

@[simp] lemma is_salem_spencer_empty : is_salem_spencer (∅ : set α) := λ x _ _ hx, hx.elim

lemma is_salem_spencer.prod {t : set β} (hs : is_salem_spencer s) (ht : is_salem_spencer t) :
  is_salem_spencer (s.prod t) :=
λ a b c ha hb hc h,
  prod.ext (hs ha.1 hb.1 hc.1 (prod.ext_iff.1 h).1) (ht ha.2 hb.2 hc.2 (prod.ext_iff.1 h).2)

lemma is_salem_spencer_pi {ι : Type*} {α : ι → Type*} [Π i, add_monoid (α i)] {s : Π i, set (α i)}
  (hs : ∀ i, is_salem_spencer (s i)) :
  is_salem_spencer ((set.univ : set ι).pi s) :=
λ a b c ha hb hc h, funext $ λ i, hs i (ha i trivial) (hb i trivial) (hc i trivial) $ congr_fun h i

end add_monoid

section add_cancel_comm_monoid
variables [add_cancel_comm_monoid α] {s t : set α} {a : α}

lemma is_salem_spencer.add_left (hs : is_salem_spencer s) : is_salem_spencer ((+) a '' s) :=
begin
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h,
  rw [add_add_add_comm, smul_add, two_nsmul] at h,
  rw hs hb hc hd (add_left_cancel h),
end

lemma is_salem_spencer.add_right (hs : is_salem_spencer s) : is_salem_spencer ((λ x, x + a) '' s) :=
begin
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h,
  rw [add_add_add_comm, smul_add 2 _, two_nsmul a] at h,
  rw hs hb hc hd (add_right_cancel h),
end

end add_cancel_comm_monoid
end salem_spencer

section roth_number
section monoid
variables [decidable_eq α] [add_monoid α] (s t : finset α)

/-- The Roth number of a finset is the cardinality of its biggest Salem-Spencer subset. The usual
Roth number corresponds to `roth_number (finset.range n)`, see `roth_number_nat`. -/
def roth_number : finset α →ₘ ℕ :=
⟨λ s, nat.fand_greatest (λ m, ∃ t ⊆ s, t.card = m ∧ is_salem_spencer (t : set α)) s.card,
begin
  rintro t u htu,
  refine nat.fand_greatest_mono (λ m, _) (card_le_of_subset htu),
  rintro ⟨v, hvt, hv⟩,
  exact ⟨v, hvt.trans htu, hv⟩,
end⟩

lemma roth_number_le : roth_number s ≤ s.card := by convert nat.fand_greatest_le s.card

lemma roth_number_spec : ∃ t ⊆ s, t.card = roth_number s ∧ is_salem_spencer (t : set α) :=
@nat.fand_greatest_spec (λ m, ∃ t ⊆ s, t.card = m ∧ is_salem_spencer (t : set α)) _ _ _
  (nat.zero_le _) ⟨∅, empty_subset _, card_empty, is_salem_spencer_empty⟩

variables {s t} {n : ℕ}

lemma is_salem_spencer.le_roth_number (hs : is_salem_spencer (s : set α)) (h : s ⊆ t) :
  s.card ≤ roth_number t :=
begin
  convert le_fand_greatest (card_le_of_subset h) _,
  exact ⟨s, h, rfl, hs⟩,
end

lemma is_salem_spencer.roth_number_eq (hs : is_salem_spencer (s : set α)) :
  roth_number s = s.card :=
(roth_number_le _).antisymm $ hs.le_roth_number $ subset.refl _

lemma roth_number_union_le (s t : finset α) : roth_number (s ∪ t) ≤ roth_number s + roth_number t :=
let ⟨u, hsubs, hcard, hu⟩ := roth_number_spec (s ∪ t) in
calc
  roth_number (s ∪ t)
      = u.card : hcard.symm
  ... = (u ∩ s ∪ u ∩ t).card
      : by rw [←finset.inter_distrib_left, (inter_eq_left_iff_subset _ _).2 hsubs]
  ... ≤ (u ∩ s).card + (u ∩ t).card : card_union_le _ _
  ... ≤ roth_number s + roth_number t
      : add_le_add ((hu.mono $ inter_subset_left _ _).le_roth_number $ inter_subset_right _ _)
          ((hu.mono $ inter_subset_left _ _).le_roth_number $ inter_subset_right _ _)

lemma roth_number_lt_of_forall_not_salem_spencer
  (h : ∀ t ∈ powerset_len n s, ¬is_salem_spencer ((t : finset α) : set α)) :
  roth_number s < n :=
begin
  obtain ⟨t, hts, hcard, ht⟩ := roth_number_spec s,
  rw [←hcard, ←not_le],
  intro hn,
  obtain ⟨u, hut, rfl⟩ := exists_smaller_set t n hn,
  exact h _ (mem_powerset_len.2 ⟨hut.trans hts, rfl⟩) (ht.mono hut),
end

open_locale pointwise

-- True?
-- lemma roth_number_add_le (s t : finset α) :
  -- roth_number (s + t) ≤ roth_number s * roth_number t :=

end monoid

section add_cancel_comm_monoid
variables [decidable_eq α] [add_cancel_comm_monoid α] (s t : finset α) (a : α)

lemma is_salem_spencer_iff_eq_right {s : set α} :
  is_salem_spencer s ↔ ∀ ⦃a b c⦄, a ∈ s → b ∈ s → c ∈ s → a + b = 2 • c → a = c :=
begin
  refine forall_congr (λ a, forall_congr $ λ b, forall_congr $ λ c, forall_congr $
    λ _, forall_congr $ λ _, forall_congr $ λ _,  forall_congr $ λ habc, ⟨_, _⟩),
  { rintro rfl,
    rw ←two_nsmul at habc,
    sorry
  },
  { rintro rfl,
    rw two_nsmul at habc,
    exact (add_left_cancel habc).symm }
end

-- BM: this is (obviously) a special case of the above, but i'm not convinced the above is
-- true; the `sorry` is definitely false (eg use α = klein four group). For now I'll use this
-- special case to make things build again below without needing sorry, ideally we can kill it
lemma nat_is_salem_spencer_iff_eq_right {s : set ℕ} :
  is_salem_spencer s ↔ ∀ ⦃a b c⦄, a ∈ s → b ∈ s → c ∈ s → a + b = 2 • c → a = c :=
begin
  refine forall_congr (λ a, forall_congr $ λ b, forall_congr $ λ c, forall_congr $
    λ _, forall_congr $ λ _, forall_congr $ λ _,  forall_congr $ λ habc, ⟨_, _⟩),
  { rintro rfl,
    rw ←two_nsmul at habc,
    simpa using habc },
  { rintro rfl,
    rw two_nsmul at habc,
    exact (add_left_cancel habc).symm }
end

@[simp] lemma roth_number_map_add_left :
  roth_number (s.map $ add_left_embedding a) = roth_number s :=
begin
  sorry
end

@[simp] lemma roth_number_map_add_right :
  roth_number (s.map $ add_right_embedding a) = roth_number s :=
begin
  sorry
end

end add_cancel_comm_monoid
end roth_number

section roth_number_nat
variables {s : finset ℕ} {k n : ℕ}

/-- The Roth number of a natural `N` is the largest integer `m` for which there is a subset of
`range N` of size `m` with no arithmetic progression of length 3.
Trivially, `roth_number N ≤ N`, but Roth's theorem (proved in ...) shows that
`roth_number N = o(N)` and the construction by Behrend `roth_behrend_bound` gives a lower bound
of the form `N * exp(-C sqrt(log(N))) ≤ roth_number N`.
A significant refinement of Roth's theorem by Bloom and Sisask announced in 2020 gives
`roth_number N = O(N / (log N)^(1+c))` for an absolute constant `c`. -/
def roth_number_nat : ℕ →ₘ ℕ := ⟨λ n, roth_number (range n), roth_number.mono.comp range_mono⟩

lemma roth_number_nat_def (n : ℕ) : roth_number_nat n = roth_number (range n) := rfl

lemma roth_number_nat_le (N : ℕ) : roth_number_nat N ≤ N :=
(roth_number_le _).trans (card_range _).le

/-- A verbose specialization of `is_salem_spencer.le_roth_number`. -/
lemma is_salem_spencer.le_roth_number_nat (s : finset ℕ) (hs : is_salem_spencer (s : set ℕ))
  (hsn : ∀ x ∈ s, x < n) (hsk : s.card = k) :
  k ≤ roth_number_nat n :=
begin
  rw ←hsk,
  exact hs.le_roth_number (λ x hx, mem_range.2 $ hsn x hx),
end

/-- The Roth number is a subadditive function. Note that by Fekete's lemma this shows that
the limit `roth_number N / N` exists, but Roth's theorem gives the stronger result that this
limit is actually `0`. -/
lemma roth_number_nat_add_le (M N : ℕ) :
  roth_number_nat (M + N) ≤ roth_number_nat M + roth_number_nat N :=
begin
  simp_rw roth_number_nat_def,
  rw [range_add_eq_union, ←roth_number_map_add_right (range N) M],
  exact roth_number_union_le _ _,
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
-/

section explicit_values

-- lemma has_three_ap_iff {s : finset ℕ} :
--   (∃ (x ∈ s) (y ∈ s), x < y ∧ y + (y - x) ∈ s) ↔ has_three_ap (s : set ℕ) :=
-- begin
--   simp only [has_three_ap, exists_prop, mem_coe, exists_and_distrib_left, ne.def],
--   split,
--   { rintro ⟨x, hx, y, xy, hy, hz⟩,
--     refine ⟨x, y, xy.ne, _, hz, hy, hx, _⟩,
--     rw [←nat.add_sub_assoc xy.le, ←nat.add_sub_assoc (le_add_right xy.le),
--       nat.add_sub_cancel_left] },
--   { rintro ⟨x, y, xy, z, hz, hy, hx, e⟩,
--     cases lt_or_gt_of_ne xy,
--     { refine ⟨x, hx, y, h, hy, _⟩,
--       rwa [←nat.add_sub_assoc h.le, ←e, nat.add_sub_cancel_left] },
--     { have zy : z < y,
--       { rwa [←add_lt_add_iff_right y, ←e, add_comm, add_lt_add_iff_right] },
--       refine ⟨z, hz, y, zy, hy, _⟩,
--       rwa [←nat.add_sub_assoc zy.le, ←e, nat.add_sub_cancel] } }
-- end

/-- A simpler `decidable` instance for Salem-Spencer sets of naturals. We use it to prove small
values of the Roth number by `rfl`/`dec_trivial`. -/
def is_salem_spencer.decidable_nat {s : finset ℕ} : decidable (is_salem_spencer (s : set ℕ)) :=
decidable_of_iff (∀ (a ∈ s) (b ∈ s), a < b → b + (b - a) ∉ s) begin
  rw is_salem_spencer_iff_eq_right,
  refine ⟨λ hs a b c ha hb hc habc, _, λ hs a ha b hb hab h, _⟩,
  { by_contra h,
    obtain hac | hac := lt_or_gt_of_ne h,
    { refine hs _ ha _ hc hac _,
      rwa [←add_tsub_assoc_of_le hac.le, ←two_nsmul, ←habc, add_tsub_cancel_left] },
    { have hbc : b < c,
      {
        sorry
      },
      refine hs _ hb _ hc hbc _,
      rwa [←add_tsub_assoc_of_le hbc.le, ←two_nsmul, ←habc, add_tsub_cancel_right] } },
  { refine hab.ne (hs ha h hb _),
    rw [←add_tsub_assoc_of_le hab.le, add_tsub_cancel_of_le (le_add_left hab.le), two_nsmul] }
end

local attribute [instance] is_salem_spencer.decidable_nat

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
  apply is_salem_spencer.le_roth_number_nat {0, 1, 3, 7, 8, 10},
  { dec_trivial },
  { simp },
  { simp }
end

@[simp] lemma roth_number_twelve : roth_number_nat 12 = 6 :=
begin
  apply le_antisymm,
  { rw ←nat.lt_succ_iff,
    apply roth_number_lt_of_forall_not_salem_spencer,
    dec_trivial },
  simpa using roth_number_nat_mono (show 11 ≤ 12, by norm_num),
end

@[simp] lemma roth_number_thirteen : roth_number_nat 13 = 7 :=
begin
  apply le_antisymm,
  { simpa using roth_number_nat_add_le 12 1 },
  apply is_salem_spencer.le_roth_number_nat {0, 1, 3, 4, 9, 10, 12},
  { dec_trivial },
  { simp },
  { simp }
end

@[simp] lemma roth_number_fourteen : roth_number_nat 14 = 8 :=
begin
  apply le_antisymm,
  { simpa using roth_number_nat_add_le 12 2 },
  apply is_salem_spencer.le_roth_number_nat {0, 1, 3, 4, 9, 10, 12, 13}, -- unique example
  { dec_trivial },
  { simp },
  { simp }
end

lemma roth_number_dec_upper_bound {N M : ℕ}
  (h₂ : roth_number_nat N ≤ M)
  (h : ∀ s ∈ (powerset_len M (range N)).filter (λ (s : finset ℕ), is_salem_spencer (s : set ℕ)),
          ∃ z ∈ s, N ≤ z + z ∧ z + z - N ∈ s) :
  roth_number_nat (N+1) ≤ M :=
begin
  apply nat.le_of_lt_succ,
  change roth_number_nat (N+1) < M.succ,
  apply roth_number_lt_of_forall_not_salem_spencer,
  simp only [range_succ, powerset_len_succ_insert not_mem_range_self, mem_union, mem_image,
    or_imp_distrib, forall_and_distrib, and_imp, coe_insert, forall_exists_index,
    forall_apply_eq_imp_iff₂],
  refine ⟨_, λ s hs hsN, _⟩,
  { simp only [mem_powerset_len, and_imp],
    rw ←not_lt at h₂,
    exact λ x hx₁ hx₂ h, h₂ (h.le_roth_number_nat _ (λ x hx, mem_range.1 (hx₁ hx)) hx₂) },
  simp only [and_imp, exists_prop, mem_filter, exists_and_distrib_left] at h,
  obtain ⟨a, hNa, ha, haN⟩ := h s hs (hsN.mono $ set.subset_insert _ _),
  rw [mem_powerset_len] at hs,
  replace hs := hs.1 haN,
  rw hsN (set.mem_insert_of_mem _ haN) (set.mem_insert _ _) (set.mem_insert_of_mem _ ha) _ at hs,
  exact not_mem_range_self hs,
  { rw [tsub_add_cancel_of_le hNa, two_nsmul] }
end

-- lemma roth_number_sixty_four : 20 ≤ roth_number 64 :=
-- begin
--   apply le_roth_number_of_not_has_three_ap {1,3,8,9,11,16,20,22,25,26,38,40,45,46,48,53,57,59,62,63},
--   { simp only [subset_iff, mem_range, mem_insert, mem_singleton, forall_eq_or_imp],
--     simp },
--   { dec_trivial },
--   { rw [card_insert_of_not_mem, card_insert_of_not_mem],

--   }
-- end

-- @[simp] lemma roth_number_fifteen : roth_number 15 = 8 :=
-- begin
--   apply le_antisymm,
--   { refine roth_number_dec_upper_bound (by simp) _,
--     dec_trivial },
--   simpa using roth_number_monotone (show 14 ≤ 15, by norm_num),
--   -- dec_trivial,
-- end
-- @[simp] lemma roth_number_sixteen : roth_number 16 = 8 := sorry
-- @[simp] lemma roth_number_seventeen : roth_number 17 = 8 := sorry
-- @[simp] lemma roth_number_eighteen : roth_number 18 = 8 :=
-- begin
--   apply le_antisymm,
--   { refine roth_number_dec_upper_bound (by simp) _,
--     dec_trivial
--     },
--   simpa using roth_number_monotone (show 14 ≤ 18, by norm_num),
--   -- dec_trivial,
-- end

-- lemma roth_number_nineteen_le : roth_number 19 ≤ 8 :=
-- begin

-- end

-- @[simp] lemma roth_number_nineteen : roth_number 19 = 8 :=
-- begin
--   apply le_antisymm,
--   { rw ←nat.lt_succ_iff,
--     apply roth_number_lt_of_forall_not_salem_spencer,

--   },
--   simpa using roth_number_monotone (show 14 ≤ 19, by norm_num)
-- end

end explicit_values

/-! The Behrend construction giving lower bounds on the Roth number. -/
namespace behrend

open_locale big_operators

def sphere (n d : ℕ) : finset (fin n → ℕ) :=
fintype.pi_finset (λ _, range d)

lemma mem_sphere {n d : ℕ} (x : fin n → ℕ) : x ∈ sphere n d ↔ ∀ i, x i < d := by simp [sphere]

lemma bound_of_mem_sphere {n d : ℕ} {x : fin n → ℕ} (hx : x ∈ sphere n d) : ∀ i, x i < d :=
(mem_sphere _).1 hx

def sphere_slice (n d k : ℕ) : finset (fin n → ℕ) :=
(sphere n d).filter (λ x, ∑ i, x i^2 = k)

lemma sphere_slice_zero {n d : ℕ} : sphere_slice n d 0 ⊆ {λ _, 0} :=
begin
  intros x hx,
  simp only [sphere_slice, nat.succ_pos', sum_eq_zero_iff, mem_filter, mem_univ, forall_true_left,
    pow_eq_zero_iff] at hx,
  simp only [mem_singleton, function.funext_iff],
  apply hx.2
end

lemma sphere_to_nat_mod {n d : ℕ} (a : fin n.succ → ℕ) :
  from_digits d a % d = a 0 % d :=
by rw [from_digits_succ, nat.add_mul_mod_self_right]

lemma sphere_to_nat_eq_iff {n d : ℕ} {x₁ x₂ : fin n.succ → ℕ}
  (hx₁ : ∀ i, x₁ i < d) (hx₂ : ∀ i, x₂ i < d) :
  from_digits d x₁ = from_digits d x₂ ↔
    x₁ 0 = x₂ 0 ∧ from_digits d (x₁ ∘ fin.succ) = from_digits d (x₂ ∘ fin.succ) :=
begin
  split,
  { intro h,
    have : from_digits d x₁ % d = from_digits d x₂ % d,
    { rw h },
    simp only [sphere_to_nat_mod, nat.mod_eq_of_lt (hx₁ _), nat.mod_eq_of_lt (hx₂ _)] at this,
    refine ⟨this, _⟩,
    rw [from_digits_succ, from_digits_succ, this, add_right_inj, mul_eq_mul_right_iff] at h,
    apply or.resolve_right h,
    apply (lt_of_le_of_lt (nat.zero_le _) (hx₁ 0)).ne' },
  rintro ⟨h₁, h₂⟩,
  rw [from_digits_succ', from_digits_succ', h₁, h₂],
end

lemma sphere_to_nat_inj_on {n d : ℕ} :
  set.inj_on (from_digits d) {x : fin n → ℕ | ∀ i, x i < d} :=
begin
  simp only [set.inj_on, set.mem_set_of_eq],
  intros x₁ hx₁ x₂ hx₂ h,
  induction n with n ih,
  { simp },
  ext i,
  have x := (sphere_to_nat_eq_iff hx₁ hx₂).1 h,
  refine fin.cases x.1 (function.funext_iff.1 (ih (λ _, _) (λ _, _) x.2)) i,
  { exact hx₁ _ },
  { exact hx₂ _ }
end

-- lemma sum_mul_sq_le_sq_mul_sq' {α : Type*} (s : finset α) (f g : α → ℝ)  :
--   (∑ i in s, f i * g i)^2 ≤ (∑ i in s, (f i)^2) * (∑ i in s, (g i)^2) :=
-- begin
--   simp only [←finset.sum_finset_coe _ s, pow_two],
--   exact real_inner_mul_inner_self_le (show euclidean_space ℝ s, from f ∘ coe)
--     (show euclidean_space ℝ s, from g ∘ coe),
-- end

-- theorem inner_eq_norm_mul_iff_real {F : Type u_3} [inner_product_space ℝ F] {x y : F} :
-- inner x y = ∥x∥ * ∥y∥ ↔ ∥y∥ • x = ∥x∥ • y

lemma sphere_strictly_convex {F : Type*} [inner_product_space ℝ F] {x y : F}
  (h : ∥x∥ = ∥y∥) (hx : x ≠ 0) (hxy : x ≠ y) : ∥(1/2 : ℝ) • (x + y)∥ < ∥x∥ :=
begin
  have := @inner_eq_norm_mul_iff_real _ _ x y,
  apply lt_of_pow_lt_pow 2 (norm_nonneg _) _,
  rw [norm_smul, mul_pow, norm_add_sq_real, h, add_right_comm, ←two_mul, ←mul_add, ←mul_assoc],
  suffices : inner x y < ∥y∥^2,
  { norm_num,
    linarith },
  apply lt_of_le_of_ne,
  { simpa [h, sq] using real_inner_le_norm x y },
  rw h at this,
  simp only [←sq] at this,
  rw [ne.def, this],
  refine (smul_right_injective _ _).ne hxy,
  rw ←h,
  simpa [←h] using hx,
end

lemma slice_norm {n d k : ℕ} {x : fin n → ℕ} (hx : x ∈ sphere_slice n d k) :
  @has_norm.norm (euclidean_space ℝ (fin n)) _ (coe ∘ x : fin n → ℝ) =
  real.sqrt k :=
begin
  rw pi_Lp.norm_eq_of_L2,
  simp only [real.norm_coe_nat, function.comp_app, ←nat.cast_pow, ←nat.cast_sum],
  congr' 2,
  simp only [sphere_slice, mem_filter] at hx,
  apply hx.2
end

lemma is_salem_spencer_sphere_slice (n d : ℕ) {k : ℕ} :
  is_salem_spencer (sphere_slice n d k : set (fin n → ℕ)) :=
begin
  intros x z y hx hz hy hxyz,
  rcases nat.eq_zero_or_pos k with rfl | hk,
  { rw [mem_singleton.1 (sphere_slice_zero hx), mem_singleton.1 (sphere_slice_zero hz)] },
  let x' : euclidean_space ℝ (fin n) := (coe ∘ x : fin n → ℝ),
  let y' : euclidean_space ℝ (fin n) := (coe ∘ y : fin n → ℝ),
  let z' : euclidean_space ℝ (fin n) := (coe ∘ z : fin n → ℝ),
  rw two_nsmul at hxyz,
  have : x' + z' = y' + y',
  { simpa [function.funext_iff, ←nat.cast_add] using hxyz },
  by_contra hxz,
  have nxz : x' ≠ z',
  { simpa [function.funext_iff] using hxz },
  have nxy : x' ≠ y',
  { intro t,
    apply nxz,
    rw ←t at this,
    exact add_right_injective _ this.symm },
  have yeq : (1 / 2 : ℝ) • (x' + z') = y',
  { rw [one_div, inv_smul_eq_iff₀ (show (2 : ℝ) ≠ 0, by norm_num)],
    simp only [function.funext_iff, pi.add_apply] at hxyz,
    ext j,
    simp only [algebra.id.smul_eq_mul, pi.add_apply, pi.smul_apply, ←nat.cast_add, two_mul,
      nat.cast_inj, hxyz] },
  have xz : ∥x'∥ = ∥z'∥,
  { simp only [slice_norm hx, slice_norm hz] },
  have i₂ := @sphere_strictly_convex (euclidean_space ℝ (fin n)) _ x' z' xz _ nxz,
  { rw [yeq, slice_norm hx, slice_norm hy] at i₂,
    simpa using i₂ },
  suffices : ∥x'∥ ≠ 0,
  { simpa using this },
  rw slice_norm hx,
  simp [hk.ne'],
end

lemma is_salem_spencer_image_slice {n d k : ℕ} :
  is_salem_spencer ((finset.image (from_digits (2 * d - 1)) (sphere_slice n d k)) : set ℕ) :=
begin
  -- rw nat_is_salem_spencer_iff_eq_right,
  rintro a b c ha hb hc,
  rw [mem_coe, mem_image] at ha hb hc,
  obtain ⟨x, hx, rfl⟩ := ha,
  obtain ⟨y, hy, rfl⟩ := hc,
  obtain ⟨z, hz, rfl⟩ := hb,
  have hx' : ∀ i, x i < d := bound_of_mem_sphere (mem_filter.1 hx).1,
  have hy' : ∀ i, y i < d := bound_of_mem_sphere (mem_filter.1 hy).1,
  have hz' : ∀ i, z i < d := bound_of_mem_sphere (mem_filter.1 hz).1,
  rw [←from_digits_two_add hx' hz', two_nsmul, ←from_digits_two_add hy' hy'],
  rintro (t : from_digits (2 * d - 1) (x + z) = from_digits (2 * d - 1) (y + y)),
  rw sphere_to_nat_inj_on.eq_iff (λ i, (hx' i).trans_le weird_thing)
    (λ i, (hz' i).trans_le weird_thing),
  rw sphere_to_nat_inj_on.eq_iff (sum_bound hx' hz') (sum_bound hy' hy') at t,
  apply is_salem_spencer_sphere_slice n d hx hz hy,
  rwa two_nsmul,
end

@[simp] lemma sphere_size {n d : ℕ} : (sphere n d).card = d ^ n := by simp [sphere]

lemma sum_squares_bound_of_le {n d : ℕ} (x : fin n → ℕ) (hx : x ∈ sphere n d) :
  ∑ (i : fin n), (x i)^2 ≤ n * (d - 1)^2 :=
begin
  simp only [mem_sphere] at hx,
  have : ∀ i, x i^2 ≤ (d - 1)^2,
  { intro i,
    apply nat.pow_le_pow_of_le_left,
    apply nat.le_pred_of_lt (hx i) },
  apply (finset.sum_le_of_forall_le univ _ _ (λ i _, this i)).trans,
  simp,
end

lemma le_of_mem_sphere {n d : ℕ} : ∀ x ∈ sphere n d, x ≤ (λ i, d - 1) :=
λ x hx i, nat.le_pred_of_lt (bound_of_mem_sphere hx i)

lemma from_digits_le_of_mem_sphere {n d : ℕ} :
  ∀ x ∈ sphere n d, from_digits (2 * d - 1) x ≤ ∑ (i : fin n), (d - 1) * (2 * d - 1)^(i : ℕ) :=
λ x hx, from_digits_monotone (2 * d - 1) (le_of_mem_sphere x hx)

lemma behrend_bound_aux1 {n d k N : ℕ} (hd : 0 < d) (hN : (2 * d - 1)^n ≤ N):
  (sphere_slice n d k).card ≤ roth_number_nat N :=
begin
  refine is_salem_spencer_image_slice.le_roth_number_nat _ _ (card_image_of_inj_on _),
  { simp only [subset_iff, mem_image, and_imp, forall_exists_index, mem_range,
      forall_apply_eq_imp_iff₂, sphere_slice, mem_filter],
    rintro _ x hx _ rfl,
    apply ((from_digits_le_of_mem_sphere x hx).trans_lt (digits_sum_le hd)).trans_le hN },
  refine set.inj_on.mono (λ x, _) sphere_to_nat_inj_on,
  simp only [mem_coe, sphere_slice, mem_filter, mem_sphere, and_imp, set.mem_set_of_eq],
  exact λ h₁ h₂ i, (h₁ i).trans_le weird_thing,
end

lemma large_slice_aux (n d : ℕ) :
  ∃ k ∈ range (n * (d - 1)^2 + 1),
    (↑(d ^ n) / (↑(n * (d - 1)^2) + 1) : ℝ) ≤ (sphere_slice n d k).card :=
begin
  apply exists_le_card_fiber_of_mul_le_card_of_maps_to',
  { intros x hx,
    rw [mem_range, nat.lt_succ_iff],
    apply sum_squares_bound_of_le _ hx },
  { simp },
  { rw [card_range, _root_.nsmul_eq_mul, mul_div_assoc', nat.cast_add_one, mul_div_cancel_left],
    { simp },
    exact (nat.cast_add_one_pos _).ne' }
end

lemma large_slice {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
  ∃ k, (d ^ n / ↑(n * d^2) : ℝ) ≤ (sphere_slice n d k).card :=
begin
  obtain ⟨k, -, hk⟩ := large_slice_aux n d,
  refine ⟨k, _⟩,
  rw ←nat.cast_pow,
  refine (div_le_div_of_le_left _ _ _).trans hk,
  { exact nat.cast_nonneg _ },
  { exact nat.cast_add_one_pos _ },
  simp only [←le_sub_iff_add_le', nat.cast_mul, ←mul_sub, nat.cast_pow, nat.cast_sub hd, sub_sq,
    one_pow, nat.cast_one, mul_one, sub_add, sub_sub_self],
  apply one_le_mul_of_one_le_of_one_le,
  { rwa nat.one_le_cast },
  rw le_sub_iff_add_le,
  norm_num,
  exact le_mul_of_one_le_right zero_le_two (nat.one_le_cast.2 hd),
end
-- d ^ n / (n * d^2) ≤ (sphere_slice n d k).card

lemma behrend_bound_aux2 {n d N : ℕ} (hd : 0 < d) (hn : 0 < n) (hN : (2 * d - 1)^n ≤ N):
  (d ^ n / ↑(n * d^2) : ℝ) ≤ roth_number_nat N :=
begin
  obtain ⟨k, _⟩ := large_slice hn hd,
  apply h.trans,
  rw nat.cast_le,
  apply behrend_bound_aux1 hd hN,
end

lemma behrend_bound_aux3 {n d N : ℕ} (hd : 0 < d) (hn : 2 ≤ n) (hN : (2 * d - 1)^n ≤ N):
  (d ^ (n - 2) / n : ℝ) ≤ roth_number_nat N :=
begin
  convert behrend_bound_aux2 hd (zero_lt_two.trans_le hn) hN using 1,
  rw [nat.cast_mul, nat.cast_pow, mul_comm, ←div_div_eq_div_mul, pow_sub₀ _ _ hn, ←div_eq_mul_inv],
  rw nat.cast_ne_zero,
  apply hd.ne',
end

open_locale filter topological_space
open real

variables {N : ℕ}

lemma two_pow_log_two_lt : (2 : ℝ) ^ log 2 < 2 :=
begin
  have : log 2 < 1 := log_two_lt_d9.trans_le (by norm_num),
  simpa using rpow_lt_rpow_of_exponent_lt one_lt_two this,
end

noncomputable def n_value (N : ℕ) : ℕ := ⌈sqrt (log N)⌉₊
noncomputable def d_value (N : ℕ) : ℕ := ⌊(N:ℝ)^(1/n_value N:ℝ)/2⌋₊

lemma n_value_pos {N : ℕ} (hN : 2 ≤ N) : 0 < n_value N :=
begin
  rw [pos_iff_ne_zero, n_value, ne.def, nat.ceil_eq_zero, not_le, real.sqrt_pos],
  apply log_pos,
  rw nat.one_lt_cast,
  apply hN
end

lemma two_le_n_value {N : ℕ} (hN : 3 ≤ N) : 2 ≤ n_value N :=
begin
  rw [n_value],
  apply nat.succ_le_of_lt,
  rw [nat.lt_ceil, nat.cast_one],
  apply lt_sqrt_of_sq_lt,
  rw [one_pow, lt_log_iff_exp_lt],
  refine lt_of_lt_of_le _ (nat.cast_le.2 hN),
  { exact exp_one_lt_d9.trans_le (by norm_num) },
  rw nat.cast_pos,
  exact lt_of_lt_of_le (by norm_num) hN,
end

lemma three_le_n_value {N : ℕ} (hN : 64 ≤ N) : 3 ≤ n_value N :=
begin
  rw [n_value, ←nat.lt_iff_add_one_le, nat.lt_ceil, nat.cast_two],
  apply lt_sqrt_of_sq_lt,
  have : (2 : ℝ)^((6 : ℕ) : ℝ) ≤ N,
  { rw rpow_nat_cast,
    refine le_trans _ (nat.cast_le.2 hN),
    norm_num1 },
  apply lt_of_lt_of_le _ ((log_le_log (rpow_pos_of_pos zero_lt_two _) _).2 this),
  rw [log_rpow zero_lt_two, nat.cast_bit0, nat.cast_bit1, nat.cast_one, ←div_lt_iff'],
  { exact lt_of_le_of_lt (by norm_num1) log_two_gt_d9 },
  { norm_num1 },
  rw nat.cast_pos,
  exact lt_of_lt_of_le (by norm_num1) hN,
end

lemma log_two_mul_two_le_sqrt_log_eight : log 2 * 2 ≤ sqrt (log 8) :=
begin
  suffices : log 2 * 2 ≤ sqrt ((3:ℕ) * log 2),
  { rw [←log_rpow zero_lt_two (3:ℕ), rpow_nat_cast] at this,
    norm_num at this,
    apply this },
  apply le_sqrt_of_sq_le,
  rw [mul_pow, sq (log 2), mul_assoc, mul_comm],
  refine mul_le_mul_of_nonneg_right _ (log_nonneg one_le_two),
  rw ←le_div_iff,
  apply log_two_lt_d9.le.trans,
  all_goals { norm_num },
end

lemma d_value_pos {N : ℕ} (hN₃ : 8 ≤ N) : 0 < d_value N :=
begin
  have hN₀ : 0 < (N:ℝ) := nat.cast_pos.2 (nat.succ_pos'.trans_le hN₃),
  rw [d_value, nat.floor_pos, ←log_le_log zero_lt_one, log_one, log_div _ two_ne_zero, log_rpow hN₀,
    div_mul_eq_mul_div, one_mul, sub_nonneg, le_div_iff],
  { have : (n_value N : ℝ) ≤ 2 * sqrt (log N),
    { apply (nat.ceil_lt_add_one (sqrt_nonneg _)).le.trans,
      rw [two_mul, add_le_add_iff_left],
      apply le_sqrt_of_sq_le,
      rw [one_pow, le_log_iff_exp_le hN₀],
      exact (exp_one_lt_d9.le.trans (by norm_num)).trans (nat.cast_le.2 hN₃) },
    apply (mul_le_mul_of_nonneg_left this (log_nonneg one_le_two)).trans _,
    rw [←mul_assoc, ←le_div_iff (real.sqrt_pos.2 (log_pos (nat.one_lt_cast.2 _))), div_sqrt],
    { apply log_two_mul_two_le_sqrt_log_eight.trans,
      apply real.sqrt_le_sqrt,
      rw log_le_log _ hN₀,
      { exact_mod_cast hN₃ },
      { norm_num } },
    exact lt_of_lt_of_le (by norm_num) hN₃ },
  { exact nat.cast_pos.2 (n_value_pos ((show 2 ≤ 8, by norm_num).trans hN₃)) },
  { apply (rpow_pos_of_pos hN₀ _).ne' },
  { exact div_pos (rpow_pos_of_pos hN₀ _) zero_lt_two },
end

lemma le_N (hN : 2 ≤ N) : (2 * (d_value N) - 1)^(n_value N) ≤ N :=
begin
  have : (2 * d_value N - 1)^(n_value N) ≤ (2 * d_value N)^(n_value N) :=
    nat.pow_le_pow_of_le_left (nat.sub_le _ _) _,
  apply this.trans,
  suffices : ((2 * d_value N)^n_value N : ℝ) ≤ N, by exact_mod_cast this,
  rw ←rpow_nat_cast,
  suffices i : (2 * d_value N : ℝ) ≤ (N:ℝ)^(1/n_value N:ℝ),
  { apply (rpow_le_rpow (mul_nonneg zero_le_two (nat.cast_nonneg _)) i (nat.cast_nonneg _)).trans,
    rw [←rpow_mul (nat.cast_nonneg _), one_div_mul_cancel, rpow_one],
    rw nat.cast_ne_zero,
    apply (n_value_pos hN).ne', },
  rw ←le_div_iff',
  { exact nat.floor_le (div_nonneg (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) zero_le_two) },
  apply zero_lt_two
end

lemma floor_lt_mul {x : ℝ} (hx : 2 / (1 - 2 / exp 1) ≤ x) :
  x / exp 1 < (⌊x/2⌋₊ : ℝ) :=
begin
  apply lt_of_le_of_lt _ (nat.sub_one_lt_floor _),
  have : 0 < 1 - 2 / exp 1,
  { rw [sub_pos, div_lt_one (exp_pos _)],
    exact lt_of_le_of_lt (by norm_num) exp_one_gt_d9 },
  rwa [le_sub, div_eq_mul_one_div x, div_eq_mul_one_div x, ←mul_sub, div_sub', ←div_eq_mul_one_div,
    mul_div_assoc', one_le_div, ←div_le_iff this],
  { exact zero_lt_two },
  { exact two_ne_zero }
end

lemma ceil_lt_mul {x : ℝ} (hx : 50/19 ≤ x) :
  (⌈x⌉₊ : ℝ) < 1.38 * x :=
begin
  refine (nat.ceil_lt_add_one (le_trans (by norm_num) hx)).trans_le _,
  rw [←le_sub_iff_add_le', div_mul_eq_mul_div, div_sub', one_le_div, ←sub_mul],
  linarith,
  norm_num,
  norm_num,
end

lemma weird_bound :
  2 / (1 - 2 / exp 1) ≤ 8 :=
begin
  rw [div_le_iff, mul_sub, mul_one, mul_div_assoc', le_sub, div_le_iff (exp_pos _)],
  { linarith [exp_one_gt_d9] },
  rw [sub_pos, div_lt_one];
  exact lt_trans (by norm_num) exp_one_gt_d9,
end

lemma annoying_bound (hN : 4096 ≤ N) :
  log (2 / (1 - 2 / exp 1)) * (69 / 50) ≤ sqrt (log ↑N) :=
begin
  have : ((12 : ℕ) : ℝ) * log 2 ≤ log N,
  { rw [←log_rpow zero_lt_two, log_le_log, rpow_nat_cast],
    { norm_num1,
      exact_mod_cast hN },
    { apply rpow_pos_of_pos zero_lt_two },
    rw nat.cast_pos,
    apply lt_of_lt_of_le _ hN,
    norm_num1 },
  refine (mul_le_mul_of_nonneg_right ((log_le_log _ (by norm_num1)).2 weird_bound) _).trans _,
  { refine div_pos zero_lt_two _,
    rw [sub_pos, div_lt_one (exp_pos _)],
    exact lt_of_le_of_lt (by norm_num1) exp_one_gt_d9 },
  { norm_num1 },
  have l8 : log 8 = ((3:ℕ):ℝ) * log 2,
  { rw [←log_rpow zero_lt_two, rpow_nat_cast],
    norm_num },
  rw [l8, nat.cast_bit1, nat.cast_one],
  apply le_sqrt_of_sq_le (le_trans _ this),
  simp only [nat.cast_bit0, nat.cast_bit1, nat.cast_one],
  rw [mul_right_comm, mul_pow, sq (log 2), ←mul_assoc],
  apply mul_le_mul_of_nonneg_right _ (log_nonneg one_le_two),
  rw ←le_div_iff',
  { apply log_two_lt_d9.le.trans,
    norm_num1 },
  apply sq_pos_of_ne_zero,
  norm_num1,
end

lemma bound (hN : 4096 ≤ N) :
  (N:ℝ)^(1/n_value N:ℝ) / exp 1 < d_value N :=
begin
  apply floor_lt_mul _,
  rw [←log_le_log, log_rpow, mul_comm, ←div_eq_mul_one_div],
  { apply le_trans _ (div_le_div_of_le_left _ _ (ceil_lt_mul _).le),
    rw [mul_comm, ←div_div_eq_div_mul, div_sqrt, le_div_iff],
    { apply annoying_bound hN },
    { apply div_pos;
      norm_num1 },
    { apply log_nonneg,
      rw nat.one_le_cast,
      exact le_trans (by norm_num1) hN },
    { rw [nat.cast_pos, nat.lt_ceil, nat.cast_zero, real.sqrt_pos],
      apply log_pos,
      rw nat.one_lt_cast,
      exact lt_of_lt_of_le (by norm_num1) hN },
    apply le_sqrt_of_sq_le,
    have : ((12 : ℕ) : ℝ) * log 2 ≤ log N,
    { rw [←log_rpow zero_lt_two, log_le_log, rpow_nat_cast],
      { norm_num1,
        exact_mod_cast hN },
      { apply rpow_pos_of_pos zero_lt_two },
      rw nat.cast_pos,
      apply lt_of_lt_of_le _ hN,
      norm_num1 },
    apply le_trans _ this,
    simp only [nat.cast_bit0, nat.cast_bit1, nat.cast_one],
    rw ←div_le_iff',
    { refine le_trans (by norm_num1) log_two_gt_d9.le },
    { norm_num1 } },
  { rw nat.cast_pos,
    exact lt_of_lt_of_le (by norm_num1) hN },
  { refine div_pos zero_lt_two _,
    rw [sub_pos, div_lt_one (exp_pos _)],
    exact lt_of_le_of_lt (by norm_num1) exp_one_gt_d9 },
  apply rpow_pos_of_pos,
  rw nat.cast_pos,
  exact lt_of_lt_of_le (by norm_num1) hN,
end

-- MOVE TO MATHLIB
lemma monotone_on.congr {α β : Type*} [preorder α] [preorder β] {f g : α → β} {s : set α}
  (hf : monotone_on f s) (fg : set.eq_on f g s) :
  monotone_on g s :=
begin
  intros x hx y hy xy,
  rw [←fg hx, ←fg hy],
  apply hf hx hy xy,
end

lemma lower_bound_increasing_comp {c : ℝ} :
  monotone_on (λ x, x * (x - c)) (set.Ici (c/2)) :=
begin
  apply (convex_Ici _).monotone_on_of_deriv_nonneg,
  { exact continuous_on_id.mul (continuous_on_id.sub continuous_on_const) },
  { exact differentiable_on_id.mul (differentiable_on_id.sub (differentiable_on_const _)) },
  intros x hx,
  simp only [interior_Ici, set.mem_Ioi, div_lt_iff', zero_lt_two] at hx,
  simp_rw [mul_sub, ←sq],
  simpa using hx.le,
end

lemma lower_bound_increasing (c : ℝ) :
  monotone_on (λ N, N * exp (-c * sqrt (log N))) (set.Ici (exp ((c/2)^2))) :=
begin
  have pos : set.Ici (exp ((c/2)^2)) ⊆ set.Ioi 0,
  { rintro x hx,
    exact lt_of_lt_of_le (exp_pos _) hx },
  have : set.eq_on (λ N, N * exp (-c * sqrt (log N))) (λ N, exp (sqrt (log N) * (sqrt (log N) - c)))
    (set.Ici (exp ((c/2)^2))),
  { intros x hx,
    dsimp,
    rw set.mem_Ici at hx,
    rw [mul_sub, mul_self_sqrt, sub_eq_add_neg, exp_add, neg_mul_eq_neg_mul_symm, exp_log,
      mul_comm c],
    { apply pos hx },
    refine log_nonneg _,
    apply le_trans _ hx,
    apply one_le_exp_iff.2 (sq_nonneg _) },
  apply monotone_on.congr _ this.symm,
  apply monotone.comp_monotone_on,
  { apply exp_monotone },
  intros x hx y hy xy,
  apply lower_bound_increasing_comp _ _ (sqrt_le_sqrt ((log_le_log (pos hx) (pos hy)).2 xy));
  { rw [set.mem_Ici],
    apply le_sqrt_of_sq_le,
    rw le_log_iff_exp_le (pos _);
    assumption },
end

lemma lower_bound_increasing' :
  monotone_on (λ N, N * exp (-4 * sqrt (log N))) (set.Ici (exp 4)) :=
begin
  convert lower_bound_increasing 4,
  norm_num1
end

lemma exp_thing {x : ℝ} (hx : 0 < x) :
  exp (- 2 * x) < exp (2 - ⌈x⌉₊) / ⌈x⌉₊ :=
begin
  have i := nat.ceil_lt_add_one hx.le,
  have h₁ : 0 < ⌈x⌉₊, by rwa [nat.lt_ceil, nat.cast_zero],
  have h₂ : 1 - x ≤ 2 - ⌈x⌉₊,
  { rw le_sub_iff_add_le,
    apply (add_le_add_left i.le _).trans,
    rw [←add_assoc, sub_add_cancel],
    apply le_refl },
  have h₃ : exp (-(x+1)) ≤ 1 / (x + 1),
  { rw [exp_neg, inv_eq_one_div],
    refine one_div_le_one_div_of_le (add_pos hx zero_lt_one) _,
    apply le_trans _ (add_one_le_exp_of_nonneg (add_nonneg hx.le zero_le_one)),
    exact le_add_of_nonneg_right zero_le_one },
  refine lt_of_le_of_lt _ (div_lt_div_of_lt_left (nat.cast_pos.2 h₁) i (exp_pos _)),
  refine le_trans _ (div_le_div_of_le_of_nonneg (exp_le_exp.2 h₂) (add_nonneg hx.le zero_le_one)),
  rw [le_div_iff (add_pos hx zero_lt_one), ←le_div_iff' (exp_pos _), ←exp_sub,
    neg_mul_eq_neg_mul_symm, sub_neg_eq_add, two_mul, sub_add_add_cancel, add_comm _ x],
  apply le_trans _ (add_one_le_exp_of_nonneg (add_nonneg hx.le zero_le_one)),
  exact le_add_of_nonneg_right zero_le_one
end

lemma exp_one_rpow {r : ℝ} :
  exp 1^r = exp r :=
by rw [←exp_mul, one_mul]

lemma roth_lower_bound_explicit (hN : 4096 ≤ N) :
  (N : ℝ) * exp (-4 * sqrt (log N)) < roth_number_nat N :=
begin
  let n := n_value N,
  have hn : 0 < n := n_value_pos ((show _ ≤ _, by norm_num1).trans hN),
  have hd : 0 < d_value N := d_value_pos ((show _ ≤ _, by norm_num1).trans hN),
  have hN₀ : 0 < (N:ℝ) := nat.cast_pos.2 ((show 0 < 4096, by norm_num1).trans_le hN),
  have hn₂ : 2 ≤ n := two_le_n_value ((show _ ≤ _, by norm_num1).trans hN),
  have : (2 * d_value N - 1)^n ≤ N := le_N (ge_trans hN (by norm_num1)),
  have := behrend_bound_aux3 hd hn₂ this,
  apply lt_of_lt_of_le _ this,
  apply lt_of_le_of_lt _ (div_lt_div_of_lt _ (pow_lt_pow_of_lt_left (bound hN) _ _)),
  { rw [←rpow_nat_cast, div_rpow (rpow_nonneg_of_nonneg hN₀.le _) (exp_pos _).le, ←rpow_mul hN₀.le,
      mul_comm (_ / _), mul_one_div, nat.cast_sub hn₂, nat.cast_two, same_sub_div, exp_one_rpow,
      div_div_eq_div_mul, rpow_sub, rpow_one, div_div_eq_div_mul, div_eq_mul_inv],
    { apply mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
      rw [mul_inv₀, mul_inv₀, ←exp_neg, ←rpow_neg (nat.cast_nonneg _), neg_sub, ←div_eq_mul_inv],
      have : exp ((-4) * sqrt (log N)) = exp (-2 * sqrt (log N)) * exp (-2 * sqrt (log N)),
      { rw [←exp_add, ←add_mul],
        norm_num },
      rw this,
      apply (mul_le_mul _ (exp_thing (real.sqrt_pos.2 _)).le _ _),
      { rw [←le_log_iff_exp_le (rpow_pos_of_pos hN₀ _), log_rpow hN₀, ←le_div_iff, mul_div_assoc,
          div_sqrt, neg_mul_eq_neg_mul_symm, neg_le_neg_iff, div_mul_eq_mul_div, div_le_iff],
        { exact mul_le_mul_of_nonneg_left (nat.le_ceil _) zero_le_two },
        { rwa nat.cast_pos },
        rw real.sqrt_pos,
        apply log_pos,
        rw nat.one_lt_cast,
        exact lt_of_lt_of_le (by norm_num1) hN },
      { apply log_pos,
        rw nat.one_lt_cast,
        exact lt_of_lt_of_le (by norm_num1) hN },
      { apply (exp_pos _).le },
      apply rpow_nonneg_of_nonneg (nat.cast_nonneg _) },
    { apply hN₀ },
    apply ne_of_gt,
    rwa nat.cast_pos },
  { rwa nat.cast_pos },
  { exact div_nonneg (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) (exp_pos _).le },
  apply nat.sub_pos_of_lt,
  apply three_le_n_value,
  apply le_trans _ hN,
  norm_num1
end

lemma exp_four_lt : exp 4 < 64 :=
begin
  have : (2:ℝ) ^ ((6:ℕ):ℝ) = 64,
  { rw rpow_nat_cast,
    norm_num1 },
  rw [←this, ←lt_log_iff_exp_lt (rpow_pos_of_pos zero_lt_two _), log_rpow zero_lt_two,
    ←div_lt_iff'],
  refine lt_of_le_of_lt (by norm_num1) log_two_gt_d9,
  norm_num
end


lemma four_zero_nine_six_lt_exp_sixteen : 4096 < exp 16 :=
begin
  rw [←log_lt_iff_lt_exp (show (0:ℝ) < 4096, by norm_num)],
  have : (4096:ℝ) = 2 ^ 12,
  { norm_num },
  rw [this, ←rpow_nat_cast, log_rpow zero_lt_two, nat.cast_bit0, nat.cast_bit0, nat.cast_bit1,
    nat.cast_one],
  linarith [log_two_lt_d9]
end

lemma lower_bound_le_one' (hN : 2 ≤ N) (hN' : N ≤ 4096) :
  (N : ℝ) * exp (-4 * sqrt (log N)) ≤ 1 :=
begin
  rw [←log_le_log (mul_pos (nat.cast_pos.2 (zero_lt_two.trans_le hN)) (exp_pos _)) zero_lt_one,
    log_one, log_mul (nat.cast_pos.2 (zero_lt_two.trans_le hN)).ne' (exp_pos _).ne', log_exp,
    neg_mul_eq_neg_mul_symm, ←sub_eq_add_neg, sub_nonpos,
    ←div_le_iff (real.sqrt_pos.2 (log_pos (nat.one_lt_cast.2 (one_lt_two.trans_le hN)))), div_sqrt,
    sqrt_le_left (zero_le_bit0.2 zero_le_two),
    log_le_iff_le_exp (nat.cast_pos.2 (zero_lt_two.trans_le hN))],
  norm_num1,
  apply le_trans _ four_zero_nine_six_lt_exp_sixteen.le,
  exact_mod_cast hN'
end

lemma lower_bound_le_one (hN : 1 ≤ N) (hN' : N ≤ 4096) :
  (N : ℝ) * exp (-4 * sqrt (log N)) ≤ 1 :=
begin
  rcases nat.eq_or_lt_of_le hN with rfl | hN,
  { simp },
  apply lower_bound_le_one' hN hN',
end

lemma roth_lower_bound :
  (N : ℝ) * exp (-4 * sqrt (log N)) ≤ roth_number_nat N :=
begin
  rcases nat.eq_zero_or_pos N with rfl | hN,
  { simp },
  { cases le_or_lt 4096 N with h₁ h₁,
    { apply (roth_lower_bound_explicit h₁).le },
    apply (lower_bound_le_one hN h₁.le).trans,
    simpa using roth_number_nat.monotone hN }
end

-- lemma roth_lower_asymptotic {δ : ℝ} (hδ : 0 < δ) :
--   is_o (λ (x:ℝ), x^(1 - δ)) (λ x, (roth_number ⌊x⌋₊ : ℝ)) at_top :=
-- begin
--   suffices : is_o (λ (x:ℝ), (x^(1 - δ))) (λ x, x * exp (-4 * sqrt (log x))) at_top,
--   { apply is_o.trans_is_O this,
--     simp only [is_O_iff, eventually_le, eventually_at_top],
--     refine ⟨1, exp 4, λ N hN, _⟩,
--     rw [norm_coe_nat, real.norm_eq_abs, one_mul],
--     -- have := is_o.trans_le,
--     -- apply this.trans_le,
--     -- intros x,
--     -- rw [normed_field.norm_mul, norm_coe_nat, norm_coe_nat, real.norm_eq_abs, abs_exp],
--     -- apply roth_lower_bound
--     },
-- end

-- #exit

-- lemma roth_lower_asymptotic {δ : ℝ} (hδ : 0 < δ) :
--   is_o (λ (N:ℕ), (N:ℝ)^(1 - δ)) (λ N, (roth_number N : ℝ)) at_top :=
-- begin
--   suffices : is_o (λ (N:ℕ), ((N:ℝ)^(1 - δ))) (λ (N:ℕ), (N : ℝ) * exp (-4 * sqrt (log N))) at_top,
--   { apply this.trans_le,
--     intros x,
--     rw [normed_field.norm_mul, norm_coe_nat, norm_coe_nat, real.norm_eq_abs, abs_exp],
--     apply roth_lower_bound },
--   suffices : is_o (λ (N:ℕ), ((N:ℝ) * N^(-δ))) (λ (N:ℕ), (N : ℝ) * exp (-4 * sqrt (log N))) at_top,
--   { apply is_o.congr' _ (eventually_eq.refl _ _) this,
--     rw [eventually_eq, eventually_at_top],
--     refine ⟨1, λ N hN, _⟩,
--     rw [rpow_sub (nat.cast_pos.2 hN), rpow_neg (nat.cast_nonneg _), rpow_one, div_eq_mul_inv] },
--    refine is_O.mul_is_o (is_O_refl _ _) _,
--   rw is_o_iff,
--   intros c hc,
--   rw eventually_at_top,
--   refine ⟨1, λ N hN, _⟩,
--   have hN' : 0 < (N : ℝ) ^ -δ := rpow_pos_of_pos (nat.cast_pos.2 hN) _,
--   rw [real.norm_rpow_of_nonneg (nat.cast_nonneg _), norm_coe_nat, real.norm_eq_abs, abs_exp,
--     ←div_le_iff' hc, ←log_le_iff_le_exp (div_pos hN' hc), log_div hN'.ne' hc.ne'],
--   -- simp only [neg_mul_eq_neg_mul_symm, ge_iff_le, eventually_at_top, real.norm_eq_abs],

--   -- have : is_O (λ (N:ℕ), (N : ℝ) * exp (-4 * sqrt (log N))) (λ N, (roth_number N : ℝ)) at_top,
--   -- { apply is_O_of_le,
--   --   simp only [normed_field.norm_mul, norm_coe_nat],
--   --   intro x,
--   --   simp only [real.norm_eq_abs, abs_exp],
--   --   apply roth_lower_bound },

-- end

end behrend
