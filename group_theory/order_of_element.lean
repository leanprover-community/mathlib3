/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.finite group_theory.coset
open set function

variables {α : Type*} {s : set α} {a a₁ a₂ b c: α}

-- TODO this lemma isn't used anywhere in this file, and should be moved elsewhere.
namespace finset
open finset

lemma mem_range_iff_mem_finset_range_of_mod_eq [decidable_eq α] {f : ℤ → α} {a : α} {n : ℕ}
  (hn : 0 < n) (h : ∀i, f (i % n) = f i) :
  a ∈ set.range f ↔ a ∈ (finset.range n).image (λi, f i) :=
suffices (∃i, f (i % n) = a) ↔ ∃i, i < n ∧ f ↑i = a, by simpa [h],
have hn' : 0 < (n : ℤ), from int.coe_nat_lt.mpr hn,
iff.intro
  (assume ⟨i, hi⟩,
    have 0 ≤ i % ↑n, from int.mod_nonneg _ (ne_of_gt hn'),
    ⟨int.to_nat (i % n),
      by rw [←int.coe_nat_lt, int.to_nat_of_nonneg this]; exact ⟨int.mod_lt_of_pos i hn', hi⟩⟩)
  (assume ⟨i, hi, ha⟩,
    ⟨i, by rw [int.mod_eq_of_lt (int.coe_zero_le _) (int.coe_nat_lt_coe_nat_of_lt hi), ha]⟩)

end finset

lemma conj_inj [group α] {x : α} : function.injective (λ (g : α), x * g * x⁻¹) :=
λ a b h, by simpa [mul_left_inj, mul_right_inj] using h

lemma mem_normalizer_fintype [group α] {s : set α} [fintype s] {x : α}
  (h : ∀ n, n ∈ s → x * n * x⁻¹ ∈ s) : x ∈ is_subgroup.normalizer s :=
by haveI := classical.prop_decidable;
haveI := set.fintype_image s (λ n, x * n * x⁻¹); exact
λ n, ⟨h n, λ h₁,
have heq : (λ n, x * n * x⁻¹) '' s = s := set.eq_of_card_le_of_subset
  (by rw set.card_image_of_injective s conj_inj) (λ n ⟨y, hy⟩, hy.2 ▸ h y hy.1),
have x * n * x⁻¹ ∈ (λ n, x * n * x⁻¹) '' s := heq.symm ▸ h₁,
let ⟨y, hy⟩ := this in conj_inj hy.2 ▸ hy.1⟩

section order_of
variables [group α] [fintype α] [decidable_eq α]

instance (s : set α) [is_subgroup s] [d : decidable_pred s] :
  fintype (left_cosets s) :=
@quotient.fintype _ _ (left_rel s) (λ _ _, d _)

lemma card_eq_card_cosets_mul_card_subgroup (s : set α) [hs : is_subgroup s] [fintype s]
  [decidable_pred s] : fintype.card α = fintype.card (left_cosets s) * fintype.card s :=
by rw ← fintype.card_prod;
  exact fintype.card_congr (is_subgroup.group_equiv_left_cosets_times_subgroup hs)

lemma card_subgroup_dvd_card (s : set α) [is_subgroup s] [fintype s] :
  fintype.card s ∣ fintype.card α :=
by haveI := classical.prop_decidable; simp [card_eq_card_cosets_mul_card_subgroup s]

lemma card_left_cosets_dvd_card (s : set α) [is_subgroup s] [decidable_pred s] [fintype s] :
  fintype.card (left_cosets s) ∣ fintype.card α :=
by simp [card_eq_card_cosets_mul_card_subgroup s]

@[simp] lemma card_trivial [fintype (is_subgroup.trivial α)] :
  fintype.card (is_subgroup.trivial α) = 1 :=
fintype.card_eq_one_iff.2
  ⟨⟨(1 : α), by simp⟩, λ ⟨y, hy⟩, subtype.eq $ is_subgroup.mem_trivial.1 hy⟩

lemma exists_gpow_eq_one (a : α) : ∃i≠0, a ^ (i:ℤ) = 1 :=
have ¬ injective (λi, a ^ i),
  from not_injective_int_fintype,
let ⟨i, j, a_eq, ne⟩ := show ∃(i j : ℤ), a ^ i = a ^ j ∧ i ≠ j,
  by rw [injective] at this; simpa [classical.not_forall] in
have a ^ (i - j) = 1,
  by simp [gpow_add, gpow_neg, a_eq],
⟨i - j, sub_ne_zero.mpr ne, this⟩

lemma exists_pow_eq_one (a : α) : ∃i≠0, a ^ i = 1 :=
let ⟨i, hi, eq⟩ := exists_gpow_eq_one a in
begin
  cases i,
  { exact ⟨i, by simp [int.of_nat_eq_coe, *] at *, eq⟩ },
  { exact ⟨i + 1, dec_trivial, inv_eq_one.1 eq⟩ }
end

/-- `order_of a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `a ^ n = 1` -/
def order_of (a : α) : ℕ := nat.find (exists_pow_eq_one a)

lemma pow_order_of_eq_one (a : α) : a ^ order_of a = 1 :=
let ⟨h₁, h₂⟩ := nat.find_spec (exists_pow_eq_one a) in h₂

lemma order_of_ne_zero (a : α) : order_of a ≠ 0 :=
let ⟨h₁, h₂⟩ := nat.find_spec (exists_pow_eq_one a) in h₁

private lemma pow_injective_aux {n m : ℕ} (a : α) (h : n ≤ m)
  (hn : n < order_of a) (hm : m < order_of a) (eq : a ^ n = a ^ m) : n = m :=
decidable.by_contradiction $ assume ne : n ≠ m,
  have h₁ : m - n ≠ 0, by simp [nat.sub_eq_iff_eq_add h, ne.symm],
  have h₂ : a ^ (m - n) = 1, by simp [pow_sub _ h, eq],
  have le : order_of a ≤ m - n, from nat.find_min' (exists_pow_eq_one a) ⟨h₁, h₂⟩,
  have lt : m - n < order_of a,
    from (nat.sub_lt_left_iff_lt_add h).mpr $ nat.lt_add_left _ _ _ hm,
  lt_irrefl _ (lt_of_le_of_lt le lt)

lemma pow_injective_of_lt_order_of {n m : ℕ} (a : α)
  (hn : n < order_of a) (hm : m < order_of a) (eq : a ^ n = a ^ m) : n = m :=
(le_total n m).elim
  (assume h, pow_injective_aux a h hn hm eq)
  (assume h, (pow_injective_aux a h hm hn eq.symm).symm)

lemma order_of_le_card_univ : order_of a ≤ fintype.card α :=
finset.card_le_of_inj_on ((^) a)
  (assume n _, fintype.complete _)
  (assume i j, pow_injective_of_lt_order_of a)

lemma pow_eq_mod_order_of {n : ℕ} : a ^ n = a ^ (n % order_of a) :=
calc a ^ n = a ^ (n % order_of a + order_of a * (n / order_of a)) :
    by rw [nat.mod_add_div]
  ... = a ^ (n % order_of a) :
    by simp [pow_add, pow_mul, pow_order_of_eq_one]

lemma gpow_eq_mod_order_of {i : ℤ} : a ^ i = a ^ (i % order_of a) :=
calc a ^ i = a ^ (i % order_of a + order_of a * (i / order_of a)) :
    by rw [int.mod_add_div]
  ... = a ^ (i % order_of a) :
    by simp [gpow_add, gpow_mul, pow_order_of_eq_one]

lemma mem_gpowers_iff_mem_range_order_of {a a' : α} :
  a' ∈ gpowers a ↔ a' ∈ (finset.range (order_of a)).image ((^) a : ℕ → α) :=
finset.mem_range_iff_mem_finset_range_of_mod_eq
  (nat.pos_iff_ne_zero.mpr (order_of_ne_zero a))
  (assume i, gpow_eq_mod_order_of.symm)

instance decidable_range_gpow : decidable_pred (gpowers a) :=
assume a', decidable_of_iff'
  (a' ∈ (finset.range (order_of a)).image ((^) a))
  mem_gpowers_iff_mem_range_order_of

section
local attribute [instance] set_fintype

lemma order_eq_card_gpowers : order_of a = fintype.card (gpowers a) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨gpow a n, ⟨n, rfl⟩⟩ },
  { exact assume ⟨_, i, rfl⟩ _,
    have pos: (0:int) < order_of a,
      from int.coe_nat_lt.mpr $ nat.pos_iff_ne_zero.mpr $ order_of_ne_zero a,
    have 0 ≤ i % (order_of a),
      from int.mod_nonneg _ $ ne_of_gt pos,
    ⟨int.to_nat (i % order_of a),
      by rw [← int.coe_nat_lt, int.to_nat_of_nonneg this];
        exact ⟨int.mod_lt_of_pos _ pos, subtype.eq gpow_eq_mod_order_of.symm⟩⟩ },
  { intros, exact finset.mem_univ _ },
  { exact assume i j hi hj eq, pow_injective_of_lt_order_of a hi hj $ by simpa using eq }
end

@[simp] lemma order_of_one : order_of (1 : α) = 1 :=
by rw [order_eq_card_gpowers, fintype.card_eq_one_iff];
  exact ⟨⟨1, 0, rfl⟩, λ ⟨a, i, ha⟩, by simp [ha.symm]⟩

lemma order_of_dvd_of_pow_eq_one {n : ℕ} (h : a ^ n = 1) : order_of a ∣ n :=
by_contradiction
(λ h₁, nat.find_min _ (show n % order_of a < order_of a,
  from nat.mod_lt _ (nat.pos_of_ne_zero (order_of_ne_zero _)))
    ⟨mt nat.dvd_of_mod_eq_zero h₁, by rwa ← pow_eq_mod_order_of⟩)

lemma order_of_eq_one_iff : order_of a = 1 ↔ a = 1 :=
⟨λ h, by conv { to_lhs, rw [← pow_one a, ← h, pow_order_of_eq_one] }, λ h, by simp [h]⟩

section classical
local attribute [instance] classical.prop_decidable

/- TODO: use cardinal theory, introduce `card : set α → ℕ`, or setup decidability for cosets -/
lemma order_of_dvd_card_univ : order_of a ∣ fintype.card α :=
have ft_prod : fintype (left_cosets (gpowers a) × (gpowers a)),
  from fintype.of_equiv α (gpowers.is_subgroup a).group_equiv_left_cosets_times_subgroup,
have ft_s : fintype (gpowers a),
  from @fintype.fintype_prod_right _ _ _ ft_prod _,
have ft_cosets : fintype (left_cosets (gpowers a)),
  from @fintype.fintype_prod_left _ _ _ ft_prod ⟨⟨1, is_submonoid.one_mem (gpowers a)⟩⟩,
have ft : fintype (left_cosets (gpowers a) × (gpowers a)),
  from @prod.fintype _ _ ft_cosets ft_s,
have eq₁ : fintype.card α = @fintype.card _ ft_cosets * @fintype.card _ ft_s,
  from calc fintype.card α = @fintype.card _ ft_prod :
      @fintype.card_congr _ _ _ ft_prod (gpowers.is_subgroup a).group_equiv_left_cosets_times_subgroup
    ... = @fintype.card _ (@prod.fintype _ _ ft_cosets ft_s) :
      congr_arg (@fintype.card _) $ subsingleton.elim _ _
    ... = @fintype.card _ ft_cosets * @fintype.card _ ft_s :
      @fintype.card_prod _ _ ft_cosets ft_s,
have eq₂ : order_of a = @fintype.card _ ft_s,
  from calc order_of a = _ : order_eq_card_gpowers
    ... = _ : congr_arg (@fintype.card _) $ subsingleton.elim _ _,
dvd.intro (@fintype.card (left_cosets (gpowers a)) ft_cosets) $
  by rw [eq₁, eq₂, mul_comm]


end classical

end

end order_of
