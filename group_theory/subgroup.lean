/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl


-/
import data.finset algebra.big_operators data.equiv data.set data.nat.basic set_theory.cardinal
open set function finset
local infix ` ^ ` := monoid.pow

universes u v w
variables {α : Type u} {β : Type v} {s : set α} {a a₁ a₂ : α}

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

variables [group α]

/-- A subset of a group closed under the group operations. -/
structure is_subgroup (s : set α) : Prop :=
(one_mem : (1:α) ∈ s)
(mul_inv_mem : ∀a∈s, ∀b∈s, a * b⁻¹ ∈ s)

def cosets (s : set α) : set (set α) := range (λa, (*) a '' s)

namespace is_subgroup
lemma inv_mem (hs : is_subgroup s) (h : a ∈ s) : a⁻¹ ∈ s :=
have 1 * a⁻¹ ∈ s, from hs.mul_inv_mem _ hs.one_mem _ h,
by simpa

lemma inv_mem_iff (hs : is_subgroup s) : a⁻¹ ∈ s ↔ a ∈ s :=
iff.intro (assume h, have a⁻¹⁻¹ ∈ s, from hs.inv_mem h, by simpa) hs.inv_mem

lemma mul_mem (hs : is_subgroup s) (h₁ : a₁ ∈ s) (h₂ : a₂ ∈ s) : a₁ * a₂ ∈ s :=
have a₁ * a₂⁻¹⁻¹ ∈ s, from hs.mul_inv_mem _ h₁ _ (hs.inv_mem h₂),
by simpa

lemma mul_image (hs : is_subgroup s) (a : α) (ha : a ∈ s) :
  (*) a '' s = s :=
ext $ assume a', iff.intro
  (assume ⟨a'', ha'', eq⟩, eq ▸ hs.mul_mem ha ha'')
  (assume ha', ⟨a⁻¹ * a', hs.mul_mem (hs.inv_mem ha) ha', by simp⟩)

lemma injective_mul {a : α} : injective ((*) a) :=
assume a₁ a₂ h,
have a⁻¹ * a * a₁ = a⁻¹ * a * a₂, by rw [mul_assoc, mul_assoc, h],
by rwa [inv_mul_self, one_mul, one_mul] at this

lemma subgroup_mem_cosets (hs : is_subgroup s) : s ∈ cosets s :=
⟨1, hs.mul_image _ hs.one_mem⟩

lemma cosets_disjoint (hs : is_subgroup s) :
  ∀{s₁ s₂ : set α}, s₁ ∈ cosets s → s₂ ∈ cosets s → ∀{a}, a ∈ s₁ → a ∈ s₂ → s₁ = s₂
| _ _ ⟨b₁, rfl⟩ ⟨b₂, rfl⟩ a ⟨c₁, hc₁, eq₁⟩ ⟨c₂, hc₂, eq₂⟩ :=
have b_eq : b₁ = b₂ * c₂ * c₁⁻¹, by rw [eq_mul_inv_iff_mul_eq, eq₁, eq₂],
have hc : c₂ * c₁⁻¹ ∈ s, from hs.mul_mem hc₂ (hs.inv_mem hc₁),
calc (*) b₁ '' s = (*) b₂ '' ((*) (c₂ * c₁⁻¹) '' s) :
    by rw [←image_comp, (∘), b_eq]; apply image_congr _; simp [mul_assoc]
  ... = (*) b₂ '' s :
    by rw [hs.mul_image _ hc]

lemma pairwise_cosets_disjoint (hs : is_subgroup s) : pairwise_on (cosets s) disjoint :=
assume s₁ h₁ s₂ h₂ ne, eq_empty_iff_forall_not_mem.mpr $ assume a ⟨ha₁, ha₂⟩,
  ne $ hs.cosets_disjoint h₁ h₂ ha₁ ha₂

lemma cosets_equiv_subgroup (hs : is_subgroup s) : ∀{t : set α}, t ∈ cosets s → nonempty (t ≃ s)
| _ ⟨a, rfl⟩ := ⟨(equiv.set.image ((*) a) s injective_mul).symm⟩

lemma Union_cosets_eq_univ (hs : is_subgroup s) : ⋃₀ cosets s = univ :=
eq_univ_of_forall $ assume a, ⟨(*) a '' s, mem_range_self _, ⟨1, hs.one_mem, mul_one _⟩⟩

lemma group_equiv_cosets_times_subgroup (hs : is_subgroup s) : nonempty (α ≃ (cosets s × s)) :=
⟨calc α ≃ (@set.univ α) :
    (equiv.set.univ α).symm
  ... ≃ (⋃t∈cosets s, t) :
    by rw [←hs.Union_cosets_eq_univ]; simp
  ... ≃ (Σt:cosets s, t) :
    equiv.set.bUnion_eq_sigma_of_disjoint hs.pairwise_cosets_disjoint
  ... ≃ (Σt:cosets s, s) :
    equiv.sigma_congr_right $ λ⟨t, ht⟩, classical.choice $ hs.cosets_equiv_subgroup ht
  ... ≃ (cosets s × s) :
    equiv.sigma_equiv_prod _ _⟩

end is_subgroup

lemma is_subgroup_range_gpow : is_subgroup (range $ gpow a) :=
⟨⟨0, rfl⟩, assume a ⟨i, ha⟩ b ⟨j, hb⟩, ⟨i - j, by simp [gpow_add, gpow_neg, ha.symm, hb.symm]⟩⟩

section finite_group
variables [fintype α] [decidable_eq α]

lemma exists_gpow_eq_one (a : α) : ∃i≠0, gpow a i = 1 :=
have ¬ injective (λi, gpow a i),
  from not_injective_int_fintype,
let ⟨i, j, a_eq, ne⟩ := show ∃(i j : ℤ), gpow a i = gpow a j ∧ i ≠ j,
  by rw [injective] at this; simpa [classical.not_forall] in
have gpow a (i - j) = 1,
  by simp [gpow_add, gpow_neg, a_eq],
⟨i - j, sub_ne_zero.mpr ne, this⟩

lemma exists_pow_eq_one (a : α) : ∃i≠0, a ^ i = 1 :=
let ⟨i, hi, eq⟩ := exists_gpow_eq_one a in
begin
  cases i,
  { exact ⟨i, by simp [int.of_nat_eq_coe, *] at *, eq⟩ },
  { have := congr_arg has_inv.inv eq,
    exact ⟨i + 1, dec_trivial, by simp * at *⟩ }
end

/-- `order_of a` is the order of the element, i.e. the `n ≥ 1`, s.t. `a ^ n = 1` -/
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

lemma gpow_eq_mod_order_of {i : ℤ} : gpow a i = gpow a (i % order_of a) :=
calc gpow a i = gpow a (i % order_of a + order_of a * (i / order_of a)) :
    by rw [int.mod_add_div]
  ... = gpow a (i % order_of a) :
    by simp [gpow_add, gpow_mul, pow_order_of_eq_one]

lemma mem_range_gpow_iff_mem_range_order_of {a a' : α} :
  a' ∈ range (gpow a) ↔ a' ∈ (finset.range (order_of a)).image ((^) a) :=
finset.mem_range_iff_mem_finset_range_of_mod_eq
  (nat.pos_iff_ne_zero.mpr (order_of_ne_zero a))
  (assume i, gpow_eq_mod_order_of.symm)

instance decidable_range_gpow : decidable_pred (range (gpow a)) :=
assume a', decidable_of_iff
  (a' ∈ (finset.range (order_of a)).image ((^) a))
  mem_range_gpow_iff_mem_range_order_of.symm

section
local attribute [instance] set_fintype

lemma order_eq_card_range_gpow : order_of a = fintype.card (range (gpow a)) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨gpow a n, mem_range_self n⟩ },
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

section classical
local attribute [instance] classical.prop_decidable

-- TODO: use cardinal theory, or introduce `card : set α → ℕ`
lemma order_of_dvd_card_univ : order_of a ∣ fintype.card α :=
let s := range $ gpow a in
have hs : is_subgroup s, from is_subgroup_range_gpow,
let ⟨equiv⟩ := hs.group_equiv_cosets_times_subgroup in
have ft_prod : fintype (cosets s × s),
  from fintype.of_equiv α equiv,
have ft_s : fintype s,
  from @fintype.fintype_prod_right _ _ _ ft_prod ⟨⟨s, hs.subgroup_mem_cosets⟩⟩,
have ft_cosets : fintype (cosets s),
  from @fintype.fintype_prod_left _ _ _ ft_prod ⟨⟨1, hs.one_mem⟩⟩,
have ft : fintype (cosets s × s),
  from @prod.fintype _ _ ft_cosets ft_s,
have eq₁ : fintype.card α = @fintype.card _ ft_cosets * @fintype.card _ ft_s,
  from calc fintype.card α = @fintype.card _ ft_prod :
      (@fintype.card_eq _ _ _ ft_prod).2 hs.group_equiv_cosets_times_subgroup
    ... = @fintype.card _ (@prod.fintype _ _ ft_cosets ft_s) :
      congr_arg (@fintype.card _) $ subsingleton.elim _ _
    ... = @fintype.card _ ft_cosets * @fintype.card _ ft_s :
      @fintype.card_prod _ _ ft_cosets ft_s,
have eq₂ : order_of a = @fintype.card _ ft_s,
  from calc order_of a = _ : order_eq_card_range_gpow
    ... = _ : congr_arg (@fintype.card _) $ subsingleton.elim _ _,
dvd.intro (@fintype.card (cosets s) ft_cosets) $
  by rw [eq₁, eq₂, mul_comm]

end classical

end

end finite_group
