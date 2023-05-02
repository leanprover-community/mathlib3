/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir-/

import group_theory.index
import group_theory.specific_groups.alternating
import group_theory.specific_groups.cyclic
import group_theory.sylow
import data.fintype.basic

/-!
# Some complements on finite groups

- A subgroup of index two is normal
- A subgroup whose index is the smallest prime factor of the cardinal is normal
- The alternating group is characteristic

-/

open_locale classical


variables {α : Type*} [fintype α] [decidable_eq α]

/-- The alternating group of a subsingleton is ⊥ -/
lemma alternating_group_of_subsingleton (hα : subsingleton α) :
  alternating_group α = (⊥ : subgroup (equiv.perm α)) :=
begin
    rw eq_bot_iff,
    intros g hg,
    rw subgroup.mem_bot,
    let hα := @alternating_group.unique α _ _ hα,
    rw ← set_like.coe_mk g hg,
    rw ← subgroup.coe_one (alternating_group α),
    let hαq := hα.uniq,
    rw set_like.coe_eq_coe,
    rw hαq 1, rw hαq ⟨g, hg⟩
end

variable (α)
/-- The alternating group is a characteristic subgroup -/
theorem alternating_is_characteristic : (alternating_group α).characteristic :=
begin
  cases subsingleton_or_nontrivial α with hα hα,
  -- hα : subsingleton α
  { rw alternating_group_of_subsingleton hα,
    exact subgroup.bot_characteristic },

  -- hα : nontrivial α
  resetI,
  apply subgroup.characteristic.mk,
  intro φ,
  rw alternating_group_eq_sign_ker,
  rw monoid_hom.comap_ker,
  let s := equiv.perm.sign.comp φ.to_monoid_hom,

  have hs : function.surjective s,
  { change function.surjective (equiv.perm.sign ∘ φ),
    rw function.surjective.of_comp_iff _,
    exact equiv.perm.sign_surjective α,
    exact mul_equiv.surjective φ },
  obtain ⟨g', hg'⟩ := hs (-1),
  have hg' : s g' ≠ 1,
  { rw hg',  intro h, rw ← units.eq_iff at h,
    simpa only using h, },

  apply congr_arg,

  ext g,
  apply congr_arg,
  refine equiv.perm.swap_induction_on g _ _,
  { rw [map_one, equiv.perm.sign.map_one] },
  { intros f x y hxy hf,

    rw [s.map_mul, equiv.perm.sign.map_mul, hf],
    apply congr_arg2 (*) _ (rfl),
    revert x y hxy,
    by_contra,
    push_neg at h,
    obtain ⟨a, b, hab, hk⟩ := h,
    rw equiv.perm.sign_swap hab at hk,
    let hk := or.resolve_right (int.units_eq_one_or (s _)) hk,

    apply hg',
    refine equiv.perm.swap_induction_on g' (s.map_one) _,
    intros f x y hxy hf,
    rw [s.map_mul, hf, mul_one],

    obtain ⟨u, hu⟩ := equiv.perm.is_conj_swap hxy hab,
    apply mul_left_cancel,
    swap, exact (s u),
    rw [← s.map_mul, semiconj_by.eq hu, s.map_mul, hk, mul_one, one_mul] }
end

/-- A finite group of prime order is commutative -/
lemma is_commutative_of_prime_order {G : Type*} [group G] [fintype G] {p : ℕ} [hp : fact p.prime]
  (h : fintype.card G = p) : is_commutative G (*) :=
begin
  resetI,
  apply is_commutative.mk,
  haveI := is_cyclic_of_prime_card h,
  exact (is_cyclic.comm_group).mul_comm,
end

example (a b : ℕ) (h : a * 2 = b * 2) : a = b :=
begin
apply mul_left_injective₀ _ h, norm_num,
end

/-- The alternating group on a fintype of cardinal 3 is commutative -/
lemma alternating_group.is_commutative_of_order_three {α : Type*} [fintype α] [decidable_eq α]
  (hα : fintype.card α = 3) : is_commutative (alternating_group α) (*) :=
begin
  apply @is_commutative_of_prime_order _ _ _ 3 _,
  haveI hα' : nontrivial α,
  { rw ← fintype.one_lt_card_iff_nontrivial, rw hα, norm_num, },
  apply mul_right_injective₀ _,
  rw [two_mul_card_alternating_group, fintype.card_perm, hα], norm_num, norm_num,
end

lemma aux_dvd_lemma (r p : ℕ) (hp : p.prime) (h : r ∣ nat.factorial p )
  (hr : ∀ {l : ℕ} (hl : l.prime) (hl' : l ∣ r), p ≤ l) :
  r ∣ p :=
begin
  rw ← nat.coprime.dvd_mul_right _,
  rw nat.mul_factorial_pred (nat.prime.pos hp),
  exact h,
  rw nat.coprime_iff_gcd_eq_one ,
  by_contradiction,
  obtain ⟨l, hl, hl'⟩ := nat.exists_prime_and_dvd h,
  rw [nat.dvd_gcd_iff, nat.prime.dvd_factorial hl] at hl',
  apply (lt_iff_not_ge p.pred p).mp (nat.pred_lt (nat.prime.ne_zero hp)),
  rw nat.pred_eq_sub_one, rw ge_iff_le,
  exact le_trans (hr hl hl'.left) (hl'.right),
end

/-- A subgroup of a finite group whose index is the smallest prime factor is normal -/
theorem subgroup.normal_of_index_eq_smallest_prime_factor {G : Type*} [fintype G] [group G]
  (H : subgroup G) {p : ℕ} (hp : p.prime) (hHp : H.index = p)
  (hp' : ∀ {l : ℕ} (hl : l.prime) (hl' : l ∣ fintype.card G), p ≤ l) : H.normal :=
begin
  let f := (mul_action.to_perm_hom G (G ⧸ H)),
  suffices : f.ker = H,
  { rw ← this, refine monoid_hom.normal_ker f, },
  suffices : H.normal_core.relindex H = 1,
  { rw ← subgroup.normal_core_eq_ker,
    unfold subgroup.relindex at this,
    rw subgroup.index_eq_one  at this,
    apply le_antisymm, apply subgroup.normal_core_le,
    intros x hx,
    rw [← subgroup.coe_mk H x hx, ← subgroup.mem_subgroup_of, this],
    apply subgroup.mem_top },
  suffices : H.index ≠ 0,
  apply mul_left_injective₀ this, dsimp,
--  rw ← nat.mul_left_inj (nat.prime.pos hp),
--  conv_lhs { rw ← hHp },
  rw (subgroup.relindex_mul_index (subgroup.normal_core_le H)),
  rw one_mul,
  rw subgroup.normal_core_eq_ker, rw hHp,
  change f.ker.index = p,
  refine or.resolve_left (nat.prime.eq_one_or_self_of_dvd hp f.ker.index _) _,
  --  f.ker.index ∣ p,
  apply aux_dvd_lemma _ _ hp,
  -- f.ker.index ∣ p.factorial : Lagrange on range
  { /- -- These two lines furnished the standard equality : f.ker.index = fintype.card ↥(f.range)
    let hf := subgroup.index_comap ⊥ f,
    simp only [monoid_hom.comap_bot, subgroup.relindex_bot_left, nat.card_eq_fintype_card] at hf, -/
    have hf := subgroup.index_ker f, rw nat.card_eq_fintype_card at hf,
    rw [hf, ← hHp],
    unfold subgroup.index,
    rw [nat.card_eq_fintype_card, ← fintype.card_perm],
    refine f.range.card_subgroup_dvd_card },
  -- Condition on prime factors of f.ker.index : hypothesis on G
  { intros l hl hl', apply hp' hl,
    exact dvd_trans hl' f.ker.index_dvd_card },
  -- f.ker.index ≠ 1
  { intro hf,
    apply nat.prime.ne_one hp,
    rw [← hHp, subgroup.index_eq_one, eq_top_iff],
    apply le_trans _ (subgroup.normal_core_le H),
    rw [← eq_top_iff, ← subgroup.index_eq_one, subgroup.normal_core_eq_ker],
    exact hf },
  rw hHp, exact nat.prime.ne_zero hp,
end

/-- A subgroup of index 2 is normal -/
theorem subgroup.normal_of_index_eq_two {G : Type*} [group G]
  {H : subgroup G} (hH : H.index = 2) : H.normal :=
begin
  haveI : fintype (G⧸H),
  { refine fintype_of_not_infinite _,
    introI h,
    suffices : 2 ≠ 0, apply this,
    rw ← hH,
    unfold subgroup.index,
    unfold nat.card,
    rw cardinal.mk_to_nat_of_infinite,
    exact two_ne_zero, },
  let f := (mul_action.to_perm_hom G (G ⧸ H)),
  suffices : f.ker = H,
  { rw ← this, refine monoid_hom.normal_ker f, },
  suffices : H.normal_core.relindex H = 1,
  { rw ← subgroup.normal_core_eq_ker,
    unfold subgroup.relindex at this,
    rw subgroup.index_eq_one  at this,
    apply le_antisymm, apply subgroup.normal_core_le,
    intros x hx,
    rw [← subgroup.coe_mk H x hx, ← subgroup.mem_subgroup_of, this],
    apply subgroup.mem_top },

  suffices : H.index ≠ 0,
  apply mul_left_injective₀ this, dsimp,
  rw (subgroup.relindex_mul_index (subgroup.normal_core_le H)),
  rw one_mul,
  rw subgroup.normal_core_eq_ker,
  rw hH,
--  change f.ker.index = 2,
  apply nat.eq_of_lt_succ_of_not_lt ,
  rw [subgroup.index_ker f, nat.card_eq_fintype_card],
  rw nat.lt_succ_iff, apply nat.le_of_dvd two_pos,
  refine dvd_trans f.range.card_subgroup_dvd_card _,
  rw [fintype.card_perm, ← nat.card_eq_fintype_card],
  unfold subgroup.index at hH, rw hH, norm_num,

  -- ¬(f.ker.index < 2)
  intro h,
  apply nat.not_succ_le_self 1,
  rw nat.lt_succ_iff at h, change 2 ≤ 1,
  apply le_trans _ h,
  rw [← hH, ← subgroup.normal_core_eq_ker H],
  apply nat.le_of_dvd,
  { rw zero_lt_iff,
    rw [subgroup.normal_core_eq_ker H, subgroup.index_ker f, nat.card_eq_fintype_card],
    exact fintype.card_ne_zero, },
  apply subgroup.index_dvd_of_le,
  exact (subgroup.normal_core_le H),
  { rw hH, norm_num, },
end

variable {α}
-- I don't know why this stuff is not there !

/-- Any permutation is a product of a list of swaps -/
theorem  equiv.perm.is_prod_swap_list (g : equiv.perm α)  :
  ∃ (l : list (equiv.perm α)), (∀ (s : equiv.perm α), s ∈ l → s.is_swap) ∧ g = l.prod :=
begin
  apply equiv.perm.swap_induction_on g,
  { use list.nil,
    split,
    { intros s hs, exfalso, exact list.not_mem_nil s hs },
    { simp only [list.prod_nil] } },
  { intros f x y hxy hf,
    obtain ⟨l, hl, hf⟩ := hf,
    use (equiv.swap x y) :: l,
    split,
    { intros s hs,
      rw list.mem_cons_iff at hs,
      cases hs with hs hs,
      rw hs, exact ⟨x,y, hxy, rfl⟩,
      exact hl s hs },
    rw list.prod_cons,
    rw hf }
end

/-- The alternating group is the only subgroup of index 2 of the permutation group -/
lemma is_alternating_of_index_2 {G : subgroup (equiv.perm α)}
  (hG : G.index = 2) : alternating_group α = G :=
begin
  haveI hG' := subgroup.normal_of_index_eq_two hG,
  let s : (equiv.perm α) →* (equiv.perm α ⧸ G) := quotient_group.mk' G,
  rw alternating_group_eq_sign_ker,
  rw ← quotient_group.ker_mk G,
  have hG'' : is_commutative (equiv.perm α ⧸ G) (*),
  { refine is_commutative_of_prime_order _,
    exact 2, exact nat.fact_prime_two,
    rw ← nat.card_eq_fintype_card,
    exact hG },

  have : ∃ (g : equiv.perm α), g.is_swap ∧ g ∉ G,
  { by_contra, push_neg at h,
    suffices : G = ⊤,
      rw this at hG, rw subgroup.index_top at hG,
      apply (1 : ℕ).one_ne_bit0, exact hG,
    rw eq_top_iff,
    rw ← equiv.perm.closure_is_swap,
    rw subgroup.closure_le G,
    intros g hg,
    simp only [set.mem_set_of_eq] at hg,
    simp only [set_like.mem_coe],
    exact h g hg },
  obtain ⟨k, hk, hk'⟩ := this,

  have this' : ∀ (g : equiv.perm α), g.is_swap → s g = s k,
  { intros g hg,
    obtain ⟨a, b, hab, habg⟩ := hg,
    obtain ⟨x, y, hxy, hxyk⟩ := hk,
    obtain ⟨u, hu⟩ := equiv.perm.is_conj_swap hab hxy,
    let hu' := congr_arg s (semiconj_by.eq hu),
    simp only [map_mul] at hu',
    apply mul_left_cancel,
    swap, exact s u,
    rw [habg, hxyk, hu'],
    apply hG''.comm },

  have hsk2 : (s k) ^ 2 = 1,
  { rw pow_two, rw ← map_mul,
    obtain ⟨x, y, hxy, hxyk⟩ := hk,
    rw hxyk,
    rw equiv.swap_mul_self,
    rw map_one },

  ext g,
  simp only [equiv.perm.sign.mem_ker, (quotient_group.mk' G).mem_ker],


  obtain ⟨l, hl, hg⟩ := g.is_prod_swap_list,
  let hsg := equiv.perm.sign_prod_list_swap hl,
  rw ← hg at hsg,
  have hsg' : s g = (s k) ^l.length,
  { rw hg,
    rw map_list_prod,
    rw list.prod_eq_pow_card (list.map s l) (s k) _,
    rw list.length_map,
    intros x hx,
    simp only [list.mem_map] at hx,
    obtain ⟨y, hyl, hxy⟩ := hx,
    rw ← hxy,
    apply this', exact hl y hyl, },
  obtain ⟨m, hm⟩ := nat.even_or_odd' (l.length),
  have neg_one_neq_one : (-1 : units ℤ) ≠ 1 :=
  begin
    intro h,
    rw ← units.eq_iff at h,
    simpa only using h,
  end,

  cases hm with hm hm,
  { rw [hm, pow_mul] at hsg hsg',
    rw hsk2 at hsg', rw int.units_sq at hsg,
    rw one_pow at hsg' hsg,
    simp only [hsg, hsg'],
    simp only [eq_self_iff_true] },
  { rw [hm, pow_add, pow_mul, pow_one] at hsg hsg',
    rw hsk2 at hsg', rw int.units_sq at hsg,
    rw [one_pow, one_mul] at hsg' hsg,
    rw [hsg, hsg'],
    simp only [quotient_group.mk'_apply, quotient_group.eq_one_iff],
    split,
    { intro h, exfalso, exact neg_one_neq_one h },
    { intro h, exfalso, exact hk' h } }
end

lemma large_subgroup_of_perm_contains_alternating {G : subgroup (equiv.perm α)}
  (hG : fintype.card (equiv.perm α) ≤ 2 * fintype.card G) :
  alternating_group α ≤ G :=
begin
  cases nat.eq_zero_or_pos G.index,
  { exfalso,
    exact subgroup.index_ne_zero_of_finite h },
  cases eq_or_gt_of_le (nat.succ_le_iff.mpr h) with h h,
  { rw subgroup.index_eq_one at h, rw h, exact le_top },
  rw ← nat.succ_le_iff at h, norm_num at h,

  apply @le_of_eq _ _ (alternating_group α) G,
  apply is_alternating_of_index_2,
  refine le_antisymm _ h,

  refine nat.le_of_mul_le_mul_left _ _,
  swap,
  { rw [mul_comm, subgroup.index_mul_card, mul_comm],
    exact hG },
  exact fintype.card_pos
end

/-- A subgroup of the permutation group of index ≤ 2 contains the alternating group -/
lemma contains_alternating_of_index_le_2' {G : subgroup (equiv.perm α)}
  (hG : G.index ≤ 2) : alternating_group α ≤ G :=
begin
  apply large_subgroup_of_perm_contains_alternating,
  rw ← subgroup.index_mul_card G,
  apply nat.mul_le_mul_right _ hG,
end


#lint
