/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import .for_mathlib.set
import .primitive
import .multiple_primitivity

import group_theory.perm.support
import group_theory.index
import group_theory.specific_groups.alternating
import group_theory.specific_groups.cyclic
import .index_normal


/-! # Theorems of Jordan

A proof of theorems of Jordan regarding primitive permutation groups

This mostly follows the book of Wielandt, *Finite permutation groups*

- `is_two_pretransitive_weak_jordan` and `is_two_preprimitive_weak_jordan`
are technical lemmas that prove 2-pretransitivity / 2-preprimitivity
for some group actions (Wielandt, 13.1)

- `is_multiply_preprimitive_jordan` is a multiple preprimitivity criterion of Jordan (1871)
for a preprimitive action: the hypothesis is the preprimitivity
of the sub_mul_action of `fixing_subgroup s` (Wielandt, 13.2)

- `jordan_swap` proves that a primitive subgroup of a permutation group that contains a
swap is equal to the full permutation group (Wielandt, 13.3)

- `jordan_three_cycle` proves that a primitive subgroup of a permutation group that contains a
3-cycle contains the alternating group (Wielandt, 13.3)

## TODO

- Prove `jordan_prime_cycle` that a primitive subgroup of a permutation group that contains
a cycle of prime order contains the alternating group (Wielandt, 13.9 )

- Prove the stronger versions of the technical lemmas of Jordan. (Wielandt, 13.1')

- Golf the proofs of the technical lemmas (prove them at the same time, or find
an adequate induction lemma)
-/


open mul_action
open_locale pointwise


/-- A pretransitivity criterion -/
lemma is_pretransitive_of_fixing_subgroup_inter {α : Type*} {G : Type*} [group G] [mul_action G α]
  {s : set α}
  (hs : is_pretransitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s))
  {g : G} {a : α} (ha : a ∉ s ∪ (g • s)) :
  is_pretransitive (fixing_subgroup G (s ∩ (g • s)))
    (sub_mul_action.of_fixing_subgroup G (s ∩ g • s)) :=
begin
  have ha' : a ∈ (s ∩ (g • s))ᶜ,
  { intro ha', apply ha,
    apply set.mem_union_left,
    exact set.mem_of_mem_inter_left ha' },

  -- For an unknown reason, rw does not work
  apply (is_pretransitive.mk_base_iff
     (⟨a, ha'⟩ : sub_mul_action.of_fixing_subgroup G (s ∩ (g • s)))).mpr,
  let hs_trans_eq := hs.exists_smul_eq,
  rintros ⟨x, hx⟩,
  rw sub_mul_action.of_fixing_subgroup.mem_iff at hx,
  rw [set.mem_inter_iff, not_and_distrib] at hx,
  cases hx with hx hx,
  { -- x ∉ s
  obtain ⟨⟨k, hk⟩, hkax⟩ := hs_trans_eq ⟨a, _⟩ ⟨x, hx⟩,
  use k,
  { rintro ⟨z, hz⟩,
    simp only [subtype.coe_mk],
    simp only [← set_like.coe_eq_coe, subtype.coe_mk] at hkax,
    rw mem_fixing_subgroup_iff at hk,
    rw hk,
    apply set.mem_of_mem_inter_left hz },
  { simp only [← set_like.coe_eq_coe] at hkax ⊢,
    simp only [sub_mul_action.coe_smul_of_tower, sub_mul_action.coe_mk, subtype.coe_mk] at hkax ⊢,
    exact hkax },
  { intro ha', apply ha,
    apply set.mem_union_left,
    exact ha' } },
  { -- x ∉ g • s
    obtain ⟨⟨k, hk⟩, hkax⟩ := hs_trans_eq ⟨g⁻¹ • a, _⟩ ⟨g⁻¹ • x, _⟩,
    use g * k * g⁻¹,
    { rintro ⟨z, hz⟩,
      simp only [subtype.coe_mk],
      simp only [← set_like.coe_eq_coe, subtype.coe_mk] at hkax,
      simp only [← smul_smul],
      rw smul_eq_iff_eq_inv_smul,
      rw mem_fixing_subgroup_iff at hk,
      rw hk,
      rw ← set.mem_smul_set_iff_inv_smul_mem,
      apply set.mem_of_mem_inter_right hz },
    { simp only [← set_like.coe_eq_coe] at hkax ⊢,
      simp only [sub_mul_action.coe_smul_of_tower, sub_mul_action.coe_mk, subtype.coe_mk] at hkax ⊢,
      change k • g⁻¹ • a = g⁻¹ • x at hkax,
      change (g * k * g⁻¹) • a = x,
      rw ← smul_eq_iff_eq_inv_smul at hkax,
      simp only [← smul_smul],
      exact hkax },
    { rw sub_mul_action.of_fixing_subgroup.mem_iff,
      rw ← set.mem_smul_set_iff_inv_smul_mem,
      intro h, apply ha, apply set.mem_union_right, exact h },
    { rw sub_mul_action.of_fixing_subgroup.mem_iff,
      intro h, apply hx,
      rw set.mem_smul_set_iff_inv_smul_mem,
      exact h } }
end

section Jordan

variables {α : Type*}

variables {G : Type*} [group G] [mul_action G α]

/-- In a 2-pretransitive action, the normal closure of stabilizers is the full group -/
lemma normal_closure_of_stabilizer_eq_top
  (hsn' : 2 <  part_enat.card α) (hG' : is_multiply_pretransitive G α 2)
  {a : α} : subgroup.normal_closure (stabilizer G a).carrier = ⊤ :=
begin
  haveI hG : is_pretransitive G α,
  { rw is_pretransitive_iff_is_one_pretransitive,
    apply is_multiply_pretransitive_of_higher,
    exact hG',
    norm_num,
    rw nat.cast_two,
    exact le_of_lt hsn' },

  suffices : (stabilizer G a).is_maximal,
    rw subgroup.is_maximal_def at this,
    apply this.right,

  { --  unfold subgroup.normal_closure,
    split,
    { intros g hg, apply subgroup.closure_le_normal_closure,
      apply subgroup.subset_closure, exact hg },
    { intro hyp,

      -- prendre b, c ≠ a
      have : ∃ (b c : sub_mul_action.of_stabilizer G a), b ≠ c,
      { let x : fin 1 ↪ α := {
        to_fun := λ _, a,
        inj' := function.injective_of_subsingleton _ },
        obtain ⟨y : fin 3 ↪ α , hy⟩ := may_extend _ _ x,
        let hy_inj := y.inj', simp at hy_inj,
        have ha : x ⟨0, (by norm_num)⟩ = a, refl,
        have ha' : y ⟨0, (by norm_num)⟩ = a, rw ← ha, rw ← hy, refl,

        use y ⟨1, (by norm_num)⟩,
        { intro h, simp at h, rw ← ha' at h,
        simpa only [fin.mk_zero, embedding_like.apply_eq_iff_eq, fin.one_eq_zero_iff] using h},
        use y ⟨2, (by norm_num)⟩,
        { intro h, simp at h, rw ← ha' at h,
          simp only [fin.mk_zero, embedding_like.apply_eq_iff_eq, fin.eq_iff_veq] at h,
          simpa using h },
        { intro h, rw [← set_like.coe_eq_coe] at h,
          simp only [sub_mul_action.coe_mk] at h,
          rw [embedding_like.apply_eq_iff_eq, fin.eq_iff_veq] at h,
          simpa using h },
        -- 1 ≤ 3
        simp only [one_le_bit1, zero_le'],
        -- ↑3 ≤ part_enat.card α,
        rw part_enat.coe_le_iff,
        intro h, rw nat.succ_le_iff, revert h,
        rw [← part_enat.coe_lt_iff, nat.cast_two],
        exact hsn',
/-
        rw ← nontrivial_iff ,

        rw ← cardinal.one_lt_iff_nontrivial,
        change 1 < cardinal.mk (sub_mul_action.of_stabilizer G a).carrier,
        rw sub_mul_action.of_stabilizer.def,
        rw [← nat.cast_one, cardinal.mk_fintype, cardinal.nat_cast_lt],
        rw ← add_lt_add_iff_left 1,
        refine lt_of_lt_of_le hsn' (le_of_eq _),
        rw ← fintype.card_of_subsingleton _,
        apply cardinal.nat_cast_injective,

        rw [← cardinal.mk_fintype, nat.cast_add, ← cardinal.mk_fintype],
        simp only [← cardinal.mk_fintype],
        rw cardinal.mk_sum_compl ,
        { use a, exact set.mem_singleton a },
        exact unique.subsingleton -/ },
      obtain ⟨⟨b, hb⟩, ⟨c, hc⟩, hbc⟩ := this,
      simp only [ne.def, subtype.mk_eq_mk] at hbc,

      haveI  : is_pretransitive (stabilizer G a) (sub_mul_action.of_stabilizer G a),
      { rw is_pretransitive_iff_is_one_pretransitive,
        exact (stabilizer.is_multiply_pretransitive G α hG).mp hG' },
--      let hatrans_eq := hatrans.exists_smul_eq,

      -- trouver g ∈ stabilizer G a, g • b = c,
      obtain ⟨⟨g, hg⟩, hgbc⟩ := exists_smul_eq (stabilizer G a)
        (⟨b, hb⟩ : sub_mul_action.of_stabilizer G a) ⟨c, hc⟩,
      have hgbc' : g • b = c,
      { rw ← set_like.coe_eq_coe at hgbc, exact hgbc },

      -- trouver h ∈ G, h⁻¹ • a = b,
      obtain ⟨h : G, hinvab : h • b = a⟩ := exists_smul_eq G b a,

      suffices : (h * g * h⁻¹) • a ≠ a,
      -- h * g * h⁻¹ ∈ subgroup.normal_closure (stabilizer G a)
      { apply this,
        rw ← mem_stabilizer_iff,
        apply hyp,
        refine (subgroup.normal_closure_normal).conj_mem _ _ _,
        apply subgroup.subset_normal_closure,
        exact hg },

      -- h * g * h⁻¹ • a = h • g • b = h • c ≠ h • b = a
      suffices : (h * g * h⁻¹) • a = h • c,
      { rw this, rw ← hinvab,
        intro z,
        apply hbc, apply mul_action.injective h, exact z.symm },

      simp only [← smul_smul],
      rw ← hgbc',
      refine congr_arg2 _ rfl _,
      refine congr_arg2 _ rfl _,
      rw inv_smul_eq_iff, exact hinvab.symm } },

    haveI : nontrivial α,
    { rw [← part_enat.one_lt_card_iff_nontrivial],
      refine lt_trans _ hsn',
      rw [← nat.cast_two, ← nat.cast_one, part_enat.coe_lt_coe ],
      norm_num },

    rw maximal_stabilizer_iff_preprimitive G a,
    apply is_preprimitive_of_two_pretransitive,
    exact hG'
end

variables [fintype α]
open_locale classical

theorem card_eq_one_iff_is_singleton (s : set α) (hs : fintype.card s = 1) :
  ∃ (a : α), s = {a} :=
begin
  classical,
  obtain ⟨⟨a,ha⟩, ha'⟩ := fintype.card_eq_one_iff.mp hs,
  use a,
  rw set.eq_singleton_iff_unique_mem,
  apply and.intro ha,
  intros x hx,
  exact subtype.mk_eq_mk.mp  (ha' ⟨x, hx⟩)
end

/-- A primitivity criterion -/
theorem is_preprimitive_of_fixing_subgroup_inter {G : Type*} [group G] [mul_action G α]
  {s : set α}
  (hs : is_preprimitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s))
  {g : G} {a : α} (ha : a ∉ s ∪ (g • s)) :
  is_preprimitive (fixing_subgroup G (s ∩ (g • s)))
    (sub_mul_action.of_fixing_subgroup G (s ∩ g • s)) :=
begin
  have : fixing_subgroup G s ≤ fixing_subgroup G (s ∩ g • s),
  { apply fixing_subgroup_antitone, apply set.inter_subset_left, },
  let t := s ∩ g • s,
  have hts : t ≤ s := set.inter_subset_left s _,
  let f := sub_mul_action.of_fixing_subgroup.map_of_inclusion G hts,
  have hf: function.injective f,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
    rw ← set_like.coe_eq_coe at hxy ⊢,
    simp only [set_like.coe_mk],
    exact hxy },
  haveI : is_pretransitive ↥(fixing_subgroup G (s ∩ g • s))
    ↥(sub_mul_action.of_fixing_subgroup G (s ∩ g • s)) :=
    is_pretransitive_of_fixing_subgroup_inter hs.to_is_pretransitive ha,

  apply is_preprimitive_of_large_image hs,
  change fintype.card (sub_mul_action.of_fixing_subgroup G (s ∩ g • s)).carrier < _,
    simp only [← set.to_finset_card],
  simp_rw sub_mul_action.of_fixing_subgroup.def,
  rw [set.to_finset_compl, set.to_finset_inter, finset.compl_inter],
  apply nat.lt_of_add_lt_add_right,
  rw finset.card_union_add_card_inter,

  suffices : (g • s).to_finsetᶜ.card = s.to_finsetᶜ.card,
  rw [this, ← two_mul],
  rw nat.lt_iff_add_one_le,
  apply nat.add_le_add,
  { apply le_of_eq,
    apply congr_arg _ _,
    rw ← set.to_finset_compl,
    simp only [set.to_finset_card],
    rw set.card_range_of_injective,
    change fintype.card (sᶜ : set α) =
      fintype.card (sub_mul_action.of_fixing_subgroup G s).carrier,
    rw sub_mul_action.of_fixing_subgroup.def,
    simp only [fintype.card_of_finset, set.mem_compl_iff],
    exact hf },
  { rw nat.succ_le_iff ,
    simp only [← set.to_finset_compl, ← set.to_finset_inter,
    ← set.compl_union],
    rw set.to_finset_card, --  (sᶜ ∩ (g • s)ᶜ),
    rw fintype.card_pos_iff ,
    use a },
  { simp only [finset.card_compl, set.to_finset_card],
    rw smul_set_card_eq, },
  apply_instance,
end

-- α = Ω, s = Δ, α \ s = Γ
-- 1 ≤ #Δ < #Ω, 1 < #Γ < #Ω
/- -- TODO : prove :
theorem strong_jordan_of_pretransitive (hG : is_preprimitive G α)
    {s : set α} {n : ℕ } (hsn : fintype.card s = n.succ)
    (hsn' : 1 + n.succ < fintype.card α)
    (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)) :
  is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup G s).carrier) α 2 :=
sorry
 -/

lemma aux_pigeonhole {s t : set α} (h : fintype.card α < fintype.card s + fintype.card t) :
  (s ∩ t).nonempty :=
begin
  simp only [← set.to_finset_card] at h,
  rw set.nonempty_iff_ne_empty,
  intro hst,
  rw [← set.to_finset_inj, set.to_finset_inter, set.to_finset_empty,
    ← finset.not_nonempty_iff_eq_empty] at hst,
  apply hst,
  rw [← finset.card_compl_lt_iff_nonempty, finset.compl_inter],
  apply lt_of_le_of_lt (finset.card_union_le _ _),
  apply nat.lt_of_add_lt_add_left,
  rw ← add_assoc,
  simp only [finset.card_compl],
  rw nat.add_sub_of_le (finset.card_le_univ s.to_finset),
  conv_rhs { rw add_comm },
  apply nat.add_lt_add_left,
  apply nat.lt_of_add_lt_add_left,
  rw nat.add_sub_of_le (finset.card_le_univ t.to_finset),
  rw add_comm,
  exact h
end



/-- A criterion due to Jordan for being 2-pretransitive (Wielandt, 13.1) -/
theorem is_two_pretransitive_weak_jordan (hG : is_preprimitive G α)
    {s : set α} {n : ℕ} (hsn : fintype.card s = n.succ)
    (hsn' : 1 + n.succ < fintype.card α)
    (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)) :
  is_multiply_pretransitive G α 2 :=
begin
  unfreezingI { revert α G},
  induction n using nat.strong_induction_on with n hrec,
  introsI α G _ _ _ hG s hsn hsn' hs_trans,
  resetI,
--   let hs_trans_eq := hs_trans.exists_smul_eq,
  have hs_ne_top : s ≠ ⊤,
  { intro hs,
    rw [set.top_eq_univ, ← set_fintype_card_eq_univ_iff, hsn] at hs,
    rw hs at hsn',
    simpa only [add_lt_iff_neg_right, not_lt_zero'] using hsn' },
  have hs_nonempty : s.nonempty,
  { rw ← set.nonempty_coe_sort , rw ← not_is_empty_iff ,
    intro hs,
    rw ← fintype.card_eq_zero_iff at hs,
    rw hs at hsn,
    simpa only using hsn },

  cases nat.lt_or_ge n.succ 2 with hn hn,
  { -- Initialization : n = 0
    have hn : n = 0,
    { rw ← le_zero_iff,
      apply nat.le_of_succ_le_succ ,
      apply nat.le_of_lt_succ,
      exact hn },
    rw hn at *,
    let hG_eq := hG.to_is_pretransitive.exists_smul_eq,

    obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton s hsn,
    rw hsa at *,

    rw stabilizer.is_multiply_pretransitive G α hG.to_is_pretransitive,

    rw ← is_pretransitive_iff_is_one_pretransitive,
    exact is_pretransitive_of_surjective_map
      (sub_mul_action.of_fixing_subgroup_of_singleton.map_bijective G a).surjective
      hs_trans },

  -- Induction step : n ≥ 1

  cases nat.lt_or_ge (2 * n.succ) (fintype.card α) with hn1 hn2,
  { -- hn : 2 * s.card < fintype.card α

    -- get a, b ∈ s, a ≠ b
    obtain ⟨⟨a, ha : a ∈ s⟩, ⟨b, hb : b ∈ s⟩, hab⟩ :=
      fintype.one_lt_card_iff_nontrivial.mp (nat.succ_le_iff.mp (by { rw hsn, exact hn })),
    simp only [ne.def, subtype.mk_eq_mk] at hab,

    -- apply rudio to get g ∈ G such that a ∈ g • s, b ∉ g • s
    obtain ⟨g, hga, hgb⟩ :=
      rudio hG s (set.to_finite s) hs_nonempty hs_ne_top a b hab,

    have : ((s.to_finset)ᶜ ∩ (g • s.to_finset)ᶜ).nonempty,
    { rw ← finset.card_compl_lt_iff_nonempty,
      simp only [finset.compl_inter, compl_compl],
      apply lt_of_le_of_lt (finset.card_union_le _ _),
      rw set.to_finset_card,
      suffices : (g • s.to_finset).card = fintype.card s,
      rw [this, hsn, ← two_mul],
      exact hn1,
      change (finset.image (λ x, g • x) s.to_finset).card = _,
      rw finset.card_image_of_injective _ (mul_action.injective g),
      rw set.to_finset_card },
    obtain ⟨c, hc⟩ := this.bex,
    simp only [finset.mem_inter, finset.mem_compl, set.mem_to_finset] at hc,
    let hcs := hc.left,
    have hcgs : g⁻¹ • c ∉ s,
    { intro h,
      rw ← set.mem_to_finset at h,
      apply hc.right,
      rw finset.mem_smul_finset,
      use g⁻¹ • c, apply and.intro h,
      simp only [smul_inv_smul] },

    let t := s ∩ (g • s),
    have hct : c ∉ t, { intro h, apply hcs, apply set.mem_of_mem_inter_left h },
    have hct' : c ∉ s ∪ (g • s),
    { intro h, rw set.mem_union at h, cases h with h h,
      exact hc.left h,
      apply hcgs, rw ← set.mem_smul_set_iff_inv_smul_mem, exact h },
    let ht_trans : is_pretransitive (fixing_subgroup G t) (sub_mul_action.of_fixing_subgroup G t) :=
      is_pretransitive_of_fixing_subgroup_inter hs_trans hct',

    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ fintype.card t < fintype.card s
    have : ∃ (m : ℕ), fintype.card t = m.succ ∧ m < n,
    { suffices : fintype.card t ≠ 0,
      obtain ⟨m, hm⟩ := nat.exists_eq_succ_of_ne_zero this,
      use m, apply and.intro hm,
      rw ← nat.succ_lt_succ_iff, rw ← hm, rw ← hsn,
      apply set.card_lt_card,
      split,
      apply set.inter_subset_left,
      intro hst, apply hgb, apply set.inter_subset_right s,
      apply hst, exact hb,

      intro ht,
      rw fintype.card_eq_zero_iff at ht,
      apply ht.false,
      use ⟨a, ha, hga⟩ },
    obtain ⟨m, htm, hmn⟩ := this,

    have htm' : 1 + m.succ < fintype.card α,
    { apply lt_trans _ hsn',
      simp only [add_lt_add_iff_left],
      rw nat.succ_lt_succ_iff,
      exact hmn },

    -- apply hrec :
    -- is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup t).carrier) α 2
    refine hrec m hmn hG _ htm' ht_trans,
    -- htm does not suffice (because of different hidden instances on fintype)
    convert htm, },
  { -- 2 * s.card ≥ fintype.card α

    have : nontrivial (sᶜ : set α),
    { rw ← fintype.one_lt_card_iff_nontrivial,
      rw ← set.to_finset_card ,
      rw set.to_finset_compl,
      rw finset.card_compl ,
      rw lt_tsub_iff_right ,
      rw [set.to_finset_card , hsn], exact hsn' },
    -- get a, b ∈ sᶜ, a ≠ b
    obtain ⟨⟨a, ha : a ∈ sᶜ⟩, ⟨b, hb : b ∈ sᶜ⟩, hab⟩ := this,
    simp only [ne.def, subtype.mk_eq_mk] at hab,

    have hsc_ne : sᶜ.nonempty := set.nonempty_of_mem ha,
    have hsc_ne_top : sᶜ ≠ ⊤,
    { intro h,
      simp only [set.top_eq_univ, set.compl_univ_iff] at h,
      simpa only [h, set.not_nonempty_empty] using hs_nonempty },

    -- apply rudio to get g ∈ G such that a ∈ g • sᶜ, b ∉ g • sᶜ
    obtain ⟨g, hga, hgb⟩ :=
      rudio hG sᶜ (set.to_finite sᶜ) hsc_ne hsc_ne_top a b hab,

    let t := s ∩ (g • s),
    have hbt : b ∉ t,
    { intro h, rw set.mem_compl_iff at hb, apply hb,
      apply set.mem_of_mem_inter_left h },
    have hat' : a ∉ s ∪ g • s,
    { intro h, rw set.mem_union at h,
      cases h with h h,
      rw set.mem_compl_iff at ha, exact ha h,
      rw set.mem_smul_set_iff_inv_smul_mem at hga h,
      rw set.mem_compl_iff at hga, exact hga h },
    let ht_trans : is_pretransitive (fixing_subgroup G t) (sub_mul_action.of_fixing_subgroup G t) :=
      is_pretransitive_of_fixing_subgroup_inter hs_trans hat',

    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ fintype.card t < fintype.card s
    have : ∃ (m : ℕ), fintype.card t = m.succ ∧ m < n,
    { suffices : t.nonempty,
      { rw [← set.nonempty_coe_sort,  ← fintype.card_pos_iff] at this,
        use (fintype.card t).pred,
        rw ← nat.succ_lt_succ_iff,
        rw nat.succ_pred_eq_of_pos this,
        rw ← hsn,
        apply and.intro rfl,
        apply set.card_lt_card,
        split,
        apply set.inter_subset_left,
        intro hst,
        rw set.mem_compl_iff at hb,
        simp only [smul_compl_set, set.mem_compl_iff, set.not_not_mem] at hgb,
        suffices : s = g • s,
        { apply hb, rw this, exact hgb },
        apply set.eq_of_subset_of_card_le,
        { refine subset_trans hst _,
          apply set.inter_subset_right },
        { apply le_of_eq,
          apply smul_set_card_eq }  },

      { -- aux_pigeonhole ne marche pas !
        rw set.nonempty_iff_ne_empty,
        intro h,
        rw [← set.to_finset_inj, set.to_finset_inter, set.to_finset_empty,
          ← finset.not_nonempty_iff_eq_empty] at h,
        apply h,
        rw [← finset.card_compl_lt_iff_nonempty, finset.compl_inter],
        apply nat.lt_of_add_lt_add_right,
        rw finset.card_union_add_card_inter,
        apply nat.lt_of_add_lt_add_left,
        rw ← add_assoc,
        simp only [finset.card_compl],
        rw nat.add_sub_of_le (finset.card_le_univ s.to_finset),

        conv_rhs { rw add_comm, rw add_assoc },
        apply nat.add_lt_add_left,
        apply nat.lt_of_add_lt_add_left,
        rw nat.add_sub_of_le (finset.card_le_univ (g • s).to_finset),
        rw add_comm,
        suffices : (g • s).to_finset.card = s.to_finset.card,
        { rw this, conv_rhs { rw add_assoc },
          rw [← two_mul, set.to_finset_card, hsn],
          rw ← nat.one_add_le_iff,
          apply nat.add_le_add _ hn2,
          rw nat.succ_le_iff,
          rw finset.card_pos,
          use a,
          simp only [finset.mem_inter, finset.mem_compl, set.mem_to_finset],
          rw [← not_or_distrib, ← set.mem_union],
          exact hat' },
        { conv_lhs { simp only [set.to_finset_card, fintype.card_of_finset] },
          rw finset.card_image_of_injective _ (mul_action.injective g) } } },

    obtain ⟨m, htm, hmn⟩ := this,

    have htm' : 1 + m.succ < fintype.card α,
    { apply lt_trans _ hsn',
      simp only [add_lt_add_iff_left],
      rw nat.succ_lt_succ_iff,
      exact hmn },

    -- apply hrec :
    -- is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup t).carrier) α 2
    refine hrec m hmn hG _ htm' ht_trans,
    -- htm does not work, because of different hidden fintype instances
      rw ← htm, apply fintype.card_congr', refl },


end

/- -- TODO : prove
theorem strong_jordan_of_preprimitive (hG : is_preprimitive G α)
  {s : set α} {n : ℕ} (hsn : fintype.card s = n.succ) (hsn' : 1 + n.succ < fintype.card α)
  (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)) :
  is_multiply_preprimitive (subgroup.normal_closure (fixing_subgroup G s).carrier) α 2 := sorry
 -/

theorem is_two_preprimitive_weak_jordan {n : ℕ} :
  ∀ {α : Type*} [fintype α]
    {G : Type*} [group G] [by exactI mul_action G α],
  by exactI ∀ (hG : is_preprimitive G α)
    {s : set α} (hsn : fintype.card s = n.succ)
    (hsn' : 1 + n.succ < fintype.card α)
    (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)),
  is_multiply_preprimitive G α 2 :=
 begin
  induction n using nat.strong_induction_on with n hrec,
  introsI α _ G _ _ hG s hsn hsn' hs_prim,

  let hs_trans_eq := hs_prim.to_is_pretransitive.exists_smul_eq,
  have hs_ne_top : s ≠ ⊤,
  { intro hs,
    rw [set.top_eq_univ, ← set_fintype_card_eq_univ_iff, hsn] at hs,
    rw hs at hsn',
    simpa only [add_lt_iff_neg_right, not_lt_zero'] using hsn' },
  have hs_nonempty : s.nonempty,
  { rw ← set.nonempty_coe_sort , rw ← not_is_empty_iff ,
    intro hs,
    rw ← fintype.card_eq_zero_iff at hs,
    rw hs at hsn,
    simpa only using hsn },

  cases nat.lt_or_ge n.succ 2 with hn hn,
  { -- Initialization : n = 0
    have hn : n = 0,
    { rw ← le_zero_iff,
      apply nat.le_of_succ_le_succ ,
      apply nat.le_of_lt_succ,
      exact hn },
    rw hn at *,
    let hG_eq := hG.to_is_pretransitive.exists_smul_eq,

    obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton s hsn,
    rw hsa at *,

    rw is_multiply_preprimitive_of_stabilizer G α (nat.le_refl 1) hG.to_is_pretransitive,
    rw ← is_preprimitive_iff_is_one_preprimitive,
    apply is_preprimitive_of_surjective_map
        (sub_mul_action.of_fixing_subgroup_of_singleton.map_bijective G a).surjective,
    exact hs_prim },

  -- Induction step : n ≥ 1

  cases nat.lt_or_ge (2 * n.succ) (fintype.card α) with hn1 hn2,
  { -- hn : 2 * s.card < fintype.card α

    -- get a, b ∈ s, a ≠ b
    obtain ⟨⟨a, ha : a ∈ s⟩, ⟨b, hb : b ∈ s⟩, hab⟩ :=
      fintype.one_lt_card_iff_nontrivial.mp (nat.succ_le_iff.mp (by { rw hsn, exact hn })),
    simp only [ne.def, subtype.mk_eq_mk] at hab,

    -- apply rudio to get g ∈ G such that a ∈ g • s, b ∉ g • s
    obtain ⟨g, hga, hgb⟩ :=
      rudio hG s (set.to_finite s) hs_nonempty hs_ne_top a b hab,

    have : ((s.to_finset)ᶜ ∩ (g • s.to_finset)ᶜ).nonempty,
    { rw ← finset.card_compl_lt_iff_nonempty,
      simp only [finset.compl_inter, compl_compl],
      apply lt_of_le_of_lt (finset.card_union_le _ _),
      rw set.to_finset_card,
      suffices : (g • s.to_finset).card = fintype.card s,
      rw [this, hsn, ← two_mul],
      exact hn1,
      change (finset.image (λ x, g • x) s.to_finset).card = _,
      rw finset.card_image_of_injective _ (mul_action.injective g),
      rw set.to_finset_card },
    obtain ⟨c, hc⟩ := this.bex,
    simp only [finset.mem_inter, finset.mem_compl, set.mem_to_finset] at hc,
    let hcs := hc.left,
    have hcgs : g⁻¹ • c ∉ s,
    { intro h,
      rw ← set.mem_to_finset at h,
      apply hc.right,
      rw finset.mem_smul_finset,
      use g⁻¹ • c, apply and.intro h,
      simp only [smul_inv_smul] },

    let t := s ∩ (g • s),

    have hct : c ∉ t, { intro h, apply hcs, apply set.mem_of_mem_inter_left h },
    have hct' : c ∉ s ∪ (g • s),
    { intro h, rw set.mem_union at h, cases h with h h,
      exact hc.left h,
      apply hcgs, rw ← set.mem_smul_set_iff_inv_smul_mem, exact h },
    let ht_prim : is_preprimitive (fixing_subgroup G t) (sub_mul_action.of_fixing_subgroup G t) :=
      is_preprimitive_of_fixing_subgroup_inter hs_prim hct',

    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ fintype.card t < fintype.card s
    have : ∃ (m : ℕ), fintype.card t = m.succ ∧ m < n,
    { suffices : fintype.card t ≠ 0,
      obtain ⟨m, hm⟩ := nat.exists_eq_succ_of_ne_zero this,
      use m, apply and.intro hm,
      rw ← nat.succ_lt_succ_iff, rw ← hm, rw ← hsn,
      apply set.card_lt_card,
      split,
      apply set.inter_subset_left,
      intro hst, apply hgb, apply set.inter_subset_right s,
      apply hst, exact hb,

      intro ht,
      rw fintype.card_eq_zero_iff at ht,
      apply ht.false,
      use ⟨a, ha, hga⟩ },
    obtain ⟨m, htm, hmn⟩ := this,

    have htm' : 1 + m.succ < fintype.card α,
    { apply lt_trans _ hsn',
      simp only [add_lt_add_iff_left],
      rw nat.succ_lt_succ_iff,
      exact hmn },

    -- apply hrec :
    -- is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup t).carrier) α 2
    refine hrec m hmn hG _ htm' ht_prim,
    rw ← htm, apply fintype.card_congr', refl },
  { -- 2 * s.card ≥ fintype.card α

    have : nontrivial (sᶜ : set α),
    { rw ← fintype.one_lt_card_iff_nontrivial,
      rw ← set.to_finset_card ,
      rw set.to_finset_compl,
      rw finset.card_compl ,
      rw lt_tsub_iff_right ,
      rw [set.to_finset_card , hsn], exact hsn' },
    -- get a, b ∈ sᶜ, a ≠ b
    obtain ⟨⟨a, ha : a ∈ sᶜ⟩, ⟨b, hb : b ∈ sᶜ⟩, hab⟩ := this,
    simp only [ne.def, subtype.mk_eq_mk] at hab,

    have hsc_ne : sᶜ.nonempty := set.nonempty_of_mem ha,
    have hsc_ne_top : sᶜ ≠ ⊤,
    { intro h,
      simp only [set.top_eq_univ, set.compl_univ_iff] at h,
      simpa only [h, set.not_nonempty_empty] using hs_nonempty },

    -- apply rudio to get g ∈ G such that a ∈ g • sᶜ, b ∉ g • sᶜ
    obtain ⟨g, hga, hgb⟩ :=
      rudio hG sᶜ (set.to_finite sᶜ) hsc_ne hsc_ne_top a b hab,

    let t := s ∩ (g • s),
    have hat' : a ∉ s ∪ g • s,
    { intro h, rw set.mem_union at h,
      cases h with h h,
      rw set.mem_compl_iff at ha, exact ha h,
      rw set.mem_smul_set_iff_inv_smul_mem at hga h,
      rw set.mem_compl_iff at hga, exact hga h },
    let ht_prim : is_preprimitive (fixing_subgroup G t) (sub_mul_action.of_fixing_subgroup G t) :=
      is_preprimitive_of_fixing_subgroup_inter hs_prim hat',

    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ fintype.card t < fintype.card s
    have : ∃ (m : ℕ), fintype.card t = m.succ ∧ m < n,
    { suffices : t.nonempty,
      { rw [← set.nonempty_coe_sort,  ← fintype.card_pos_iff] at this,
        use (fintype.card t).pred,
        rw ← nat.succ_lt_succ_iff,
        rw nat.succ_pred_eq_of_pos this,
        rw ← hsn,
        apply and.intro rfl,
        apply set.card_lt_card,
        split,
        apply set.inter_subset_left,
        intro hst,
        rw set.mem_compl_iff at hb,
        simp only [smul_compl_set, set.mem_compl_iff, set.not_not_mem] at hgb,
        suffices : s = g • s,
        { apply hb, rw this, exact hgb },
        apply set.eq_of_subset_of_card_le,
        { refine subset_trans hst _,
          apply set.inter_subset_right },
        { apply le_of_eq,
          apply smul_set_card_eq }  },

      { -- aux_pigeonhole ne marche pas !
        rw set.nonempty_iff_ne_empty,
        intro h,
        rw [← set.to_finset_inj, set.to_finset_inter, set.to_finset_empty,
          ← finset.not_nonempty_iff_eq_empty] at h,
        apply h,
        rw [← finset.card_compl_lt_iff_nonempty, finset.compl_inter],
        apply nat.lt_of_add_lt_add_right,
        rw finset.card_union_add_card_inter,
        apply nat.lt_of_add_lt_add_left,
        rw ← add_assoc,
        simp only [finset.card_compl],
        rw nat.add_sub_of_le (finset.card_le_univ s.to_finset),

        conv_rhs { rw add_comm, rw add_assoc },
        apply nat.add_lt_add_left,
        apply nat.lt_of_add_lt_add_left,
        rw nat.add_sub_of_le (finset.card_le_univ (g • s).to_finset),
        rw add_comm,
        suffices : (g • s).to_finset.card = s.to_finset.card,
        { rw this, conv_rhs { rw add_assoc },
          rw [← two_mul, set.to_finset_card, hsn],
          rw ← nat.one_add_le_iff,
          apply nat.add_le_add _ hn2,
          rw nat.succ_le_iff,
          rw finset.card_pos,
          use a,
          simp only [finset.mem_inter, finset.mem_compl, set.mem_to_finset],
          rw [← not_or_distrib, ← set.mem_union],
          exact hat' },
        { conv_lhs { simp only [set.to_finset_card, fintype.card_of_finset] },
          rw finset.card_image_of_injective _ (mul_action.injective g) } } },

    obtain ⟨m, htm, hmn⟩ := this,

    have htm' : 1 + m.succ < fintype.card α,
    { apply lt_trans _ hsn',
      simp only [add_lt_add_iff_left],
      rw nat.succ_lt_succ_iff,
      exact hmn },

    -- apply hrec :
    -- is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup t).carrier) α 2
    refine hrec m hmn hG _ htm' ht_prim,
    rw ← htm, apply fintype.card_congr', refl }
end

/- These theorems will be deduced from the strong one
theorem is_two_pretransitive_weak_jordan' (hG : is_preprimitive G α)
  {s : set α} (hs : 1 ≤ fintype.card s) (hs' : 2 + fintype.card (s) ≤ fintype.card α)
  (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)) :
  is_multiply_pretransitive G α 2 :=
begin
 -- We can deduce it from jordan0
  apply is_pretransitive_of_subgroup,
  obtain ⟨n,hn : fintype.card ↥s = n.succ⟩ := nat.exists_eq_succ_of_ne_zero
    (nat.one_le_iff_ne_zero.mp hs),
  apply strong_jordan_of_pretransitive hG hn
    (begin rw hn at hs', apply lt_of_lt_of_le _ hs', norm_num,  end)
    hs_trans,
end

theorem weak_jordan_of_preprimitive' (hG : is_preprimitive G α)
  {s : set α} (hs : 1 ≤ fintype.card s) (hs' : 2 + fintype.card (s) ≤ fintype.card α)
  (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)) :
  is_multiply_preprimitive G α 2 :=
begin
 -- We can deduce it from strong_jordan_of_preprimitive
  obtain ⟨n,hn : fintype.card ↥s = n.succ⟩ := nat.exists_eq_succ_of_ne_zero
    (nat.one_le_iff_ne_zero.mp hs),
  apply is_multiply_preprimitive_of_subgroup,
  norm_num,
  refine strong_jordan_of_preprimitive hG hn
    (begin rw hn at hs', apply lt_of_lt_of_le _ hs', norm_num,  end)
    hs_prim
end
-/


-- Notations of Wielandt : s = Δ, n - m = #s, n = #α, m = #sᶜ, 1 < m < n
-- 1 + #s < n , #s ≥ 1

/-- Jordan's multiple primitivity criterion (Wielandt, 13.3) -/
theorem is_multiply_preprimitive_jordan (hG : is_preprimitive G α)
  {s : set α} {n : ℕ} (hsn : fintype.card s = n.succ) (hsn' : 1 + n.succ < fintype.card α)
  (hprim : is_preprimitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)) :
  is_multiply_preprimitive G α (1 + n.succ) :=
begin
  unfreezingI { revert α G },
  induction n with n hrec,
  { -- case n = 0
    introsI α G _ _ _ hG s hsn hα hGs,
    haveI : is_pretransitive G α := hG.to_is_pretransitive,
    obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton s hsn,
    rw hsa at *,
    split,
    { rw stabilizer.is_multiply_pretransitive,
      rw ← is_pretransitive_iff_is_one_pretransitive,
      apply is_pretransitive_of_surjective_map
        (sub_mul_action.of_fixing_subgroup_of_singleton.map_bijective G a).surjective
        hGs.to_is_pretransitive,
      exact hG.to_is_pretransitive, },
    { intros t h,
      suffices ht' : fintype.card t = 1,
      { obtain ⟨b, htb⟩ := card_eq_one_iff_is_singleton t ht',
        rw htb at *,

        obtain ⟨g, hg⟩ := exists_smul_eq G a b,
        have hst : g • ({a} : set α) = ({b} : set α),
        { change (λ x, g • x) '' {a}  = {b},
          rw [set.image_singleton, hg] },
        refine is_preprimitive_of_surjective_map
          (sub_mul_action.of_fixing_subgroup.conj_map_bijective G hst).surjective
          hGs },
      { rw [part_enat.of_fintype, ← nat.cast_one, ← nat.cast_add, part_enat.coe_inj, add_left_inj] at h,
        exact h } } },
  -- Induction step
  introsI α G _ _ _ hG s hsn hα hGs,
  suffices : ∃ (a : α) (t : set (sub_mul_action.of_stabilizer G a)),
    a ∈ s ∧ s = insert a (coe '' t),
  obtain ⟨a, t, ha, hst⟩ := this,
  have ha' : a ∉ coe '' t,
  { intro h, rw set.mem_image at h, obtain ⟨x, hx⟩ := h,
    apply x.prop, rw hx.right, exact set.mem_singleton a },
  have ht_prim : is_preprimitive (stabilizer G a) (sub_mul_action.of_stabilizer G a),
  { rw is_preprimitive_iff_is_one_preprimitive,
    rw ← is_multiply_preprimitive_of_stabilizer G α (nat.le_refl 1) hG.to_is_pretransitive,
    apply is_two_preprimitive_weak_jordan hG hsn hα hGs },

  have hGs' : is_preprimitive ↥(fixing_subgroup ↥(stabilizer G a) t)
    ↥(sub_mul_action.of_fixing_subgroup ↥(stabilizer G a) t),
  { apply is_preprimitive_of_surjective_map
        (sub_mul_action.of_fixing_subgroup_of_stabilizer.map_bijective G a t).surjective,
    apply is_preprimitive_of_surjective_map
        (sub_mul_action.of_fixing_subgroup_of_eq.map_bijective G hst).surjective,
    exact hGs },

  rw ← nat.succ_eq_one_add,
  rw is_multiply_preprimitive_of_stabilizer G α _ hG.to_is_pretransitive,
  rw nat.succ_eq_one_add,
  refine hrec ht_prim _ _ hGs',
  { -- fintype.card t = n.succ
    rw ← set.card_image_of_injective t (subtype.coe_injective),
    apply nat.add_right_cancel,
    rw ← set.card_insert (coe '' t) ha',
    simp_rw ← hst, rw ← nat.succ_eq_add_one, exact hsn,
    apply_instance },
  { -- 1 + n.succ < fintype.card ↥(sub_mul_action_of_stabilizer G α a)
    change _ < fintype.card ↥(sub_mul_action.of_stabilizer G a).carrier,
    rw ← nat.succ_eq_one_add,
    apply nat.lt_of_add_lt_add_right,
    rw sub_mul_action.of_stabilizer.def,
    rw fintype.card_compl_set,
    rw nat.sub_add_cancel (set_fintype_card_le_univ _),
    simp only [set.card_singleton],
    rw add_comm,
    exact hα },
    { apply nat.succ_le_succ, apply nat.zero_le },


  -- ∃ (a : α), a ∈ s
  { suffices : s.nonempty,
    rw set.nonempty_def at this,
    obtain ⟨a, ha⟩ := this,
    use a,
    use coe ⁻¹' s,
    apply and.intro ha,
    rw set.insert_eq,
    rw set.image_preimage_eq_inter_range,
    simp only [subtype.range_coe_subtype, set.singleton_union],
    simp_rw sub_mul_action.of_stabilizer.mem_iff,
    simp only [ne.def],
    ext x,
--    apply subset_antisymm,
    { rw set.mem_insert_iff,
      simp,
      rw or_and_distrib_left,
      simp_rw or_not,
      rw and_true,
      split,
      intro hx, apply or.intro_right _ hx,
      intro hx, cases hx with hx hx,
      rw hx, exact ha,
      exact hx },
    rw set.nonempty_iff_ne_empty,

    intro h,
    simp only [h, set.empty_card'] at hsn,
    simpa using hsn },
end

end Jordan

section Jordan'

open mul_action
open_locale pointwise

variables {α : Type*} [fintype α]
variable {G : subgroup (equiv.perm α)}

lemma eq_s2_of_nontrivial (hα : fintype.card α ≤ 2) (hG : nontrivial G) :
  G = (⊤ : subgroup (equiv.perm α)) :=
begin
  classical,
  apply subgroup.eq_top_of_card_eq,
  apply le_antisymm,
  apply fintype.card_subtype_le ,
  rw [fintype.card_equiv (equiv.cast rfl)],
  refine le_trans _ _,
  exact (2 : ℕ).factorial,
  exact nat.factorial_le hα,
  rw [nat.factorial_two],
  rw ← fintype.one_lt_card_iff_nontrivial at hG,
  exact hG,
end

lemma nontrivial_on_equiv_perm_two {K : Type*} [group K] [mul_action K α]
  (hα : fintype.card α = 2) {g : K}
  {a : α} (hga : g • a ≠ a) : is_multiply_pretransitive K α 2 :=
begin
  classical,
  let φ := mul_action.to_perm_hom K α,
  let f : α →ₑ[φ] α := { to_fun := id, map_smul' := λ k x, rfl },
  have hf: function.bijective f := function.bijective_id,
  suffices : function.surjective φ,
  { rw is_multiply_pretransitive_of_bijective_map_iff this hf,
    rw ← hα,
    exact equiv_perm_is_fully_pretransitive α },
  rw ← monoid_hom.range_top_iff_surjective,
  apply subgroup.eq_top_of_card_eq,
  apply le_antisymm,
  apply fintype.card_subtype_le,
  suffices hg : to_perm g ∈ φ.range,
  { rw [fintype.card_perm, hα, nat.factorial_two, nat.succ_le_iff, subgroup.one_lt_card_iff_ne_bot],
    intro h, apply hga,
    rw [h, subgroup.mem_bot] at hg,
    simpa using congr_fun (congr_arg coe_fn hg) a },
  use g, refl
end

lemma is_pretransitive_of_cycle [decidable_eq α] {g : equiv.perm α} (hg : g ∈ G) (hgc : g.is_cycle) :
  is_pretransitive
    (fixing_subgroup G (↑g.support : set α)ᶜ)
    (sub_mul_action.of_fixing_subgroup G (↑g.support : set α)ᶜ) :=
begin
  obtain ⟨a, hga, hgc⟩ := hgc,

  have hs : ∀ (x : α), g • x ≠ x ↔ x ∈ sub_mul_action.of_fixing_subgroup G (↑g.support : set α)ᶜ,
  { intro x,
    rw sub_mul_action.of_fixing_subgroup.mem_iff,
    simp only [set.mem_compl_iff, finset.mem_coe, equiv.perm.not_mem_support],
    refl },
  let ha := (hs a).mp hga,
  suffices : ∀ x ∈ sub_mul_action.of_fixing_subgroup G (↑g.support : set α)ᶜ,
    ∃ (k : fixing_subgroup G (↑g.support : set α)ᶜ), x = k • a,
  { apply is_pretransitive.mk,
    rintros ⟨x, hx⟩ ⟨y, hy⟩,
    obtain ⟨k, hk⟩ := this x hx,
    obtain ⟨k', hk'⟩ := this y hy,
    use k' * k⁻¹,
    rw ← set_like.coe_eq_coe, rw set_like.coe_mk,
    simp only [sub_mul_action.coe_smul_of_tower, sub_mul_action.coe_mk],
    rw [hk, hk', smul_smul, inv_mul_cancel_right] },
  intros x hx,
  obtain ⟨i, hi⟩ := hgc x _,
  have hg' : (⟨g, hg⟩ : ↥G) ∈ fixing_subgroup G (↑g.support : set α)ᶜ,
  { simp_rw mem_fixing_subgroup_iff G,
    intros y hy,
    simpa only [set.mem_compl_iff, finset.mem_coe, equiv.perm.not_mem_support] using hy },

  let g' : fixing_subgroup ↥G (↑g.support : set α)ᶜ := ⟨(⟨g, hg⟩ : ↥G), hg'⟩,
  use g' ^ i,
  rw ← hi,
  refl,

  exact (hs x).mpr hx,
end

lemma equiv.perm.is_swap.cycle_type [decidable_eq α]
  {σ : equiv.perm α} (h : σ.is_swap) : σ.cycle_type = {2} :=
begin
  simp only [equiv.perm.is_cycle.cycle_type h.is_cycle, equiv.perm.card_support_eq_two.mpr h],
  refl,
end

lemma equiv.perm.is_swap.order_of [decidable_eq α] {σ : equiv.perm α} (h : σ.is_swap) : order_of σ = 2 :=
by rw [← equiv.perm.lcm_cycle_type, h.cycle_type, multiset.lcm_singleton, normalize_eq]

/-- A primitive permutation group that contains a swap is the full permutation group (Jordan)-/
theorem jordan_swap [decidable_eq α] (hG : is_preprimitive G α)
  (g : equiv.perm α) (h2g : equiv.perm.is_swap g) (hg : g ∈ G) : G = ⊤  :=
begin
  classical,
  cases nat.lt_or_ge (fintype.card α) 3 with hα3 hα3,
  { -- trivial case : fintype.card α ≤ 2
    rw nat.lt_succ_iff at hα3,
    apply subgroup.eq_top_of_card_eq,
    apply le_antisymm,
    apply fintype.card_subtype_le ,
    rw [fintype.card_equiv (equiv.cast rfl)],
    refine le_trans (nat.factorial_le hα3) _,
    rw [nat.factorial_two],
    apply nat.le_of_dvd,
    exact fintype.card_pos,
    suffices : order_of g = 2,
    { rw [← set_like.coe_mk g hg, order_of_subgroup] at this,
      rw ← this, exact order_of_dvd_card_univ },
    apply equiv.perm.is_swap.order_of, exact h2g },
  obtain ⟨n, hn⟩ := nat.exists_eq_add_of_le hα3, rw add_comm at hn,

  let s := (g.support : set α),
  have hs2 : fintype.card s = 2,
  { simp only [finset.coe_sort_coe, fintype.card_coe, equiv.perm.card_support_eq_two],
    exact h2g },
  have hsc : fintype.card (sᶜ : set α) = n.succ,
  { rw [fintype.card_compl_set, hs2, hn],
    simp only [nat.succ_sub_succ_eq_sub, nat.add_succ_sub_one],  },

  suffices : is_multiply_preprimitive G α (fintype.card α - 1),
  exact eq_top_of_is_full_minus_one_pretransitive this.left,

  have hn' : fintype.card α - 1 = 1 + n.succ,
  { rw hn,
    conv_rhs {rw [add_comm, nat.succ_eq_add_one] },
    simp only [nat.add_succ_sub_one]},
  rw hn',

  refine is_multiply_preprimitive_jordan hG _ _ _,
  exact ((g.support)ᶜ : set α),
  { rw ← hsc,
    simp only [fintype.card_of_finset, set.mem_compl_iff], },
  { rw hn,
    rw [nat.one_add, ← nat.add_one, ← nat.add_one, add_assoc, add_lt_add_iff_left],
    norm_num },

  haveI : is_pretransitive _ _,
  { apply is_pretransitive_of_cycle hg,
    exact equiv.perm.is_swap.is_cycle h2g, },
  apply is_preprimitive_of_prime,
  change nat.prime (fintype.card (sub_mul_action.of_fixing_subgroup G (g.support : set α)ᶜ).carrier),
  rw sub_mul_action.of_fixing_subgroup.def,
  simp only [compl_compl, finset.coe_sort_coe, fintype.card_coe],
  rw equiv.perm.card_support_eq_two.mpr h2g,
  exact nat.prime_two,
end

/-- A primitive permutation that contains a 3-cycle contains the alternating group (Jordan) -/
theorem jordan_three_cycle [decidable_eq α] (hG : is_preprimitive G α)
  {g : equiv.perm α} (h3g : equiv.perm.is_three_cycle g) (hg : g ∈ G) :
  alternating_group α ≤ G :=
begin
  cases nat.lt_or_ge (fintype.card α) 4 with hα4 hα4,
  { -- trivial case : fintype.card α ≤ 3
    rw nat.lt_succ_iff at hα4,
    apply large_subgroup_of_perm_contains_alternating,
    rw fintype.card_perm,
    apply le_trans (nat.factorial_le hα4),
    norm_num,
    change 2 * 3 ≤ _,
    simp only [mul_le_mul_left, nat.succ_pos'],
    apply nat.le_of_dvd (fintype.card_pos),
    suffices : 3 = order_of (⟨g, hg⟩ : G),
    rw this, classical, exact order_of_dvd_card_univ,

    rw ← equiv.perm.is_three_cycle.order_of h3g,
    conv_lhs { rw ← set_like.coe_mk g hg },
    apply order_of_subgroup,
    exact has_one.nonempty, },

  obtain ⟨n, hn⟩ := nat.exists_eq_add_of_le hα4, rw add_comm at hn,

--  refine is_full_minus_two_pretransitive_iff α _,
  suffices : is_multiply_preprimitive G α (fintype.card α - 2),
  apply alternating_group_le_of_full_minus_two_pretransitive this.left,

  have hn' : fintype.card α - 2 = 1 + n.succ,
  { rw hn,
    conv_rhs {rw [add_comm, nat.succ_eq_add_one]  },
    simp only [nat.succ_sub_succ_eq_sub, nat.add_succ_sub_one] },
  rw hn',

  have hs3 : fintype.card (g.support) = 3,
  { simp only [fintype.card_coe],
    exact equiv.perm.is_three_cycle.card_support h3g },
  refine is_multiply_preprimitive_jordan hG _ _ _,

  exact ((g.support)ᶜ : set α),
  { simp only [fintype.card_compl_set, finset.coe_sort_coe, fintype.card_coe],
    rw equiv.perm.is_three_cycle.card_support h3g,
    rw hn,
    simp only [nat.succ_sub_succ_eq_sub, nat.add_succ_sub_one] },
  { rw hn,
    rw [nat.one_add, ← nat.add_one, ← nat.add_one, add_assoc,  add_lt_add_iff_left],
    norm_num },

  haveI : is_pretransitive _ _,
  { apply is_pretransitive_of_cycle hg,
    exact equiv.perm.is_three_cycle.is_cycle h3g },
  apply is_preprimitive_of_prime,
  change nat.prime(fintype.card (sub_mul_action.of_fixing_subgroup G (g.support : set α)ᶜ).carrier),
  rw sub_mul_action.of_fixing_subgroup.def,
  simp only [compl_compl, finset.coe_sort_coe, fintype.card_coe],
  rw equiv.perm.is_three_cycle.card_support h3g,
  exact nat.prime_three,
end

/- -- TODO : prove
theorem jordan_prime_cycle [decidable_eq α] (hG : is_preprimitive G α)
  {p : nat} (hp : prime p) (hp' : p + 3 ≤ fintype.card α)
  {g : equiv.perm α} (hgc : equiv.perm.is_cycle g) (hgp : fintype.card g.support = p)
  (hg : g ∈ G) : alternating_group α ≤ G := sorry
 -/

end Jordan'

#lint
