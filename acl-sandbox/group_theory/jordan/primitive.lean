/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/


import .blocks
import .equivariant_map

open mul_action

section equivariant_map

variables {M : Type*} [group M] {α : Type*} [mul_action M α]
variables {N β : Type*} [group N] [mul_action N β]


lemma is_trivial_block_of_surjective_map {φ : M → N} {f : α →ₑ[φ] β}
  (hf : function.surjective f.to_fun) {B : set α}
  (hB : is_trivial_block B) : is_trivial_block (f '' B) :=
begin
sorry
end

lemma is_preprimitive_of_surjective_map
  {φ : M → N} {f : α →ₑ[φ] β} (hf : function.surjective f.to_fun)
  (h : is_preprimitive M α) : is_preprimitive N β :=
begin
  let h.htb := h.has_trivial_blocks,
  apply is_preprimitive.mk,
  { apply is_pretransitive_of_surjective_map hf,
    exact h.to_is_pretransitive },
  { intros B hB,
    rw ← (set.image_preimage_eq B hf),
    apply is_trivial_block_of_surjective_map hf,
    apply h.htb,
    simp only [equivariant_map.to_fun_eq_coe],
    exact @is_block_preimage M _ α _ N β _ _ f hB,


    cases h.htb (is_block_preimage f hB) with hB' hB',
    { apply or.intro_left,
      simp only [set.subsingleton_coe] at hB' ⊢,
      apply set.subsingleton.image hB' },
    { apply or.intro_right, rw hB',
      simp only [set.top_eq_univ],
      rw set.image_univ, rw set.range_iff_surjective,
      assumption } }
end

lemma is_pretransitive_via_bijective_bihom (f : mul_action_bihom M α N β)
  (hf : function.bijective f.to_fun) (hφ : function.surjective f.to_monoid_hom.to_fun) :
  is_pretransitive M α ↔ is_pretransitive N β :=
begin
  split,
  apply is_pretransitive_of_bihom f (function.bijective.surjective hf),
  intro hN, let hN_eq := hN.exists_smul_eq,
  apply is_pretransitive.mk,
  intros x y,
  obtain ⟨k, hk⟩ := hN_eq (f.to_fun x) (f.to_fun y),
  obtain ⟨g, rfl⟩ := hφ k,
  use g,
  apply function.bijective.injective hf,
  rw ← f.map_smul', exact hk,
end

lemma is_preprimitive_via_bijective_bihom_iff (f : mul_action_bihom M α N β)
  (hf : function.bijective f.to_fun) (hφ : function.bijective f.to_monoid_hom.to_fun) :
  is_preprimitive M α ↔ is_preprimitive N β :=
begin
  split,
  apply is_preprimitive_via_surjective_bihom (function.bijective.surjective hf),
  intro hN,
  apply is_preprimitive.mk,
  rw (is_pretransitive_via_bijective_bihom f hf (function.bijective.surjective hφ)),
  exact hN.to_is_pretransitive,
  intros B hB,
  let B' := f.to_fun '' B,
  suffices hB' : is_block N β B',
  cases hN.has_trivial_blocks hB' with hB' hB',
  { apply or.intro_left,
    simp only [set.subsingleton_coe] at ⊢ hB',
    exact set.subsingleton_of_image (function.bijective.injective hf) B hB' },
  { apply or.intro_right,
    rw set.top_eq_univ at hB' ⊢,
    rw ← set.preimage_univ,
    rw set.eq_preimage_iff_image_eq hf,
    exact hB' },
  rw is_block.mk at hB ⊢,
  intro k, obtain ⟨g, hg⟩ := (function.bijective.surjective hφ) k,
  suffices : k • B' = f.to_fun '' (g • B),
  rw this,
  cases hB g with hBg hBg,
  { apply or.intro_left, rw hBg },
  { apply or.intro_right,
    exact set.disjoint_image_of_injective (function.bijective.injective hf) hBg },
  rw ← hg,
  change (λ y, f.to_monoid_hom.to_fun g • y) '' B' = f.to_fun '' ((λ x, g • x) '' B),
  simp only [← set.image_comp],
  refine congr_arg2 _ _ (rfl),
  ext x, simp only [monoid_hom.to_fun_eq_coe, function.comp_app],
  rw f.map_smul',
end



theorem is_primitive_of_bihom' [hfX : fintype X] [decidable_eq X] (htGX : is_pretransitive G X)
  {H : Type*} [group H] {C : Type*} -- [fintype C] [decidable_eq C]
  [mul_action H C]
  (hH : is_preprimitive H C)
  {j : mul_action_bihom H C G X} (hj : function.injective j.to_fun)
  (hC : 2 * fintype.card (set.range j.to_fun) > fintype.card X) :
  is_preprimitive G X :=
begin
  apply is_preprimitive.mk htGX,
  intros B hB,

  cases subsingleton_or_nontrivial B with hB_ss hB_nt,
  exact or.intro_left _ hB_ss,

  rw or_iff_not_imp_right,
  intro hB_ne_top,

  have hB_ne : nonempty ↥B :=  @nontrivial.to_nonempty _ hB_nt,
  have hB_ne' : 0 < fintype.card B := fintype.card_pos_iff.mpr hB_ne,
  rw set.nonempty_coe_sort at hB_ne,

  suffices : fintype.card B < 2,
  { rw [← not_nontrivial_iff_subsingleton, ← fintype.one_lt_card_iff_nontrivial, not_lt],
    exact nat.lt_succ_iff.mp this },

  have hcard_eq : ∀ (g : G), B.to_finset.card = (g • B).to_finset.card,
  { intro g,
    rw finset.card_congr (λ b hb, g • b) _ _ _ ,
    swap,
    { intros a ha, simp, simp at ha, exact ⟨a,ha,rfl⟩, },
    { intros a b _ _ h,
      apply mul_action.injective g,
      simp only at h, exact h },
    { intros b hb,
      simp only [set.mem_to_finset] at hb,
      obtain ⟨a, ha, rfl⟩ := hb,
      use a, use (set.mem_to_finset.mpr ha) } },

  have hba : ∀ (g : G), is_block H C (j.to_fun ⁻¹' (g • B)),
  { intro g,
    -- apply sub_mul_action.is_block,
    -- exact subgroup.is_block G X (is_block_of_block G X g hB)

    sorry },

  have hyp : ∀ (g : G), ¬ set.range j.to_fun ≤ (g • B),
  { intros g hg,
    suffices : 2 * B.to_finset.card > fintype.card X,
    { obtain ⟨k, hXk⟩ := @card_of_block_divides G X _ _ _ htGX B hB hB_ne,
      simp only [mul_comm, hXk, set.to_finset_card] at this,
      have hk : k < 2, { rw ← (mul_lt_mul_right hB_ne'), exact this },

      cases nat.eq_or_lt_of_le (nat.le_of_lt_succ hk) with hk1 hk0,
      { apply hB_ne_top,
        rw [hk1, mul_one] at hXk,
        simp only [set.top_eq_univ],
        rw [← set.coe_to_finset B, ← finset.coe_univ, finset.coe_inj],
        apply finset.eq_univ_of_card B.to_finset, rw hXk,
        exact set.to_finset_card B },
      { rw [nat.eq_zero_of_le_zero (nat.le_of_lt_succ hk0), mul_zero] at hXk,
        exfalso,
        have : fintype.card ↥B ≤ fintype.card X := set_fintype_card_le_univ B,
        rw hXk at this,
        rw (nat.eq_zero_of_le_zero this) at hB_ne',
        exact lt_irrefl 0 hB_ne' } },

    apply lt_of_lt_of_le hC,
    simp only [mul_le_mul_left, nat.succ_pos'],
    rw hcard_eq,
    rw set.le_eq_subset at hg,
    refine le_trans _ (finset.card_le_of_subset (set.to_finset_mono.mpr hg)),
    apply le_of_eq,
    rw set.to_finset_card },

  -- À ce point, on a prouvé hyp :
  -- ∀ g, g • B ne contient pas C.
  -- On reformule :
  have hyp : ∀ (g : G), (j.to_fun ⁻¹' (g • B) : set C) ≠ (⊤ : set C),
  { simp only [not_exists, set.le_eq_subset] at hyp,
    intros g h,
    apply hyp g,
    rintros x ⟨y, rfl⟩,
    rw ← set.mem_preimage, rw h,
    rw set.top_eq_univ,
    apply set.mem_univ },

  -- en déduire, via la preprimitivité (hH), que (j.to_fun.range  ∩ (g • B)) ≤ 1
  have hyp' : ∀ (g : G), fintype.card (set.range j.to_fun ∩ (g • B) : set X) ≤ 1,
  { intro g,
    rw fintype.card_le_one_iff_subsingleton,
    rw set.inter_comm,
    rw ← set.image_preimage_eq_inter_range,
    rw set.subsingleton_coe ,
    apply set.subsingleton.image ,
    rw ← set.subsingleton_coe,
    exact or.resolve_right (hH.has_trivial_blocks (hba g)) (hyp g) },

  -- en déduire que le système de blocs { g • B } a pour cardinal au moins card(C)
  have : fintype.card (set.range j.to_fun) ≤ fintype.card (set.range (λ g, g • B)),
  { simp only [← set.to_finset_card],
    rw setoid.is_partition.card_set_eq_sum_parts (set.range j.to_fun)
      (is_block_system.of_block G X hB hB_ne).left,
    rw finset.card_eq_sum_ones,
    refine finset.sum_le_sum _,
    intros t ht,
    simp only [set.mem_to_finset, set.mem_range] at ht,
    obtain ⟨g, ht⟩ := ht,
    rw ← ht,
    simp only [set.to_finset_card],
    exact hyp' g },

  have thisX : fintype.card X = fintype.card B * fintype.card (set.range (λ (g : G), g • B)),
  { rw ← @card_of_block_mul_card_of_orbit_of G X _ _ _ htGX B hB hB_ne ,
    conv_rhs { rw mul_comm, },
    rw set.to_finset_card },
  /- On peut conclure que B < 2 :
 via thisX : X = P * B, this : C ≤ P, hC : 2 * C > X -/

  rw thisX at hC, -- 2 * C > P * B
  apply lt_of_mul_lt_mul_right',
  apply lt_of_le_of_lt _ hC,
  apply nat.mul_le_mul_left _ this,
end


end primitivity
