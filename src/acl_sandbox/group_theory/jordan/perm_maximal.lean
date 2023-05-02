/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic.basic tactic.group
import group_theory.solvable
import group_theory.group_action.sub_mul_action
import order.minimal
import .for_mathlib.alternating
import .for_mathlib.group_theory__subgroup__basic
import .for_mathlib.stabilizer
import .for_mathlib.set
import .primitive
import .multiple_transitivity
import .jordan
import .mul_action_finset

/-# Maximal subgroups of the symmetric groups

This file establishes that the stabilizer of `s : set α` is a maximal subgroup of the symmetric group `equiv.perm α` when `α` is finite and the cardinality of `s` is not half of that of `α`.
This is the *intransitive case* of the O'Nan-Scott classification.
As a corollary, the action of `equiv.perm α` on finsets of `α` of given cardinality, not equal to the half of that of `α` is primitive.

* `equiv.perm.is_maximal_stab` : the stabilizer of `s : set α` is a maximal subgroup of the symmetric group `equiv.perm α` when `α` is finite and the cardinality of `s` is not half of that of `α`.


-/


open_locale pointwise

lemma nat.add_lt_of_le_lt (a b c d : ℕ) (hab : a ≤ c) (hbd : b < d) : a + b < c + d :=
begin
apply nat.lt_of_lt_of_le,
apply nat.add_lt_add_left _ a, use d, exact hbd,
apply nat.add_le_add_right hab d,
end

lemma subgroup_of_group_of_order_two {G : Type*} [group G] [fintype G] (hG : fintype.card G = 2)
  (H : subgroup G) : H = ⊥ ∨ H = ⊤ :=
begin
  classical,
  cases le_or_lt (fintype.card H) 1,
  { apply or.intro_left, apply subgroup.eq_bot_of_card_le, exact h, },
  { apply or.intro_right, apply subgroup.eq_top_of_card_eq,
    apply le_antisymm,
    { apply nat.le_of_dvd, refine fintype.card_pos,
      refine subgroup.card_subgroup_dvd_card H, },
    rw hG, exact h, },
end

namespace equiv.perm
open mul_action

variables {α : Type*} [decidable_eq α] (G : Type*) [group G] [mul_action G α]

lemma is_pretransitive.of_partition (s : set α) :
  (∀ (a ∈ s) (b ∈ s), ∃ (g : G), g • a = b) →
  (∀ (a ∈ sᶜ) (b ∈ sᶜ), ∃ (g : G), g • a = b) →
  (stabilizer G s ≠ ⊤) →
  -- (∃ (a b : α) (g : G), a ∈ s ∧ b ∈ sᶜ ∧ g • a = b) →
  is_pretransitive G α :=
begin
  intros hs hs' hG,
  suffices hss' : (∃ (a b : α) (g : G), a ∈ s ∧ b ∈ sᶜ ∧ g • a = b),
  obtain ⟨a, b, g, ha, hb, hgab⟩ := hss',
  apply is_pretransitive.mk_base a,
  intro x,
  cases em (x ∈ s) with hx hx',
  exact hs a ha x hx,
  rw ← set.mem_compl_iff at hx',
  obtain ⟨k, hk⟩ := hs' b hb x hx',
  use k * g,
  rw [mul_action.mul_smul, hgab, hk],
  --
  by_contradiction hyp,
  push_neg at hyp,
  apply hG,
  rw [eq_top_iff, mul_action.le_stabilizer_iff],
  intros g _,
  rintros b ⟨a, ha, hgab⟩,
  by_contradiction hb,
  exact hyp a b g ha (set.mem_compl hb) hgab,
end

lemma swap_mem_stabilizer {a b : α} {s : set α} (ha : a ∈ s) (hb : b ∈ s) :
  equiv.swap a b ∈ stabilizer (equiv.perm α) s :=
begin
  suffices : (equiv.swap a b) • s ⊆ s,
  { rw mem_stabilizer_iff,
    apply set.subset.antisymm,
    exact this,
    exact set.subset_set_smul_iff.mpr this, },
  rintros _ ⟨x, hx, rfl⟩,
  simp only [equiv.perm.smul_def],
  cases em (x = a) with hxa hxa',
  rw [hxa, equiv.swap_apply_left], exact hb,
  cases em (x = b) with hxb hxb',
  rw [hxb, equiv.swap_apply_right], exact ha,
  rw equiv.swap_apply_of_ne_of_ne hxa' hxb', exact hx,
end

lemma ne_one_of_is_swap {f : equiv.perm α} (hf : f.is_swap) : f ≠ 1 :=
begin
  intro h1,
  obtain ⟨x, y, hxy, h⟩ := hf,
  rw h1 at h, apply hxy,
  rw ← equiv.swap_apply_left x y, rw ← h,
  simp only [equiv.perm.coe_one, id.def],
end

lemma swap_is_swap_iff {a b : α} : (equiv.swap a b).is_swap ↔ a ≠ b :=
begin
  split,
  { intros h hab,
    suffices : equiv.swap a b ≠ 1,
    { apply this,
      rw [← hab, equiv.swap_self],
      ext x, simp only [equiv.coe_refl, equiv.perm.coe_one], },
    exact ne_one_of_is_swap h, },
  { intro h, use a, use b, exact ⟨h, rfl⟩, },
end

variable [fintype α]

open_locale classical

lemma _root_.fintype.card_add_compl (s : set α) : fintype.card s + fintype.card (sᶜ : set α) = fintype.card α :=
begin
  rw fintype.card_compl_set ,
  rw add_comm,
  rw nat.sub_add_cancel,
  exact set_fintype_card_le_univ s,
end

lemma card_smul_eq (s : set α) (g : equiv.perm α) : fintype.card (g • s : set α)  = fintype.card s :=
begin
  rw ← set.coe_to_finset s,
  simp only [← set.to_finset_card],
  change ((λ x, g • x) '' ↑(s.to_finset)).to_finset.card = _,
  simp_rw ← finset.coe_image ,
  simp only [finset.to_finset_coe],
  rw finset.card_image_of_injective _ (mul_action.injective g),
end

lemma moves_in (G : subgroup (equiv.perm α)) (t : set α) (hGt : stabilizer (equiv.perm α) t < G) :
  ∀ (a ∈ t) (b ∈ t), ∃ (g : G), g • a = b :=
begin
  intros a ha b hb,
  use equiv.swap a b,
  apply le_of_lt hGt,
  apply swap_mem_stabilizer ha hb,
  change (equiv.swap a b) • a = b,
  simp only [equiv.perm.smul_def],
  rw equiv.swap_apply_left,
end

lemma stabilizer_ne_top (s : set α) (hs : s.nonempty) (hsc : sᶜ.nonempty) :
  stabilizer (equiv.perm α) s ≠ ⊤ :=
begin
  obtain ⟨a, ha⟩ := hs,
  obtain ⟨b, hb⟩ := hsc,
  intro h,
  rw set.mem_compl_iff at hb, apply hb,
  have hg : equiv.swap a b ∈ stabilizer (equiv.perm α) s,
  { rw h, apply subgroup.mem_top },
  rw mem_stabilizer_iff at hg,
  rw ← hg,
  rw set.mem_smul_set,
  use a, use ha, apply equiv.swap_apply_left,
end

theorem stabilizer_empty_eq_top (G : Type*) [group G] (α : Type*) [mul_action G α] :
  stabilizer G (∅ : set α) = ⊤ :=
begin
  rw eq_top_iff,
  intro g, apply imp_intro,
  rw mem_stabilizer_iff,
  simp only [set.smul_set_empty],
end

theorem stabilizer_univ_eq_top (G : Type*) [group G] (α : Type*) [mul_action G α] :
  stabilizer G (set.univ : set α) = ⊤ :=
begin
  rw eq_top_iff,
  intro g, apply imp_intro,
  rw mem_stabilizer_iff,
  simp only [set.smul_set_univ],
end

theorem stabilizer_nonempty_ne_top (α : Type*)
  (s : set α) (hs : s.nonempty) (hs' : sᶜ.nonempty) :
  (stabilizer (equiv.perm α) s) ≠ ⊤ :=
begin
  obtain ⟨a : α, ha : a ∈ s⟩ := hs,
  obtain ⟨b : α, hb : b ∈ sᶜ⟩ := hs',
  intro h,
  let g := equiv.swap a b,
  have h' : g ∈ ⊤ :=  subgroup.mem_top g,
  rw [← h , mem_stabilizer_iff] at h',
  rw set.mem_compl_iff at hb,
  apply hb,
  rw ← h',
  use a,
  exact and.intro ha (equiv.swap_apply_left a b)
end


lemma has_swap_of_lt_stabilizer (s : set α)
  (G : subgroup (equiv.perm α))
  (hG : stabilizer (equiv.perm α) s < G) : ∃ (g : equiv.perm α), g.is_swap ∧ g ∈ G :=
begin
    have : ∀ (t : set α), 1 < fintype.card t →
      ∃ (g : equiv.perm α), g.is_swap ∧ g ∈ (stabilizer (equiv.perm α) t),
    { intros t ht,
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩ := fintype.exists_pair_of_one_lt_card ht,
      simp only [ne.def, subtype.mk_eq_mk] at h,
      use equiv.swap a b,
      split,
      rw swap_is_swap_iff, exact h,
      apply swap_mem_stabilizer ha hb, },

    have hs : s.nonempty,
    { by_contradiction,
      rw set.not_nonempty_iff_eq_empty  at h,
      apply ne_top_of_lt hG,
      rw h,
      apply stabilizer_empty_eq_top, },
    have hsc : sᶜ.nonempty,
    { by_contradiction,
      rw set.not_nonempty_iff_eq_empty  at h,
      apply ne_top_of_lt hG,
      rw ← stabilizer_compl, rw h,
      apply stabilizer_empty_eq_top, },

    cases lt_or_le 1 (fintype.card s) with h1 h1',
    { obtain ⟨g, hg, hg'⟩ := this s h1,
      use g, apply and.intro hg,
      exact le_of_lt hG hg',  },
    cases lt_or_le 1 (fintype.card (sᶜ : set α)) with h1c h1c',
    { obtain ⟨g, hg, hg'⟩ := this sᶜ _,
      use g, apply and.intro hg,
      rw stabilizer_compl at hg', exact le_of_lt hG hg',
      convert h1c },
    have hs1 : fintype.card s = 1,
    { apply le_antisymm h1',
      change 0 < fintype.card s,
      rw fintype.card_pos_iff , exact set.nonempty_coe_sort.mpr hs, },
    have hsc1 : fintype.card (sᶜ : set α) = 1,
    { apply le_antisymm,
      convert h1c',
      change 0 < _,
      rw [fintype.card_pos_iff, set.nonempty_coe_sort],
      exact hsc, },

    have hα : fintype.card α = 2, by rw [← fintype.card_add_compl s, hs1, hsc1],

    cases subgroup_of_group_of_order_two _ G,
    exfalso, exact ne_bot_of_gt hG h,
    { rw h,
      rw ← stabilizer_univ_eq_top (equiv.perm α) α,
      apply this,
      suffices : fintype.card _ = 2,
      rw this, norm_num,
      rw ← hα,
      rw set_fintype_card_eq_univ_iff, },

    rw [fintype.card_perm, hα], norm_num,
end

theorem is_maximal_stab' (s : set α) (h0 : s.nonempty) (h1 : sᶜ.nonempty)
  (hα : fintype.card s < fintype.card (sᶜ : set α)) :
  subgroup.is_maximal (stabilizer (equiv.perm α) s) :=
begin
  split, split,
  -- stabilizer (equiv.perm α) s ≠ ⊤
  exact stabilizer_ne_top s h0 h1,

  -- ∀ (G : subgroup (equiv.perm α)), stabilizer (equiv.perm α) s < b) → b = ⊤
  intros G hG,
  -- We need to prove that G = ⊤
  -- G contains a swap
  obtain ⟨g, hg_swap, hg⟩ := has_swap_of_lt_stabilizer s G hG,
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply jordan_swap _ g hg_swap hg,
  -- G acts transitively
  haveI : is_pretransitive G α,
  { apply is_pretransitive.of_partition G s,
    { apply moves_in, exact hG, },
    { apply moves_in, rw stabilizer_compl, exact hG, },
    { intro h,
      apply lt_irrefl G, apply lt_of_le_of_lt _ hG,
      --  G ≤ stabilizer (equiv.perm α) s,
      intros g hg,
      rw mem_stabilizer_iff,
      rw ← subgroup.coe_mk G g hg,
      change (⟨g, hg⟩ : ↥G) • s = s,
      rw ← mem_stabilizer_iff,
      change _ ∈ stabilizer ↥G s,
      rw h, exact subgroup.mem_top ⟨g, hg⟩, }, },

  apply is_preprimitive.mk,

  /- The proof needs 4 steps -/
  /- Step 1 : No block is equal to sᶜ
     This uses that fintype.card s < fintype.card sᶜ.
     In the equality case, fintype.card s = fintype.card sᶜ, it is possible that B = sᶜ,
     then G is the wreath product,
     this is case (b) of the O'Nan-Scott classification of max'l subgroups of the symmetric group -/
    have hB_ne_sc : ∀ (B : set α) (hB : is_block G B), ¬(B = sᶜ),
    { intros B hB hBsc,
      obtain ⟨b, hb⟩ := h1, rw ← hBsc at hb,
      obtain ⟨a, ha⟩ := h0,
      obtain ⟨k, hk⟩ := exists_smul_eq G b a,
      suffices : fintype.card (B : set α) ≤ fintype.card s,
      { apply nat.lt_irrefl (fintype.card B),
        apply lt_of_le_of_lt this,
        simp_rw hBsc, exact hα, },
      rw ← card_smul_eq B k,
      apply set.card_le_of_subset ,
      change k • B ⊆ s,
      rw [← set.disjoint_compl_right_iff_subset, ← hBsc],
      apply or_iff_not_imp_left.mp (is_block.def_one.mp hB k),
      intro h,
      apply set.not_mem_empty a,
      rw ← set.inter_compl_self s,
      split,
        exact ha,
        rw [← hk, ← hBsc, ← h, set.smul_mem_smul_set_iff], exact hb },

    /- Step 2 : A block contained in sᶜ is a subsingleton-/
    have hB_not_le_sc : ∀ (B : set α) (hB : is_block G B) (hBsc : B ⊆ sᶜ), B.subsingleton,
    { intros B hB hBsc,
      suffices : B = coe '' (coe ⁻¹' B : set (sᶜ : set α)),
      rw this,
      apply set.subsingleton.image ,

      suffices : is_trivial_block (coe ⁻¹' B : set (sᶜ : set α)),
      apply or.resolve_right this,

      intro hB',
      apply hB_ne_sc B hB,
      apply set.subset.antisymm hBsc,
      intros x hx,
      rw [← subtype.coe_mk x hx, ← set.mem_preimage],
      rw [hB', set.top_eq_univ], apply set.mem_univ,

      { -- is_trivial_block (coe ⁻¹' B : set (sᶜ : set α)),
        suffices : is_preprimitive (stabilizer G (sᶜ : set α)) (sᶜ : set α),
        refine is_preprimitive.has_trivial_blocks this _,

        -- is_block (coe ⁻¹' B : set (sᶜ : set α))
        let φ' : stabilizer G (sᶜ: set α) → G := coe,
        let f' : (sᶜ : set α) →ₑ[φ'] α := {
          to_fun := coe,
          map_smul' := λ ⟨m, hm⟩ x,
          by simp only [φ', has_smul.smul_stabilizer_def, subgroup.coe_mk], },
        apply mul_action.is_block_preimage f' hB,

        -- is_preprimitive (stabilizer G (sᶜ : set α)) (sᶜ : set α)
        let φ : stabilizer G (sᶜ : set α) → equiv.perm (sᶜ : set α) := mul_action.to_perm,
        let f : (sᶜ : set α) →ₑ[φ] (sᶜ : set α) := {
            to_fun := id,
            map_smul' := λ g x,  by simp only [id.def, equiv.perm.smul_def, to_perm_apply], },
        have hf : function.bijective f := function.bijective_id,
        rw is_preprimitive_of_bijective_map_iff _ hf,
        exact equiv.perm.is_preprimitive ↥sᶜ,

        -- function.surjective φ,
        -- will need to adjust for alternating_group

        intro g,
        suffices : equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) sᶜ,
        use equiv.perm.of_subtype g,
        { apply le_of_lt hG,
          rw ← stabilizer_compl,
          exact this, },
        { rw mem_stabilizer_iff,
          change (equiv.perm.of_subtype g) • sᶜ = sᶜ,
          rw ← mem_stabilizer_iff,
          exact this, },
        { ext ⟨x, hx⟩,
          change (equiv.perm.of_subtype g) • x = _,
          simp only [equiv.perm.smul_def],
          rw equiv.perm.of_subtype_apply_of_mem, },

        { -- equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) sᶜ
          rw mem_stabilizer_iff,
          apply set.subset.antisymm,
          { intro x,
            rw set.mem_smul_set ,
            rintro ⟨y, hy, rfl⟩,
            simp only [equiv.perm.smul_def],
            rw equiv.perm.of_subtype_apply_of_mem g hy,
            refine subtype.mem _, },
          { intros x hx,
            obtain ⟨y, hy⟩ := equiv.surjective g ⟨x, hx⟩,
            rw set.mem_smul_set,
            use y,
            apply and.intro (y.prop),
            simp only [hy, equiv.perm.smul_def, equiv.perm.of_subtype_apply_coe,
              subtype.coe_mk], }, }, },

      { -- B = coe '' (coe ⁻¹' B : set (sᶜ : set α)),
        apply set.subset.antisymm,
        intros x hx,
        use ⟨x, hBsc hx⟩,
        simp only [hx, set.mem_preimage, subtype.coe_mk, eq_self_iff_true, and_self],
        exact set.image_preimage_subset coe B, }, },

    /- Step 3 : A block contained in s is a subsingleton -/
    have hB_not_le_s : ∀ (B : set α) (hB : is_block G B), (B ⊆ s) → B.subsingleton,
    { intros B hB hBs,

      suffices hB_coe : B = coe '' (coe ⁻¹' B : set ↥s),

      suffices : is_trivial_block (coe ⁻¹' B : set s),
      cases this with hB' hB',
      { -- trivial case
        rw hB_coe,
        apply set.subsingleton.image,
        exact hB', },
      { -- coe ⁻¹' B = s
        have hBs' : B = s,
        { apply set.subset.antisymm hBs,
          intros x hx,
          rw ← subtype.coe_mk x hx,
          rw ← set.mem_preimage,
          rw hB',
          rw set.top_eq_univ,
          apply set.mem_univ, },

      have : ∃ g' ∈ G, g' • s ≠ s,
      { by_contradiction,
        apply  (ne_of_lt hG),
        push_neg at h,
        apply le_antisymm,
        exact le_of_lt hG,
        intros g' hg', rw mem_stabilizer_iff, exact h g' hg', },
      obtain ⟨g', hg', hg's⟩ := this,
      cases is_block.def_one.mp hB ⟨g', hg'⟩ with h h,
      { -- case g' • B = B : absurd, since B = s and choice of g'
        exfalso,
        apply hg's, rw ← hBs', exact h, },
      { -- case g' • B disjoint from B

        suffices : (g' • B).subsingleton,
        apply set.subsingleton_of_image _ B this,
        apply function.bijective.injective,
        apply mul_action.bijective,

        apply hB_not_le_sc ((⟨g', hg'⟩ : G) • B),
        exact is_block_of_block _ hB,
        rw ← hBs',
        apply disjoint.subset_compl_right ,
        exact h, }, },

      -- is_trivial_block (coe ⁻¹' B : set s),
      suffices : is_preprimitive (stabilizer G s) (s : set α),
      refine is_preprimitive.has_trivial_blocks this _,

      -- is_block (coe ⁻¹' B : set s)
      let φ' : stabilizer G s → G := coe,
      let f' : s →ₑ[φ'] α := {
        to_fun := coe,
      map_smul' := λ ⟨m, hm⟩ x,
      by simp only [φ', has_smul.smul_stabilizer_def], },
      apply mul_action.is_block_preimage f' hB,

      -- is_preprimitive (stabilizer G s) s
      let φ : stabilizer G s → equiv.perm s := mul_action.to_perm,
      let f : s →ₑ[φ] s := {
          to_fun := id,
          map_smul' := λ g x,  by simp only [id.def, equiv.perm.smul_def, to_perm_apply], },
      have hf : function.bijective f := function.bijective_id,
      rw is_preprimitive_of_bijective_map_iff _ hf,
      exact equiv.perm.is_preprimitive s,

      -- function.surjective φ,
      -- will need to adjust for alternating_group

      intro g,
      suffices : equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) s,
      use equiv.perm.of_subtype g,
      { apply le_of_lt hG, exact this, },
      { rw mem_stabilizer_iff,
        change (equiv.perm.of_subtype g) • s = s,
        rw ← mem_stabilizer_iff,
        exact this, },
      { ext ⟨x, hx⟩,
        change (equiv.perm.of_subtype g) • x = _,
        simp only [equiv.perm.smul_def],
        rw equiv.perm.of_subtype_apply_of_mem, },

      { -- equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) s
        rw mem_stabilizer_iff,
        apply set.subset.antisymm,
        { intro x,
          rw set.mem_smul_set ,
          rintro ⟨y, hy, rfl⟩,
          simp only [equiv.perm.smul_def],
          rw equiv.perm.of_subtype_apply_of_mem g hy,
          refine subtype.mem _, },
        { intros x hx,
          obtain ⟨y, hy⟩ := equiv.surjective g ⟨x, hx⟩,
          rw set.mem_smul_set,
          use y,
          apply and.intro (y.prop),
          simp only [hy, equiv.perm.smul_def, equiv.perm.of_subtype_apply_coe,
            subtype.coe_mk], }, },

      { -- B = coe '' (coe ⁻¹' B : set ↥s),
        apply set.subset.antisymm,
        intros x hx,
        use ⟨x, hBs hx⟩,
        simp only [hx, set.mem_preimage, subtype.coe_mk, eq_self_iff_true, and_self],
        exact set.image_preimage_subset coe B, }, },

    intros B hB,
    unfold is_trivial_block,

    rw or_iff_not_imp_left ,
    intro hB',

    obtain ⟨a, ha, ha'⟩ := set.not_subset_iff_exists_mem_not_mem.mp
      (λ h, hB' ((hB_not_le_sc B hB) h)),
    rw set.not_mem_compl_iff at ha',

    obtain ⟨b, hb, hb'⟩ := set.not_subset_iff_exists_mem_not_mem.mp
      (λ h, hB' ((hB_not_le_s B hB) h)),
    rw ← set.mem_compl_iff at hb',

    have hsc_le_B : sᶜ ⊆ B,
    {   intros x hx',
        suffices : ∃ (k : fixing_subgroup (equiv.perm α) s), k • b = x,
        obtain ⟨⟨k, hk⟩, hkbx : k • b = x⟩ := this,
        suffices : k • B = B,
        rw [← hkbx, ← this, set.smul_mem_smul_set_iff],
        exact hb,
        { -- k • B = B,
          apply or_iff_not_imp_right.mp (is_block.def_one.mp hB ⟨k, _⟩),
          { rw set.not_disjoint_iff_nonempty_inter,
            change (k • B ∩ B).nonempty,
            use a,
            split,
              rw mem_fixing_subgroup_iff at hk,
              rw ← hk a ha',
              exact set.smul_mem_smul_set ha,
              exact ha, },
          { -- ↑k ∈ G
            apply le_of_lt hG,
            exact fixing_subgroup_le_stabilizer (equiv.perm α) s hk, } },
        { -- ∃ (k : fixing_subgroup (equiv.perm α) s), k • b = x,
          suffices : is_pretransitive (fixing_subgroup (equiv.perm α) s)
            (sub_mul_action.of_fixing_subgroup (equiv.perm α) s),
          resetI,
          obtain ⟨k, hk⟩ := exists_smul_eq (fixing_subgroup (equiv.perm α) s)
            (⟨b, hb'⟩ : sub_mul_action.of_fixing_subgroup (equiv.perm α) s)
            ⟨x, hx'⟩,
          use k,
          rw [← subtype.coe_inj, sub_mul_action.coe_smul] at hk,
          exact hk,
          -- is_pretransitive …
          rw is_pretransitive_iff_is_one_pretransitive,
          apply remaining_transitivity',
          simp only [part_enat.card_eq_coe_fintype_card],
          { rw add_comm,
            rw ← fintype.card_add_compl s,
            simp only [add_le_add_iff_left],
            change 0 < _,
            rw fintype.card_pos_iff ,
            simp only [set.nonempty_coe_sort],
            exact h1,  },
          exact equiv_perm_is_fully_pretransitive α, }, },

    -- Conclusion of the proof : B = ⊤
    rw eq_top_iff,
    intros x _,
    obtain ⟨b, hb⟩ := h1,
    obtain ⟨⟨g, hg⟩, hgbx : g • b = x⟩ := exists_smul_eq G b x,
    suffices : g • B = B,
    { rw [← hgbx, ← this, set.smul_mem_smul_set_iff],
      exact hsc_le_B hb, },
    -- g • B = B,
    apply or_iff_not_imp_right.mp (is_block.def_one.mp hB ⟨g, hg⟩),
    rw set.not_disjoint_iff_nonempty_inter,
    change (g • B ∩ B).nonempty,
    apply aux_pigeonhole,

    -- card B + card (g • B) = card B + card B
    -- ... ≥ card sᶜ + card sᶜ
    -- ... > card s + card s ᶜ = card α
    rw ← fintype.card_add_compl s,
    apply nat.lt_of_lt_of_le,
    { apply nat.add_lt_add_right _ (fintype.card (sᶜ : set α)),
      use (fintype.card (sᶜ : set α)),
      exact hα, },
    apply nat.add_le_add,
    { apply le_trans (set.card_le_of_subset hsc_le_B),
      apply le_of_eq,
      rw ← set.coe_to_finset B,
      simp only [← set.to_finset_card],
      change _ = ((λ x, g • x) '' ↑(B.to_finset)).to_finset.card,
      simp_rw ← finset.coe_image ,
      simp only [finset.to_finset_coe],
      rw finset.card_image_of_injective _ (mul_action.injective g) },
    exact set.card_le_of_subset hsc_le_B,
end

/-- stabilizer (equiv.perm α) s is a maximal subgroup of equiv.perm α,
provided s ≠ ⊥, s ≠ ⊤ and fintype.card α ≠ 2 * fintype.card ↥s) -/
theorem is_maximal_stab (s : set α) (h0 : s.nonempty) (h1 : sᶜ.nonempty)
  (hα : fintype.card α ≠ 2 * fintype.card ↥s) : subgroup.is_maximal (stabilizer (equiv.perm α) s) :=
begin
  cases nat.lt_trichotomy (fintype.card s) (fintype.card (sᶜ : set α)) with hs hs',
  { exact equiv.perm.is_maximal_stab' s h0 h1 hs, },
  cases hs' with hs hs,
  { exfalso, apply hα,
    rw [← fintype.card_add_compl s, ← hs, ← two_mul], },
  { rw ← compl_compl s at h0,
    rw ← stabilizer_compl,
    apply equiv.perm.is_maximal_stab' sᶜ h1 h0,
    simp_rw compl_compl s,
    convert hs },
end

end equiv.perm

namespace mul_action

variables {α : Type*} [decidable_eq α] [fintype α]

/-- The action of equiv.perm α on the n-element subsets of α is preprimitive
provided 1 ≤ n < #α and #α ≠ 2*n -/
theorem nat.finset_is_preprimitive_of {n : ℕ} (h_one_le : 1 ≤ n) (hn : n < fintype.card α)
  (hα : fintype.card α ≠ 2 * n) : is_preprimitive (equiv.perm α) (n.finset α) :=
begin
  classical,
  cases nat.eq_or_lt_of_le h_one_le with h_one h_one_lt,
  { -- n = 1 :
    let f : α →[equiv.perm α] nat.finset α 1 := {
      to_fun := λ x, ⟨{x}, finset.card_singleton x⟩,
      map_smul' := λ g x, rfl
    },
    rw ← h_one,
    suffices hf : function.surjective f,
    { apply is_preprimitive_of_surjective_map hf,
      exact equiv.perm.is_preprimitive α, },
    rintro ⟨s, hs⟩,
    change s.card = 1 at hs,
    rw finset.card_eq_one at hs,
    obtain ⟨a, ha⟩ := hs,
    use a,
    simp only [ha, equivariant_map.coe_mk], refl, },

  -- h_one_lt : 1 < n
  haveI : nontrivial α,
  { rw ← fintype.one_lt_card_iff_nontrivial,
    exact lt_trans h_one_lt hn },
  haveI ht : is_pretransitive (equiv.perm α) (n.finset α) := n.finset_is_pretransitive α,
  haveI : nontrivial (n.finset α) :=
    n.finset_nontrivial α (lt_trans (nat.lt_succ_self 0) h_one_lt) hn,
  obtain ⟨sn : n.finset α⟩ := nontrivial.to_nonempty,
  let s := sn.val,
  let hs : s.card = n := sn.prop,
  -- have hs : (s : finset α).card = n := s.prop,
  rw ← maximal_stabilizer_iff_preprimitive (equiv.perm α) sn,
  have : stabilizer (equiv.perm α) sn = stabilizer (equiv.perm α) (s : set α),
  { ext g,
    simp only [mem_stabilizer_iff],
    rw ← subtype.coe_inj,
    change g • s = s ↔ _,
    rw [← finset.coe_smul_finset, ← finset.coe_inj], },
  rw this,
  apply equiv.perm.is_maximal_stab (s : set α),
  { simp only [finset.coe_nonempty, ← finset.card_pos, hs],
    apply lt_trans one_pos h_one_lt, },
  { simp only [← finset.coe_compl, finset.coe_nonempty, ← finset.card_compl_lt_iff_nonempty,
      compl_compl, hs],
    exact hn, },
  { simp only [finset.coe_sort_coe, fintype.card_coe, hs],
    exact hα, },
  apply_instance,
end

end mul_action
