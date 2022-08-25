/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/


-- import tactic.basic tactic.group
-- import group_theory.solvable
-- import group_theory.group_action.sub_mul_action
import group_theory.specific_groups.alternating
-- import group_theory.perm.cycle.concrete

import .for_mathlib.alternating
-- import .for_mathlib.group_theory__subgroup__basic

import .primitive
-- import .multiple_transitivity

-- import .jordan
import .perm_iwasawa


open_locale pointwise

open mul_action

section junk

variables {α G H : Type*} [group G] [group H] [mul_action G α] {N : subgroup G}

example (g : G) (s : set α) : g • s = s := sorry
lemma subgroup.map_subgroup_of_eq {K : subgroup N} : (K.map N.subtype).subgroup_of N = K :=
begin
  dsimp [subgroup.subgroup_of],
  rw subgroup.comap_map_eq ,
  simp only [subgroup.ker_subtype, sup_bot_eq],
end

lemma mul_action.stabilizer_subgroup_of_eq {a : α}  :
  stabilizer N a = (stabilizer G a).subgroup_of N :=
begin
  ext n,
  simp only [subgroup.mem_subgroup_of, mem_stabilizer_iff],
  refl,
end

example (K K' : subgroup G) : K < K' ↔ (K ≤ K' ∧ K ≠ K') := lt_iff_le_and_ne

lemma subgroup.map_iff_mono_of_injective {f : G →* H} {K K' : subgroup G}
  (hf : function.injective f) :
  K ≤ K' ↔ subgroup.map f K ≤ subgroup.map f K' :=
begin
  split,
  exact subgroup.map_mono,
  { intro h,
    intros x hx,
    suffices : f x ∈ subgroup.map f K',
    { simp only [subgroup.mem_map] at this,
      obtain ⟨y, hy, hx⟩ := this,
      rw ← hf hx,  exact hy, },
    apply h,
    rw subgroup.mem_map,
    use ⟨x, hx, rfl⟩, },
end

lemma subgroup.map_strict_mono_of_injective {f : G →* H} {K K' : subgroup G}
  (hf : function.injective f) :
  K < K' ↔ subgroup.map f K < subgroup.map f K' :=
begin
  simp only [lt_iff_le_not_le],
  simp_rw ← subgroup.map_iff_mono_of_injective hf,
end

lemma subgroup.map_injective_of_injective {f : G →* H} {K K' : subgroup G}
  (hf : function.injective f) :
  subgroup.map f K = subgroup.map f K' ↔ K = K' :=
begin
  simp only [le_antisymm_iff, ← subgroup.map_iff_mono_of_injective hf],
end


end junk

variables  {α : Type*} [fintype α] [decidable_eq α]

namespace alternating_group


lemma stabilizer_ne_top' (s : set α) (hs : s.nonempty) (hsc : sᶜ.nontrivial) :
  stabilizer (alternating_group α) s ≠ ⊤ :=
begin
  obtain ⟨a, ha⟩ := hs,
  obtain ⟨b, hb, c, hc, hbc⟩ := hsc,
  rw set.mem_compl_iff at hb hc,
  have hac : a ≠ c, { intro h, apply hc, rw ← h, exact ha },
  have hab : a ≠ b, { intro h, apply hb, rw ← h, exact ha },

  intro h, apply hc,

  -- let gc := cycle.form_perm ↑[a,b,c] (begin rw cycle.nodup_coe_iff, simp [hab, hac, hbc] end ),
  let g := equiv.swap a b * equiv.swap a c,
  have hg : g ∈ alternating_group α,
  { rw equiv.perm.mem_alternating_group,
    apply equiv.perm.is_three_cycle.sign,
    apply equiv.perm.is_three_cycle_swap_mul_swap_same hab hac hbc,  },
  suffices : g • s = s,
  { rw ← this,
    use a,
    split, exact ha,
    dsimp [g],
    rw equiv.swap_apply_left,
    rw equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm, },
  change (⟨g, hg⟩ : alternating_group α) • s = s,
  rw ← mul_action.mem_stabilizer_iff, erw h, apply subgroup.mem_top,
end

lemma stabilizer_ne_top (s : set α) (hs : s.nonempty) (hsc : sᶜ.nonempty)
  (hssc : s.nontrivial ∨ (sᶜ : set α).nontrivial) :
  stabilizer (alternating_group α) s ≠ ⊤ :=
begin
  cases hssc with hs' hsc',
  { rw ← stabilizer_compl,
    rw ← compl_compl s at hs',
    exact stabilizer_ne_top' sᶜ hsc hs', },
  exact stabilizer_ne_top' s hs hsc',
end


variable [fintype α]
open_locale classical

lemma has_three_cycle_of_lt_stabilizer (s : set α)
  (G : subgroup (equiv.perm α))
  (hG : stabilizer (equiv.perm α) s ⊓ alternating_group α < G) :
  ∃ (g : equiv.perm α), g.is_three_cycle ∧ g ∈ G :=
begin
  sorry
end

lemma theorem jordan_three_cycle' (hG : is_preprimitive G α)
  {g : equiv.perm α} (h3g : equiv.perm.is_three_cycle g) (hg : g ∈ G) :
  alternating_group α ≤ G := sorry,

lemma is_maximal_stab'_temp (s : set α) (h0 : s.nonempty) (h1 : sᶜ.nonempty)
  (hα : fintype.card s < fintype.card (sᶜ : set α))
  (G : subgroup (equiv.perm α)) (hG : (stabilizer (equiv.perm α) s) ⊓ (alternating_group α) < G) :
  is_preprimitive G α → alternating_group α ≤ G :=
begin
  intro hG',
  -- intros s h0 h1 hα G hG,
  -- G : subgroup (equiv.perm α))
  -- hG : stabilizer (equiv.perm α) s ⊓ (alternating_group α) < G)
  -- We need to prove that alternating_group α ≤ ⊤
  -- G contains a three_cycle
  obtain ⟨g, hg3, hg⟩ := has_three_cycle_of_lt_stabilizer s G hG,
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply jordan_three_cycle' hG' hg3 hg,
end

lemma is_maximal_stab'_temp' (s : set α) (h0 : s.nonempty) (h1 : sᶜ.nonempty)
  (hα : fintype.card s < fintype.card (sᶜ : set α))
  (G : subgroup (equiv.perm α)) (hG : (stabilizer (equiv.perm α) s) ⊓ (alternating_group α) < G) :
  is_preprimitive G α :=
begin
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
          map_smul' := λ ⟨m, hm⟩ x, by simp only [has_smul.stabilizer_def], },
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

    /-
    have hBs_block : ∀ (B : set α), is_block G B → is_block (equiv.perm s) (coe ⁻¹' B : set s),
    { intros B hB,
      rw is_block.def_one,
      intro g,
      suffices : ∃ (k : stabilizer G s), (∀ (x : s) , g • x = k • x),
      obtain ⟨k, hk⟩ := this,
      rw is_block.def_one at hB,
      suffices hgk : g • (coe ⁻¹' B) = coe ⁻¹' (k • B), rw hgk, simp_rw hgk,
      cases hB k with hB_eq hB_dis,
      { change k • B = B at hB_eq,
        apply or.intro_left, rw hB_eq, },
      { -- change disjoint (k • B) B at hB_dis,
        apply or.intro_right,
        refine disjoint.preimage coe hB_dis, },
      -- g • (coe ⁻¹' B) = coe ⁻¹' (k • B),
      { ext,
        simp only [set.mem_preimage, set.mem_smul_set_iff_inv_smul_mem],
        suffices : ↑(g⁻¹ • x) = k⁻¹ • ↑x, rw this,
        set y := g⁻¹ • x,
        have hy : x = g • y, by rw smul_inv_smul,
        rw [eq_inv_smul_iff, hy, hk y, has_smul.stabilizer_def],
        refl, },
      -- ∃ (k : stabilizer G s), (∀ (x : s) , g • x = k • x)
      { have : g.of_subtype ∈ stabilizer (equiv.perm α) s,
        { rw mem_stabilizer_iff,
          ext x,
          split,
          { rintro ⟨y, hy, rfl⟩,
            simp only [equiv.perm.smul_def],
            rw ← subtype.coe_mk y hy,
            rw equiv.perm.of_subtype_apply_coe ,
            rw ← equiv.perm.smul_def, simp only [subtype.coe_prop] },
          { intro hx,
            let y := g⁻¹ • (⟨x, hx⟩ : s),
            use y,
            split,
            exact y.prop,
            rw [equiv.perm.smul_def, equiv.perm.of_subtype_apply_coe, ←equiv.perm.smul_def],
            rw smul_inv_smul,
            refl, } },
        use g.of_subtype,
        { apply le_of_lt hG, exact this, },
        { rw mem_stabilizer_iff,
          change g.of_subtype • s = s,
          rw ← mem_stabilizer_iff,
          exact this, },
        { intro x,
          rw ← subtype.coe_inj,
          rw has_smul.stabilizer_def,
          simp only [equiv.perm.smul_def, subgroup.coe_mk],
          change _ = g.of_subtype • ↑x,
          rw equiv.perm.smul_def,
          rw equiv.perm.of_subtype_apply_coe }, }, }, -/

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
      map_smul' := λ ⟨m, hm⟩ x, by simp only [has_smul.stabilizer_def], },
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
            exact fixing_subgroup_le_stabilizer s hk, } },
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
          rw enat.of_fintype α,
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

theorem is_maximal_stab' (s : set α) (h0 : s.nonempty) (h1 : sᶜ.nonempty)
  (hα : fintype.card s < fintype.card (sᶜ : set α)) :
  subgroup.is_maximal (stabilizer (alternating_group α) s) :=
begin
  have h1' : sᶜ.nontrivial,
  { rw [← set.nontrivial_coe, ← fintype.one_lt_card_iff_nontrivial],
    apply lt_of_le_of_lt _ hα,
    rw [nat.succ_le_iff, fintype.card_pos_iff, set.nonempty_coe_sort],
    exact h0, },
  split, split,
  -- stabilizer (alternating_group α) s ≠ ⊤
  exact stabilizer_ne_top' s h0 h1',
  -- ∀ (G : subgroup (alternating_group α)), stabilizer (alternating_group α) s < b) → b = ⊤
  { intros G' hG',
    suffices : alternating_group α ≤ G'.map (alternating_group α).subtype,
    { rw eq_top_iff, intros g hg,
      obtain ⟨g', hg', hgg'⟩ := this g.prop,
      simp only [subgroup.coe_subtype, set_like.coe_eq_coe] at hgg',
      rw ← hgg', exact hg', },
    apply is_maximal_stab'_temp s h0 h1 hα,
    rw [← subgroup.subgroup_of_map_subtype, ← (subgroup.map_strict_mono_of_injective _)],
    rw mul_action.stabilizer_subgroup_of_eq at hG',
    exact hG',
    simp only [subgroup.coe_subtype, subtype.coe_injective], },
end

/-- stabilizer (equiv.perm α) s is a maximal subgroup of equiv.perm α,
provided s ≠ ⊥, s ≠ ⊤ and fintype.card α ≠ 2 * fintype.card ↥s) -/
theorem equiv.perm.is_maximal_stab (s : set α) (h0 : s.nonempty) (h1 : sᶜ.nonempty)
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

/-- The action of equiv.perm α on the n-element subsets of α is preprimitive
provided 1 ≤ n < #α and #α ≠ 2*n -/
theorem nat.finset_is_preprimitive_of (n : ℕ) (h_one_le : 1 ≤ n) (hn : n < fintype.card α)
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
  haveI ht : is_pretransitive (equiv.perm α) (n.finset α) := nat.finset_is_pretransitive,
  haveI : nontrivial (n.finset α) :=
    nat.finset_nontrivial (lt_trans (nat.lt_succ_self 0) h_one_lt) hn,
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

open_locale classical

def Iw_t (s : finset α) : (equiv.perm s) →* (equiv.perm α) := equiv.perm.of_subtype
def Iw_T(s : finset α) := (Iw_t s).range

lemma IwT_is_conj (s : finset α) (g : equiv.perm α) :
  Iw_T (g • s) = mul_aut.conj g • (Iw_T s) :=
begin
  unfold Iw_T,
  let ts := Iw_t s, let tgs := Iw_t (g • s),
  let Ts := Iw_T s, let Tgs := Iw_T (g • s),
  let kg : ↥s ≃ ↥(g • s) := equiv.subtype_equiv g (
    begin
      intro a,
      rw ← equiv.perm.smul_def,
      rw finset.smul_mem_smul_finset_iff,
    end),

  have this1 :
    (mul_aut.conj g) • (Iw_t s).range = ((mul_aut.conj g).to_monoid_hom.comp (Iw_t s)).range,
    simp only [←  monoid_hom.map_range], refl,
  rw this1,

  suffices this2 : tgs.range = ((mul_aut.conj g).to_monoid_hom.comp ts).range,
  rw this2,

  let pg : equiv.perm (↥s) → equiv.perm ↥(g • s) := λ k, (kg.symm.trans k).trans kg,
  let pg' : equiv.perm ↥(g • s) → equiv.perm ↥s := λ k, (kg.trans k).trans kg.symm,
  have hpgg' : ∀ k, k = pg (pg' k) ,
  { intro k,
    change k = (kg.symm.trans ((kg.trans k).trans kg.symm)).trans kg,
    simp only [← equiv.trans_assoc, equiv.symm_trans_self, equiv.refl_trans],
    rw [equiv.trans_assoc, equiv.symm_trans_self, equiv.trans_refl], },
/-   have hpg'g : ∀ k, k = pg' (pg k) ,
  { intro k,
    change k = (kg.trans ((kg.symm.trans k).trans kg)).trans kg.symm,
    simp only [← equiv.trans_assoc, equiv.self_trans_symm, equiv.refl_trans],
    rw [equiv.trans_assoc, equiv.self_trans_symm, equiv.trans_refl], }, -/


  suffices this3 : ∀(k : equiv.perm ↥s), ((mul_aut.conj g).to_monoid_hom.comp ts) k  = tgs (pg k),

  ext,
  split,
  rintro ⟨k,rfl⟩, use pg' k, conv_rhs {rw hpgg' k}, rw this3,
  rintro ⟨k, rfl⟩, use pg k, rw this3,

  intro k,
  ext x,
  cases em (x ∈ g • s) with hx hx',
  { -- x ∈ g • s
    dsimp [tgs, Iw_T, Iw_t], rw equiv.perm.of_subtype_apply_of_mem,
    dsimp [pg],
    simp only [embedding_like.apply_eq_iff_eq],
    dsimp [ts, Iw_T, Iw_t], rw equiv.perm.of_subtype_apply_of_mem,
    apply congr_arg, apply congr_arg,
    rw ← subtype.coe_inj, simp only [subtype.coe_mk],
    refl,

    { rw [← equiv.perm.smul_def, finset.inv_smul_mem_iff],
      exact hx, },
    exact hx, },
  { -- x ∉ g • s
    dsimp [tgs, Iw_T, Iw_t], rw equiv.perm.of_subtype_apply_of_not_mem,
    dsimp [ts, Iw_T, Iw_t], rw equiv.perm.of_subtype_apply_of_not_mem,
    simp only [equiv.perm.apply_inv_self],
    { intro hx, apply hx',
      rw [← finset.inv_smul_mem_iff], exact hx,  },
    exact hx', },
end


def Iw2 : iwasawa_structure (equiv.perm α) (nat.finset α 2) :=
{ T := λ s, Iw_T ↑s,
  is_comm := λ s,
  begin
    apply monoid_hom.range_is_commutative,
    rw ← equiv.perm.is_commutative_iff,
    apply le_of_eq,
    simp only [coe_sort_coe_base, fintype.card_coe],
    exact s.prop,
  end,
  is_conj := λ g s, IwT_is_conj ↑s g,
  is_generator :=
  begin
    rw eq_top_iff,
    rw ← equiv.perm.closure_is_swap,
    rw subgroup.closure_le,
    intros g hg,
    simp only [set.mem_set_of_eq] at hg,
    obtain ⟨a,b, hab, rfl⟩ := hg,
    let s : nat.finset α 2 := ⟨{a,b}, finset.card_doubleton hab⟩,
    apply subgroup.mem_supr_of_mem s,
    dsimp [Iw_T, Iw_t],
    let a' : ↥s := ⟨a,
    begin
      change a ∈ ↑s, dsimp [s],
      exact finset.mem_insert_self a {b},
    end⟩,
    let b' : ↥s := ⟨b,
    begin
      change b ∈ ↑s, dsimp [s],
      apply finset.mem_insert_of_mem ,
      rw finset.mem_singleton,
    end⟩,

    use equiv.swap a' b',
    ext,
    have : x ∈ {a, b}  ↔ (x = a ∨ x = b), by rw [finset.mem_insert, finset.mem_singleton],
    cases em (x ∈ {a, b}) with hx hx,
    { rw equiv.perm.of_subtype_apply_of_mem (equiv.swap a' b') hx,
      cases this.mp hx with ha hb,
      { conv_rhs {rw ha},
        have ha' : a' = ⟨x, hx⟩, rw ← subtype.coe_inj, change a = x, exact ha.symm,
        rw ha',
        simp only [equiv.swap_apply_left], refl, },
      { conv_rhs {rw hb},
        have hb' : b' = ⟨x, hx⟩, rw ← subtype.coe_inj, change b = x, exact hb.symm,
        rw hb',
        simp only [equiv.swap_apply_right], refl, },
    },
    { rw equiv.perm.of_subtype_apply_of_not_mem (equiv.swap a' b') hx,
      rw equiv.swap_apply_of_ne_of_ne,
      { intro ha, apply hx, rw this, apply or.intro_left, exact ha, },
      { intro hb, apply hx, rw this, apply or.intro_right, exact hb, }, },
  end
}


lemma finset.mem_doubleton_iff (a b x : α) : x ∈ ({a, b} : finset α) ↔ (x = a ∨ x = b) :=
begin
  rw [finset.mem_insert, finset.mem_singleton],
end


-- The main theorem, unfortunately weaker than expected
/-- If α has at least 5 elements, then
the only nontrivial normal sugroup of (perm α) is the alternating_group. -/
theorem equiv.perm.normal_subgroups {α : Type*} [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α)
  {N : subgroup (equiv.perm α)} (hnN : N.normal) (ntN : nontrivial N) : alternating_group α  ≤ N :=
begin
  rw ←  alternating_group.commutator_group_eq hα,

  have hprim : is_preprimitive (equiv.perm α) (nat.finset α 2),
  { apply nat.finset_is_preprimitive_of,
    norm_num,
    apply lt_of_lt_of_le _ hα, norm_num,
    apply ne_of_gt,
    apply lt_of_lt_of_le _ hα, norm_num,  },
  apply commutator_le_iwasawa hprim Iw2 hnN ,

  -- N acts nontrivially
  intro h,
  obtain ⟨g, hgN, hg_ne⟩ := N.nontrivial_iff_exists_ne_one.mp ntN,
  obtain ⟨s, hs⟩ := nat.finset.mul_action_faithful α 2 _ _ g hg_ne,
  apply hs,
  suffices : s ∈ fixed_points N (nat.finset α 2),
  rw mem_fixed_points at this, exact this ⟨g, hgN⟩,
  rw h, rw set.top_eq_univ, apply set.mem_univ,
  norm_num,
  apply lt_of_lt_of_le _ hα, norm_num,
end
