/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/


-- import tactic.basic tactic.group
-- import group_theory.solvable
import group_theory.group_action.sub_mul_action
import group_theory.specific_groups.alternating
-- import group_theory.perm.cycle.concrete

import .for_mathlib.alternating
import .index_normal

-- import .for_mathlib.group_theory__subgroup__basic

import .primitive
import .multiple_transitivity
import .stabilizer_primitive
import .perm_iwasawa
import .perm_maximal

import .V4

open_locale pointwise
-- open_locale classical

open mul_action

section junk

variables {α G H : Type*} [group G] [group H] [mul_action G α] {N : subgroup G}

lemma subgroup.map_subgroup_of_eq {K : subgroup N} : (K.map N.subtype).subgroup_of N = K :=
by rw [← subgroup.comap_subtype, subgroup.comap_map_eq , subgroup.ker_subtype, sup_bot_eq]

lemma mul_action.stabilizer_subgroup_of_eq {a : α} :
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

open_locale classical

lemma is_pretransitive_of_fixing_subgroup (s : set α) (h0 : s.nontrivial)
  (hα : fintype.card s < fintype.card (sᶜ : set α))  :
  is_pretransitive (fixing_subgroup (alternating_group α) s)
    (sub_mul_action.of_fixing_subgroup (alternating_group α) s) :=
begin
  rw is_pretransitive_iff_is_one_pretransitive,
  refine remaining_transitivity' _ _ _ _ (fintype.card α - 2) _ _ _,
  simp only [part_enat.of_fintype α, part_enat.coe_le_coe, tsub_le_self],
  { have  h1' : 2 < fintype.card (sᶜ : set α),
    { apply lt_of_le_of_lt _ hα,
      rw [nat.succ_le_iff, fintype.one_lt_card_iff_nontrivial, set.nontrivial_coe_sort],
      exact h0, },
    rw [add_comm,← fintype.card_add_compl s, nat.add_sub_assoc (le_of_lt h1'), add_le_add_iff_left,
      nat.le_sub_iff_right (le_of_lt h1')],
    exact h1', },
  -- Here, we needed to add an instance in multiple_transitivity.lean to apply the following lemma
  exact mul_action.alternating_group_is_fully_minus_two_pretransitive α,
end


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

-- open_locale classical

example (s t : set α) (h : s ⊆ t) : fintype.card s ≤ fintype.card t :=
begin
exact set.card_le_of_subset h
end

example (s : finset α) : fintype.card (s : set α) = s.card :=
begin
  simp only [finset.coe_sort_coe, fintype.card_coe],
end


-- Il va falloir, soit que t ait ≥ 3 éléments, soit que tᶜ en ait ≥ 2.
-- autrement dit : fintype.card α ≥ 4.
-- La condition est nécessaire :
-- dans le cas α = {1, 2, 3}, t = {1,2} ou t = {1}, le résultat est faux
lemma moves_in (hα : 4 ≤ fintype.card α) (t : set α) :
  ∀ (a ∈ t) (b ∈ t), ∃ (g ∈ stabilizer (equiv.perm α) t ⊓ alternating_group α), g • a = b :=
begin
  intros a ha b hb,
  cases em (a = b) with hab hab,
  { -- a = b, on prend g = 1,
    use 1,
    simp only [hab, subgroup.one_mem, one_smul, eq_self_iff_true, and_self], },
  rw ← ne.def at hab,
  cases le_or_gt (fintype.card t) 2 with ht ht',
  { -- fintype.card t ≤ 2, alors on prend le produit d'un swap (a b) avec un swap dans tᶜ
    have h : 1 < fintype.card (tᶜ : set α),
    { by_contradiction,
      rw not_lt at h,
      rw [← not_lt] at hα,
      apply hα,
      rw ← fintype.card_add_compl t,
      apply nat.lt_succ_of_le,
      apply add_le_add ht h, } ,
    rw fintype.one_lt_card_iff at h,
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩, hcd⟩ := h,
    simp only [ne.def, subtype.mk_eq_mk] at hcd,
    use equiv.swap a b * equiv.swap c d,
    split,
    { simp only [subgroup.mem_inf],
      split,
      { rw mem_stabilizer_of_finite_iff,
        rintros _ ⟨x, hx, rfl⟩,
        simp only [equiv.perm.smul_def, equiv.perm.coe_mul, function.comp_app],
        have hx_ne : ∀ (u ∈ tᶜ), x ≠ u := λ u hu h,
          set.mem_compl hu (begin rw ← h, exact hx, end),
        rw equiv.swap_apply_of_ne_of_ne (hx_ne c hc) (hx_ne d hd),
        cases em (x = a) with hxa hxa',
        { rw [hxa, equiv.swap_apply_left], exact hb, },
        cases em (x = b) with hxb hxb',
        { rw [hxb, equiv.swap_apply_right], exact ha, },
        rw equiv.swap_apply_of_ne_of_ne hxa' hxb', exact hx, },
      { simp only [equiv.perm.mem_alternating_group, equiv.perm.sign_mul],
        rw equiv.perm.sign_swap hab, rw equiv.perm.sign_swap hcd,
        simp only [int.units_mul_self], }, },
    simp only [equiv.perm.smul_def, equiv.perm.coe_mul, function.comp_app],
    rw set.mem_compl_iff t at hc hd,
    have hac : a ≠ c, intro h, apply hc, rw ← h, exact ha,
    have had : a ≠ d, intro h, apply hd, rw ← h, exact ha,
    rw equiv.swap_apply_of_ne_of_ne hac had,
    rw equiv.swap_apply_left, },
  { -- fintype t ≥ 3, alors on prend un 3-cycle dans t
    suffices : ∃ c ∈ t, c ≠ a ∧ c ≠ b,
    obtain ⟨c, hc, hca, hcb⟩ := this,
    use equiv.swap a c * equiv.swap a b,
    split,
    { simp only [subgroup.mem_inf],
      split,
      { rw mem_stabilizer_of_finite_iff,
        rintros _ ⟨x, hx, rfl⟩,
        simp only [equiv.perm.smul_def, equiv.perm.coe_mul, function.comp_app],
        cases em (x = a) with hxa hxa',
        { rw [hxa, equiv.swap_apply_left],
          rw equiv.swap_apply_of_ne_of_ne hab.symm hcb.symm,
          exact hb, },
        rw ← ne.def at hxa',
        cases em (x = b) with hxb hxb',
        { rw [hxb, equiv.swap_apply_right, equiv.swap_apply_left], exact hc,},
        rw ← ne.def at hxb',
        rw equiv.swap_apply_of_ne_of_ne hxa' hxb',
        cases em (x = c) with hxc hxc',
        { rw [hxc, equiv.swap_apply_right], exact ha, },
        rw ← ne.def at hxc',
        rw equiv.swap_apply_of_ne_of_ne hxa' hxc',
        exact hx, },
      { simp only [equiv.perm.mem_alternating_group, equiv.perm.sign_mul],
        rw equiv.perm.sign_swap hab, rw equiv.perm.sign_swap (ne.symm hca),
        simp only [int.units_mul_self], }, },
    { simp only [equiv.perm.smul_def, equiv.perm.coe_mul, function.comp_app],
      rw equiv.swap_apply_left,
      rw equiv.swap_apply_of_ne_of_ne (ne.symm hab) (ne.symm hcb), },
    suffices : (t \ {a, b}).nonempty,
    { obtain ⟨c, h⟩ := this,
      simp only [set.mem_diff, set.mem_insert_iff, set.mem_singleton_iff, not_or_distrib] at h,
      use c,
      apply and.intro h.left,
      exact h.right, },
    rw set.nonempty_diff,
    intro ht,
    rw [gt_iff_lt, ← not_le] at ht', apply ht',
    rw ← finset.card_doubleton hab,
    simp only [← fintype.card_coe, ← finset.coe_sort_coe],
    apply set.card_le_of_subset,
    simp only [finset.coe_insert, finset.coe_singleton],
    exact ht },
end

lemma moves_in' (hα : 4 ≤ fintype.card α) (G : subgroup (equiv.perm α)) (t : set α)
  (hGt : stabilizer (equiv.perm α) t ⊓ (alternating_group α) ≤ G) :
  ∀ (a ∈ t) (b ∈ t), ∃ (g : G), g • a = b :=
begin
  intros a ha b hb,
  obtain ⟨g, hg, H⟩ := moves_in hα t a ha b hb,
  use g, apply hGt,  exact hg, exact H,
end


lemma has_three_cycle_of_stabilizer' (s : set α) (hs : 2 < fintype.card s) :
 -- (G : subgroup (equiv.perm α)) :
 --  (hG : stabilizer (equiv.perm α) s ⊓ alternating_group α < G) :
  ∃ (g : equiv.perm α), g.is_three_cycle ∧ g ∈ stabilizer (equiv.perm α) s :=
begin
  rw fintype.two_lt_card_iff at hs,
  obtain ⟨⟨a, ha⟩,⟨b,hb⟩, ⟨c, hc⟩, hab, hac, hbc⟩ := hs,
  rw [ne.def, subtype.mk_eq_mk, ← ne.def] at hab hac hbc,
  use (equiv.swap a b) * (equiv.swap a c),
  split,
  apply equiv.perm.is_three_cycle_swap_mul_swap_same hab hac hbc,
  rw ← stabilizer_compl,
  rw mem_stabilizer_of_finite_iff,
  rintros _ ⟨x, hx, rfl⟩,
  simp only [equiv.perm.smul_def, equiv.perm.coe_mul, function.comp_app],
  rw set.mem_compl_iff at hx,
  suffices h : ∀ (u ∈ s), x ≠ u,
  { rw equiv.swap_apply_of_ne_of_ne (h a ha) (h c hc),
    rw equiv.swap_apply_of_ne_of_ne (h a ha) (h b hb),
    exact hx, },
  { intros u hu h, apply hx, rw h, exact hu, },
end

lemma has_three_cycle_of_stabilizer [decidable_eq α] (s : set α) (hα : 4 < fintype.card α) :
  ∃ (g : equiv.perm α), g.is_three_cycle ∧ g ∈ stabilizer (equiv.perm α) s :=
begin
  cases nat.lt_or_ge 2 (fintype.card s) with hs hs,
  exact has_three_cycle_of_stabilizer' s hs,
  obtain ⟨g, hg, hg'⟩ := has_three_cycle_of_stabilizer' sᶜ _,
  { use g, rw stabilizer_compl at hg', exact ⟨hg, hg'⟩, },
  { rw lt_iff_not_le at hα ⊢,
    intro hs', apply hα,
    rw ← fintype.card_add_compl s,
    suffices : 2 + 2 ≤ 4,
    { apply le_trans _ this,
      apply nat.add_le_add, exact hs,
      apply le_trans _ hs', apply le_of_eq,
      simp only [fintype.card_of_finset, set.mem_compl_iff], },
    norm_num, },
end

lemma le_of_is_preprimitive (s : set α) (hα : 4 < fintype.card α)
 -- (h0 : s.nonempty) (h1 : sᶜ.nonempty)
 -- (hs : fintype.card s < fintype.card (sᶜ : set α))
  (G : subgroup (equiv.perm α)) (hG : (stabilizer (equiv.perm α) s) ⊓ (alternating_group α) ≤ G) :
  is_preprimitive G α → alternating_group α ≤ G :=
begin
  intro hG',
  -- intros s h0 h1 hα G hG,
  -- G : subgroup (equiv.perm α))
  -- hG : stabilizer (equiv.perm α) s ⊓ (alternating_group α) < G)
  -- We need to prove that alternating_group α ≤ ⊤
  -- G contains a three_cycle
  obtain ⟨g, hg3, hg⟩ := has_three_cycle_of_stabilizer s hα,
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply jordan_three_cycle hG' hg3,
  { apply hG,
    simp only [subgroup.mem_inf, hg, true_and],
    exact equiv.perm.is_three_cycle.mem_alternating_group hg3, },
end

/- lemma stabilizer.is_preprimitive (s : set α) (hs : (sᶜ : set α).nontrivial):
  is_preprimitive (stabilizer (alternating_group α) s) s :=
begin
  let φ : stabilizer (alternating_group α) s → equiv.perm s := mul_action.to_perm,
  let f : s →ₑ[φ] s := {
  to_fun := id,
  map_smul' := λ ⟨g, hg⟩ ⟨x, hx⟩, by simp only [id.def, equiv.perm.smul_def, to_perm_apply], },
  have hf : function.bijective f := function.bijective_id,
  rw is_preprimitive_of_bijective_map_iff _ hf,
  exact equiv.perm.is_preprimitive s,

  -- function.surjective φ
  suffices : ∃ k : equiv.perm (sᶜ : set α), equiv.perm.sign k = -1,
  obtain ⟨k, hk_sign⟩ := this,
  have hks : (equiv.perm.of_subtype k) • s = s,
  { rw ← mem_stabilizer_iff,
    apply equiv.perm.of_subtype_mem_stabilizer', },

  -- function.surjective φ
  { intro g,
    have hgs : (equiv.perm.of_subtype g) • s = s,
    apply equiv.perm.of_subtype_mem_stabilizer,

    have hminus_one_ne_one : (-1 : units ℤ) ≠ 1,
    { intro h, rw [← units.eq_iff, units.coe_one, units.coe_neg_one] at h, norm_num at h, },

    let g' := ite (equiv.perm.sign g = 1)
      (equiv.perm.of_subtype g)
      (equiv.perm.of_subtype g * (equiv.perm.of_subtype k)),

    use g',

    rw equiv.perm.mem_alternating_group,
    cases int.units_eq_one_or (equiv.perm.sign g) with hsg hsg;
    { dsimp [g'], -- rw hsg,
      simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false,
        equiv.perm.sign_of_subtype,
        equiv.perm.sign_mul, mul_neg, mul_one, neg_neg, hsg, hk_sign], },

    rw mem_stabilizer_iff,
    change (ite (equiv.perm.sign g = 1)
      (equiv.perm.of_subtype g)
      (equiv.perm.of_subtype g * (equiv.perm.of_subtype k))) • s = s,
    cases int.units_eq_one_or (equiv.perm.sign g) with hsg hsg,
    { simp only [hsg,  eq_self_iff_true, if_true],
      exact hgs, },
    { simp only [hsg, hminus_one_ne_one, if_false],
      rw mul_smul, rw hks, exact hgs, },

    dsimp [φ],
    cases int.units_eq_one_or (equiv.perm.sign g) with hsg hsg,
    { dsimp [g'], simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false],
      ext,
      simp only [to_perm_apply, has_smul.smul_stabilizer_def, subtype.coe_mk],
      change equiv.perm.of_subtype g ↑x = ↑(g x),
      exact equiv.perm.of_subtype_apply_coe g x, },
    { dsimp [g'], simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false],
      ext,
      simp only [to_perm_apply, has_smul.smul_stabilizer_def, subtype.coe_mk],
      change ((equiv.perm.of_subtype g) * (equiv.perm.of_subtype k)) ↑x = ↑(g x),
      rw equiv.perm.mul_apply ,
      rw equiv.perm.of_subtype_apply_of_not_mem k _,
      exact equiv.perm.of_subtype_apply_coe g x,
      rw set.not_mem_compl_iff, exact x.prop, }, },

  -- ∃ k : equiv.perm (sᶜ : set α), equiv.perm.sign k = -1,
  obtain ⟨a, ha, b, hb, hab⟩ := hs,
  use equiv.swap ⟨a, ha⟩ ⟨b, hb⟩,
  rw equiv.perm.sign_swap _,
  rw ← function.injective.ne_iff (subtype.coe_injective),
  simp only [subtype.coe_mk], exact hab,
end

example (s t : set α) (a : α) (ha : a ∈ s ⊓ t) : a ∈ s :=
begin
  apply @inf_le_left _ _ s t,  exact ha,
end
-/
/-
lemma stabilizer.is_preprimitive' (s : set α) (hsc : sᶜ.nontrivial)
  (G : subgroup (equiv.perm α)) (hG : stabilizer (equiv.perm α) s ⊓ alternating_group α ≤ G) :
  is_preprimitive (stabilizer G s) s :=
begin
  let φ : stabilizer (alternating_group α) s → stabilizer G s := λ g,
  begin
    use (g : alternating_group α), apply hG, rw subgroup.mem_inf,
    split,
    { let h := g.prop, rw mem_stabilizer_iff at h ⊢, exact h, },
    { exact set_like.coe_mem ↑g, },
    { rw mem_stabilizer_iff, let h := g.prop, rw mem_stabilizer_iff at h, exact h, },
  end,
  let f : s →ₑ[φ] s := {
    to_fun := id,
    map_smul' := λ ⟨⟨m, hm'⟩, hm⟩ ⟨a, ha⟩, rfl, },
  have hf : function.surjective f := function.surjective_id,
  apply is_preprimitive_of_surjective_map hf,
  apply stabilizer.is_preprimitive,
  exact hsc,
end

-/

lemma is_preprimitive_of_stabilizer_lt (s : set α) (h0 : s.nontrivial) (h1 : sᶜ.nontrivial)
  (hα : fintype.card s < fintype.card (sᶜ : set α)) (h4 : 4 ≤ fintype.card α)
  (G : subgroup (equiv.perm α))
  (hG : (stabilizer (equiv.perm α) s) ⊓ (alternating_group α) < G ⊓ (alternating_group α)) :
  is_preprimitive G α :=
begin
  -- G acts transitively
  haveI : is_pretransitive G α,
  { have hG' : stabilizer (equiv.perm α) s ⊓ alternating_group α ≤ G :=
    le_trans (le_of_lt hG) (inf_le_left),
    apply equiv.perm.is_pretransitive.of_partition G s,
    { intros a ha b hb,
      obtain ⟨g, hg, H⟩ := alternating_group.moves_in h4 s a ha b hb,
      use g,
      apply hG',
      exact hg,
      exact H, },
    { intros a ha b hb,
      obtain ⟨g, hg, H⟩ := alternating_group.moves_in h4 sᶜ a ha b hb,
      use g,
      apply hG',
      rw stabilizer_compl at hg, exact hg,
      exact H, },
    { intro h,
      apply (lt_iff_le_not_le.mp hG).right,
      --  G ⊓ alternating_group α ≤ stabilizer (equiv.perm α) s ⊓ alternating_group α,
      rw le_inf_iff,
      split,
      { intro g, rw subgroup.mem_inf, rintro ⟨hg, hg'⟩,
        rw mem_stabilizer_iff,
        rw ← subgroup.coe_mk G g hg,
        change (⟨g, hg⟩ : ↥G) • s = s,
        rw ← mem_stabilizer_iff,
        change _ ∈ stabilizer ↥G s,
        rw h, exact subgroup.mem_top ⟨g, hg⟩, },
      { exact inf_le_right, }, }, },

  apply is_preprimitive.mk,

  /- The proof needs 4 steps -/
  /- Step 1 : No block is equal to sᶜ
     This uses that fintype.card s < fintype.card sᶜ.
     In the equality case, fintype.card s = fintype.card sᶜ, it is possible that B = sᶜ,
     then G is the wreath product,
     this is case (b) of the O'Nan-Scott classification of max'l subgroups of the symmetric group -/
  have hB_ne_sc : ∀ (B : set α) (hB : is_block G B), ¬(B = sᶜ),
  { intros B hB hBsc,
    obtain ⟨b, hb⟩ := h1.nonempty, rw ← hBsc at hb,
    obtain ⟨a, ha⟩ := h0.nonempty,
    obtain ⟨k, hk⟩ := exists_smul_eq G b a,
    suffices : fintype.card (B : set α) ≤ fintype.card s,
    { apply nat.lt_irrefl (fintype.card B),
      apply lt_of_le_of_lt this,
      simp_rw hBsc, exact hα, },
    rw ← smul_set_card_eq k B,
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
        map_smul' := λ m x, by simp only [φ', has_smul.smul_stabilizer_def], },
      apply mul_action.is_block_preimage f' hB,

      apply stabilizer.is_preprimitive',
      rw ← stabilizer_compl at hG,
      rw compl_compl, exact h0,
      rw stabilizer_compl,
      apply le_trans (le_of_lt hG),
      exact inf_le_left, },

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
      intros g' hg',
      rw subgroup.mem_inf at hg' ⊢,

      rw mem_stabilizer_iff, apply and.intro (h g' hg'.left),
      exact hg'.right, },
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

    { -- is_trivial_block (coe ⁻¹' B : set s),
      suffices : is_preprimitive (stabilizer G s) (s : set α),
      refine is_preprimitive.has_trivial_blocks this _,

      -- is_block (coe ⁻¹' B : set s)
      let φ' : stabilizer G s → G := coe,
      let f' : s →ₑ[φ'] α := {
        to_fun := coe,
      map_smul' := λ ⟨m, hm⟩ x, by simp only [φ', has_smul.smul_stabilizer_def], },
      apply mul_action.is_block_preimage f' hB,

      apply stabilizer.is_preprimitive' s h1,
      apply le_trans (le_of_lt hG), exact inf_le_left, },

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
  {  intros x hx',
    suffices : ∃ (k : fixing_subgroup (alternating_group α) s), k • b = x,
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
        apply le_trans (le_of_lt hG), exact inf_le_left,

        rw subgroup.mem_inf, split,

      suffices hk' : k ∈ stabilizer (alternating_group α) s,
      { simpa [mem_stabilizer_iff] using hk', },
      apply mul_action.fixing_subgroup_le_stabilizer, exact hk,
      exact k.prop, }, },
    { -- ∃ (k : fixing_subgroup (alternating_group α) s), k • b = x,
      haveI : is_pretransitive (fixing_subgroup (alternating_group α) s)
        (sub_mul_action.of_fixing_subgroup (alternating_group α) s) :=
        is_pretransitive_of_fixing_subgroup s h0 hα,
      obtain ⟨k, hk⟩ := exists_smul_eq (fixing_subgroup (alternating_group α) s)
        (⟨b, hb'⟩ : sub_mul_action.of_fixing_subgroup (alternating_group α) s)
        ⟨x, hx'⟩,
      use k,
      rw [← subtype.coe_inj, sub_mul_action.coe_smul] at hk,
      exact hk,
      }, },

  -- Conclusion of the proof : B = ⊤
  rw eq_top_iff,
  intros x _,
  obtain ⟨b, hb⟩ := h1.nonempty,
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

theorem is_maximal_stab' -- (hα : 4 < fintype.card α)
  (s : set α) (h0' : s.nontrivial) (h1' : sᶜ.nontrivial)
  (hs : fintype.card s < fintype.card (sᶜ : set α)) :
  subgroup.is_maximal (stabilizer (alternating_group α) s) :=
begin
  suffices hα : 4 < fintype.card α,
-- h0 : s.nonempty, h1  : sᶜ.nonempty
/-   have h1' : sᶜ.nontrivial,
  { rw [← set.nontrivial_coe, ← fintype.one_lt_card_iff_nontrivial],
    apply lt_of_le_of_lt _ hs,
    rw [nat.succ_le_iff, fintype.card_pos_iff, set.nonempty_coe_sort],
    exact h0, },
 -/
 --  cases em(s.nontrivial) with h0' h0',
  -- We start with the case where s.nontrivial
  split, split,
  -- stabilizer (alternating_group α) s ≠ ⊤
  exact stabilizer_ne_top' s h0'.nonempty h1',
  -- ∀ (G : subgroup (alternating_group α)), stabilizer (alternating_group α) s < b) → b = ⊤
  { intros G' hG',
    suffices : alternating_group α ≤ G'.map (alternating_group α).subtype,
    { rw eq_top_iff, intros g hg,
      obtain ⟨g', hg', hgg'⟩ := this g.prop,
      simp only [subgroup.coe_subtype, set_like.coe_eq_coe] at hgg',
      rw ← hgg', exact hg', },

    --   apply is_maximal_stab'_temp' s hα,
    apply le_of_is_preprimitive s hα,

    rw [← subgroup.subgroup_of_map_subtype, subgroup.map_subtype_le_map_subtype],
    rw mul_action.stabilizer_subgroup_of_eq at hG',
    exact le_of_lt hG',

    apply is_preprimitive_of_stabilizer_lt s h0' h1' hs (le_of_lt hα),
    rw lt_iff_le_not_le,
    split,
    { intro g,
      simp only [subgroup.mem_inf],
      rintro ⟨hg, hg'⟩,
      refine and.intro _ hg',
      simp only [subgroup.mem_map, subgroup.coe_subtype, exists_prop],
      use ⟨g, hg'⟩,
      split,
      { apply le_of_lt hG',
        simpa only [mem_stabilizer_iff] using hg, },
      refl,  },
    { intro h,
      rw lt_iff_le_not_le at hG', apply hG'.right,
      intros g' hg',
      rw mem_stabilizer_iff,
      change (g' : equiv.perm α) • s = s, rw ← mem_stabilizer_iff,
      apply @inf_le_left (subgroup (equiv.perm α)) _ , apply h,
      rw subgroup.mem_inf,
      apply and.intro _ g'.prop,
      simp only [subgroup.mem_map,
        subgroup.coe_subtype, set_like.coe_eq_coe, exists_prop, exists_eq_right],
      exact hg', }, },

    -- hα : 4 < fintype.card α
    have h0 : 2 ≤ fintype.card s,
    rw [nat.succ_le_iff, fintype.one_lt_card_iff_nontrivial, set.nontrivial_coe_sort],
    exact h0',
    change 2 + 2 < _,
    rw ← fintype.card_add_compl s,
    apply lt_of_le_of_lt,
    exact nat.add_le_add_right h0 2,
    apply nat.add_lt_add_left,
    exact lt_of_le_of_lt h0 hs,
end


lemma three_le {c n : ℕ} (h : 1 ≤ n) (h' : n < c) (hh' : c ≠ 2 * n) : 3 ≤ c :=
begin
  cases nat.eq_or_lt_of_le h with h h,
  { rw ← h at h' hh',
    cases nat.eq_or_lt_of_le h' with h' h',
    { exfalso, apply hh' h'.symm, },
    exact h',  },
  rw nat.succ_le_iff,
  exact lt_of_le_of_lt h h',
end

/-- stabilizer (alternating_group α) s is a maximal subgroup of alternating_group α,
provided s ≠ ⊥, s ≠ ⊤ and fintype.card α ≠ 2 * fintype.card ↥s) -/
theorem stabilizer.is_maximal (s : set α) (h0 : s.nonempty) (h1 : sᶜ.nonempty)
  (hs : fintype.card α ≠ 2 * fintype.card ↥s) :
  subgroup.is_maximal (stabilizer (alternating_group α) s) :=
begin
  have hα : 3 ≤ fintype.card α,
  { rw [← set.nonempty_coe_sort, ← fintype.card_pos_iff, ← nat.succ_le_iff] at h0 h1,
    refine three_le h0 _ hs,
    rw [← tsub_pos_iff_lt,  ←  fintype.card_compl_set], exact h1, },
  haveI : nontrivial α,
  { rw ← fintype.one_lt_card_iff_nontrivial, apply lt_of_lt_of_le _ hα, norm_num, },

  have h : ∀ (t : set α) (h0 : t.nonempty) (h0': t.subsingleton),
    (stabilizer (alternating_group α) t).is_maximal,
  { intros t ht ht',
    suffices : ∃ (a : α), t = ({a} : set α),
    obtain ⟨a, rfl⟩ := this,
    have : stabilizer (alternating_group α) ({a} : set α) = stabilizer (alternating_group α) a,
    { ext g, simp only [mem_stabilizer_iff, set.smul_set_singleton, set.singleton_eq_singleton_iff], },
    rw this,
    apply has_maximal_stabilizers_of_preprimitive,
    apply alternating_group.is_preprimitive hα,
    { obtain ⟨a, ha⟩ := ht,
      use a, exact set.subsingleton.eq_singleton_of_mem ht' ha, }, },

  cases em (s.nontrivial) with h0' h0',
  cases em (sᶜ.nontrivial) with h1' h1',
  -- h0' : s.nontrivial, h1' : sᶜ.nontrivial
  cases nat.lt_trichotomy (fintype.card s) (fintype.card (sᶜ : set α)) with hs' hs',
  { exact is_maximal_stab' s h0' h1' hs', },
  cases hs' with hs' hs',
  { exfalso, apply hs,
    rw [← fintype.card_add_compl s, ← hs', ← two_mul], },
  { rw ← compl_compl s at h0',
    rw ← stabilizer_compl,
    apply is_maximal_stab' sᶜ h1' h0',
    simp_rw compl_compl s,
    convert hs', },
  -- h0' : s.nontrivial, h1' : ¬(s.nontrivial)
  { simp only [set.not_nontrivial_iff] at h1',
    rw ← stabilizer_compl, exact h sᶜ h1 h1', },
  -- h0' : ¬(s.nontrivial),
  { simp only [set.not_nontrivial_iff] at h0',
    exact h s h0 h0', },
end

/-- The action of alternating_group α on the n-element subsets of α is preprimitive
provided 0 < n < #α and #α ≠ 2*n -/
theorem nat.finset_is_preprimitive_of_alt (n : ℕ) (h_one_le : 1 ≤ n) (hn : n < fintype.card α)
  (hα : fintype.card α ≠ 2 * n) : is_preprimitive (alternating_group α) (n.finset α) :=
begin
  have hα' : 3 ≤ fintype.card α := three_le h_one_le hn hα,
  haveI : nontrivial α,
  { rw ← fintype.one_lt_card_iff_nontrivial, exact lt_of_le_of_lt h_one_le hn },
  cases nat.eq_or_lt_of_le h_one_le with h_one h_one_lt,
  { -- n = 1 :
    let f : α →[alternating_group α] nat.finset α 1 := {
      to_fun := λ x, ⟨{x}, finset.card_singleton x⟩,
      map_smul' := λ g x, rfl },
    rw ← h_one,
    suffices hf : function.surjective f,
    { apply is_preprimitive_of_surjective_map hf,
      exact alternating_group.is_preprimitive hα', },
    rintro ⟨s, hs⟩,
    change s.card = 1 at hs,
    rw finset.card_eq_one at hs,
    obtain ⟨a, ha⟩ := hs,
    use a,
    simp only [ha, equivariant_map.coe_mk], refl, },

  -- h_one_lt : 1 < n
  haveI ht : is_pretransitive (alternating_group α) (n.finset α),
  { -- apply nat.finset_is_pretransitive_of_multiply_pretransitive,
    have : (fintype.card α - n) + n = fintype.card α,
    { apply nat.sub_add_cancel , exact le_of_lt hn, },
    rw is_pretransitive_of_bijective_map_iff (function.surjective_id)
      (nat.finset_compl_bijective α (alternating_group α) n this),
    apply nat.finset_is_pretransitive_of_multiply_pretransitive,
    have h' : fintype.card α - n ≤ fintype.card α - 2,
    { apply nat.sub_le_sub_left , exact h_one_lt, },

    apply is_multiply_pretransitive_of_higher (alternating_group α) α _ h',
    rw part_enat.card_eq_coe_fintype_card, simp only [part_enat.coe_le_coe, tsub_le_self],
    exact alternating_group_is_fully_minus_two_pretransitive α, },

  haveI : nontrivial (n.finset α) :=
    nat.finset_nontrivial α n (lt_trans (nat.lt_succ_self 0) h_one_lt) hn,
  obtain ⟨sn : n.finset α⟩ := nontrivial.to_nonempty,
  let s := sn.val,
  let hs : s.card = n := sn.prop,
  -- have hs : (s : finset α).card = n := s.prop,
  rw ← maximal_stabilizer_iff_preprimitive (alternating_group α) sn,
  have : stabilizer (alternating_group α) sn = stabilizer (alternating_group α) (s : set α),
  { ext g,
    simp only [mem_stabilizer_iff],
    rw ← subtype.coe_inj,
    change g • s = s ↔ _,
    rw [← finset.coe_smul_finset, ← finset.coe_inj], },
  rw this,
  apply stabilizer.is_maximal (s : set α),
  { simp only [finset.coe_nonempty, ← finset.card_pos, hs],
    apply lt_trans one_pos h_one_lt, },
  { simp only [← finset.coe_compl, finset.coe_nonempty, ← finset.card_compl_lt_iff_nonempty,
      compl_compl, hs],
    exact hn, },
  { simp only [finset.coe_sort_coe, fintype.card_coe, hs],
    exact hα, },
  apply_instance,
end

end alternating_group
