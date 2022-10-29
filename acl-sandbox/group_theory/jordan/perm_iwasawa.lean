/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic.basic tactic.group

import group_theory.solvable
import group_theory.group_action.sub_mul_action
import .for_mathlib.set
import .for_mathlib.group_theory__subgroup__basic
import .for_mathlib.alternating
import .mul_action_finset

import .jordan


/-
-- import .for_mathlib.alternating

import .primitive
import .multiple_transitivity


 -/


open_locale pointwise

open mul_action


open_locale classical

variables {α : Type*} [decidable_eq α] (G : Type*) [group G] [mul_action G α]

/-- A group `G` acting on `α` is pretransitive if it is pretransitive on `s : set α`
and its complement `sᶜ`, and if it does not stabilizes `s` -/
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
  rw eq_top_iff,
  rw le_stabilizer_iff ,
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

lemma fintype.card_add_compl (s : set α) :
  fintype.card s + fintype.card (sᶜ : set α) = fintype.card α :=
begin
  rw fintype.card_compl_set ,
  rw add_comm,
  rw nat.sub_add_cancel,
  exact set_fintype_card_le_univ s,
end


lemma moves_in (t : set α) : ∀ (a ∈ t) (b ∈ t),
  ∃ (g ∈ stabilizer (equiv.perm α) t), g • a = b :=
begin
  intros a ha b hb,
  use equiv.swap a b,
  split,
  { apply swap_mem_stabilizer ha hb, },
  { change (equiv.swap a b) • a = b,
    simp only [equiv.perm.smul_def],
    rw equiv.swap_apply_left, },
end

lemma moves_in' (G : subgroup (equiv.perm α)) (t : set α)
  (hGt : stabilizer (equiv.perm α) t ≤ G) :
  ∀ (a ∈ t) (b ∈ t), ∃ (g : G), g • a = b :=
begin
  intros a ha b hb,
  obtain ⟨g, hg, H⟩ := moves_in t a ha b hb,
  use g, apply hGt,  exact hg, exact H,
end

example (s : finset α) (g : equiv.perm α) : (g • s).card  = s.card :=
begin
  change (finset.image (λ x, g • x)  s).card = _,
  rw finset.card_image_of_injective _ (mul_action.injective g),
end

example (s t : set α) (hst : s ⊆ t) : fintype.card s ≤ fintype.card t :=
begin
  exact set.card_le_of_subset hst,
end

lemma fixing_subgroup_le_stabilizer (s : set α) :
  fixing_subgroup G s ≤ stabilizer G s :=
begin
  intros k hk,
  rw mem_fixing_subgroup_iff at hk,
  rw mem_stabilizer_iff,
  change (λ x, k • x) '' s = s,
  conv_rhs { rw ← set.image_id s},
  apply set.image_congr ,
  simp only [id.def],
  exact hk,
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

example (p q : Prop) (hq : q) : p → q := begin
exact imp_intro hq,
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

example (G : Type*) [group G] [fintype G] (H : subgroup G) :
  fintype.card H ≤ fintype.card G :=
begin
  apply nat.le_of_dvd, refine fintype.card_pos,
  refine subgroup.card_subgroup_dvd_card H,
end


lemma subgroup_of_group_of_order_two {G : Type*} [group G] [fintype G] (hG : fintype.card G = 2)
  (H : subgroup G) : H = ⊥ ∨ H = ⊤ :=
begin
  cases le_or_lt (fintype.card H) 1,
  { apply or.intro_left, apply subgroup.eq_bot_of_card_le, exact h, },
  { apply or.intro_right, apply subgroup.eq_top_of_card_eq,
    apply le_antisymm,
    { apply nat.le_of_dvd, refine fintype.card_pos,
      refine subgroup.card_subgroup_dvd_card H, },
    rw hG, exact h, },
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
      apply lt_of_lt_of_le one_lt_two,
      apply le_of_eq,
      rw ← hα, apply symm,
      rw set_fintype_card_eq_univ_iff,
      -- because one_lt_two needs it!
      apply_instance, },

    rw [fintype.card_perm, hα], norm_num,
end

example (s : set α) (g : equiv.perm α) :
  s.subsingleton ↔ (g • s).subsingleton :=
  begin
  change _ ↔ ((λ x, g • x) '' s).subsingleton,
  split,
  intro hs, apply set.subsingleton.image, exact hs,
  intro hgs, apply set.subsingleton_of_image _ s hgs,
  apply function.bijective.injective,
  apply mul_action.bijective,
end

example (s : set α) (g : equiv.perm α) : g • s ⊆ s ↔ g • s = s :=
begin
  rw ← mem_stabilizer_iff,
  rw ← mem_stabilizer_of_finite_iff,
end

lemma equiv.perm.of_subtype.mem_stabilizer (s : set α) (g : equiv.perm s) :
  equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) s :=
begin
  rw mem_stabilizer_of_finite_iff,
  { intro x,
    rw set.mem_smul_set ,
    rintro ⟨y, hy, rfl⟩,
    simp only [equiv.perm.smul_def],
    rw equiv.perm.of_subtype_apply_of_mem g hy,
    refine subtype.mem _, },
/- -- Preuve plus longue qui marche sans [fintype s]
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
      subtype.coe_mk], },
      -/
end


lemma equiv.perm.of_subtype.mem_stabilizer' (s : set α) (g : equiv.perm (sᶜ : set α)) :
  equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) s :=
begin
 -- The proof that does not work, for a reason I don't understand
 -- stabilizer_compl adds a `classical.prop_decidable` instance, but
 -- the lemma expects `set.compl_decidable`.
 /-
    rw ← stabilizer_compl,
    let hz := @equiv.perm.of_subtype.mem_stabilizer α _ _ (sᶜ : set α) g,
-/
  rw mem_stabilizer_of_finite_iff,
  { intro x,
    rw set.mem_smul_set ,
    rintro ⟨y, hy, rfl⟩,
    simp only [equiv.perm.smul_def],
    rw equiv.perm.of_subtype_apply_of_not_mem g (set.not_mem_compl_iff.mpr hy),
    exact hy, },
/- -- Une preuve plus longue qui marche sans [fintype s]
  rw mem_stabilizer_iff,
  apply set.subset.antisymm,
  { intro x,
    rw set.mem_smul_set ,
    rintro ⟨y, hy, rfl⟩,
    simp only [equiv.perm.smul_def],
    rw equiv.perm.of_subtype_apply_of_not_mem g (set.not_mem_compl_iff.mpr hy),
    exact hy, },
  { intros x hx,
    use x, apply and.intro hx,
    simp only [equiv.perm.smul_def],
    apply equiv.perm.of_subtype_apply_of_not_mem,
    rw set.not_mem_compl_iff, exact hx, }, -/
end


example : mul_action (equiv.perm α) (set α) :=
begin
exact set.mul_action_set,
end

lemma equiv.perm.stabilizer.is_preprimitive (s : set α) : is_preprimitive (stabilizer (equiv.perm α) s) s :=
begin
  let φ : stabilizer (equiv.perm α) s → equiv.perm s := mul_action.to_perm,
  let f : s →ₑ[φ] s := {
  to_fun := id,
  map_smul' := λ g x,  by simp only [id.def, equiv.perm.smul_def, to_perm_apply], },
  have hf : function.bijective f := function.bijective_id,
  rw is_preprimitive_of_bijective_map_iff _ hf,
  exact equiv.perm.is_preprimitive s,

  -- function.surjective φ,
  intro g, use equiv.perm.of_subtype g,
  { -- ⇑equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) s
    apply equiv.perm.of_subtype.mem_stabilizer,
   },
  { -- φ ⟨⇑equiv.perm.of_subtype g, _⟩ = g
    ext ⟨x, hx⟩,
    change (equiv.perm.of_subtype g) • x = _,
    simp only [equiv.perm.smul_def],
    rw equiv.perm.of_subtype_apply_of_mem, },
end

lemma equiv.perm.stabilizer.is_preprimitive' (s : set α) (G : subgroup (equiv.perm α))
  (hG : stabilizer (equiv.perm α) s ≤ G) : is_preprimitive (stabilizer G s) s :=
begin
  let φ : stabilizer (equiv.perm α) s → stabilizer G s :=
  λ g, ⟨⟨g, hG g.prop⟩, mem_stabilizer_iff.mp g.prop⟩,
  let f: s →ₑ[φ] s := {
    to_fun := id,
    map_smul' := λ ⟨m, hm⟩ x,
    begin
      simp only [id.def, φ, ← subtype.coe_inj],
      simp only [of_stabilizer_def, subgroup.coe_mk, equiv.perm.smul_def],
      refl,
    end, },
  have : function.surjective f := function.surjective_id,
  apply is_preprimitive_of_surjective_map this,
  apply equiv.perm.stabilizer.is_preprimitive,
end

theorem equiv.perm.is_maximal_stab' (s : set α) (h0 : s.nonempty) (h1 : sᶜ.nonempty)
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
    { intros a ha b hb,
      obtain ⟨g, _, h⟩ := moves_in' G s (le_of_lt hG) a ha b hb,
      use g, exact h, },
    { intros a ha b hb,
      rw ← stabilizer_compl at hG,
      obtain ⟨g, hg, h⟩ := moves_in' G sᶜ (le_of_lt hG) a ha b hb,
      use g, exact h, },
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

        apply equiv.perm.stabilizer.is_preprimitive',
        rw ← stabilizer_compl at hG, exact le_of_lt hG, },

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
      map_smul' := λ m x, by simp only [φ', has_smul.smul_stabilizer_def], },
      apply mul_action.is_block_preimage f' hB,

      apply equiv.perm.stabilizer.is_preprimitive',
      exact le_of_lt hG,

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
            apply mul_action.fixing_subgroup_le_stabilizer,
            exact hk, } },
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
          rw part_enat.of_fintype α,
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
  (hα : fintype.card α ≠ 2 * n) : is_preprimitive (equiv.perm α) (nat.finset α n) :=
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
  haveI ht : is_pretransitive (equiv.perm α) (n.finset α) := nat.finset_is_pretransitive α n,
  haveI : nontrivial (n.finset α) :=
    nat.finset_nontrivial α n (lt_trans (nat.lt_succ_self 0) h_one_lt) hn,
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


/- Definition of the Iwasawa structure -/


def Iw_conj (s : finset α) (g : equiv.perm α) : equiv.perm s ≃* equiv.perm ((g • s) : finset α) :=
{ map_mul' := λ h k, equiv.ext (λ x, by simp only [equiv.to_fun_as_coe, equiv.perm_congr_apply,
    equiv.subtype_equiv_symm, equiv.subtype_equiv_apply, equiv.perm.coe_mul,
    function.comp_app, subtype.coe_mk, equiv.symm_apply_apply, finset.mk_coe])
  ..
  equiv.perm_congr (@equiv.subtype_equiv α α (λ a, a ∈ s) (λ a, a ∈ g • s) (g : α ≃ α)
  ((λ a, by rw [← finset.smul_mem_smul_finset_iff g, equiv.perm.smul_def]) :
    ∀ (a : α), a ∈ s ↔ g a ∈ g • s)) }


lemma Iw_conj_eq : ∀ (s : finset α) (g : equiv.perm α )(k : equiv.perm ↥s),
  ((mul_aut.conj g).to_monoid_hom.comp
    (equiv.perm.of_subtype :(equiv.perm s) →* (equiv.perm α)) k)  =
  (equiv.perm.of_subtype : equiv.perm ((g • s) : finset α) →* (equiv.perm α)) (Iw_conj s g k) :=
begin
  intros s g k,
  dsimp only [Iw_conj],
  ext x,
  simp only [monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, function.comp_app,
      mul_aut.conj_apply, equiv.perm.coe_mul],
  cases em (x ∈ g • s) with hx hx',
  { -- x ∈ g • s
    rw equiv.perm.of_subtype_apply_of_mem,
    rw equiv.perm.of_subtype_apply_of_mem,
    simp only [subtype.coe_mk, equiv.subtype_equiv_symm, equiv.to_fun_as_coe, mul_equiv.coe_mk,
      equiv.perm_congr_apply, equiv.subtype_equiv_apply, embedding_like.apply_eq_iff_eq],
    apply congr_arg, apply congr_arg,
    rw ← subtype.coe_inj, simp only [subtype.coe_mk], refl,
    exact hx,
    rw ← finset.inv_smul_mem_iff at hx, exact hx, },
  { -- x ∉ g • s
    rw equiv.perm.of_subtype_apply_of_not_mem,
    rw equiv.perm.of_subtype_apply_of_not_mem,
    simp only [equiv.perm.apply_inv_self],
    exact hx',
    { rw [← finset.inv_smul_mem_iff] at hx', exact hx', }, },
end

lemma Iw_is_conj' (s : finset α) (g : equiv.perm α) :
  equiv.perm.of_subtype.comp (Iw_conj s g).to_monoid_hom =
    ((mul_aut.conj g).to_monoid_hom).comp equiv.perm.of_subtype :=
begin
  ext k x,
  simp only [monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, function.comp_app,
    mul_aut.conj_apply, equiv.perm.coe_mul],
  rw ← Iw_conj_eq,
  simp only [monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, function.comp_app,
    mul_aut.conj_apply, equiv.perm.coe_mul],
end

lemma Iw_is_conj (s : finset α) (g : equiv.perm α) :
  (equiv.perm.of_subtype : equiv.perm ((g • s) : finset α) →* (equiv.perm α)).range =
  mul_aut.conj g • ((equiv.perm.of_subtype : equiv.perm s →* equiv.perm α)).range :=
begin
  suffices : (equiv.perm.of_subtype : equiv.perm ((g • s) : finset α) →* (equiv.perm α)).range
   = ((equiv.perm.of_subtype : equiv.perm ((g • s) : finset α) →* (equiv.perm α)).comp
    (Iw_conj s g).to_monoid_hom).range,
  { rw this,
    change _ = subgroup.map (mul_aut.conj g).to_monoid_hom _,
    simp only [monoid_hom.map_range],
    apply congr_arg,
    apply Iw_is_conj', },

  simp only [monoid_hom.range_eq_map, ← subgroup.map_map],
  apply congr_arg,
  simp only [← monoid_hom.range_eq_map],
  -- Via sets :
  apply set_like.coe_injective,
  simp only [monoid_hom.coe_range, mul_equiv.coe_to_monoid_hom, subgroup.coe_top,
  ← mul_equiv.coe_to_equiv, equiv.range_eq_univ],
end

def Iw2 : iwasawa_structure (equiv.perm α) (nat.finset α 2) :=
{ T := λ s, (equiv.perm.of_subtype : (equiv.perm (s : finset α)) →* (equiv.perm α)).range,
  is_comm := λ s,
  begin
    apply monoid_hom.range_is_commutative,
    rw ← equiv.perm.is_commutative_iff,
    apply le_of_eq,
    change fintype.card ↥(s : finset α) = 2,
    simp only [fintype.card_coe],
    exact s.prop,
  end,
  is_conj := λ g s, Iw_is_conj ↑s g,
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
  obtain ⟨s, hs⟩ := nat.finset.mul_action_faithful 2 _ _ _,
  { -- Conclusion
    apply hs,
    suffices : s ∈ fixed_points N (nat.finset α 2),
    rw mem_fixed_points at this, exact this ⟨g, hgN⟩,
    rw h, rw set.top_eq_univ, apply set.mem_univ, },
  -- fintype α
  apply_instance,
  -- 1 < 2
  norm_num,
  -- 2 < fintype.card α
  apply lt_of_lt_of_le _ hα, norm_num,
  -- to_perm g ≠ 1
  suffices : to_perm (⟨g, hgN⟩ : N) = g,
  rw this, exact hg_ne,
  ext x, simp only [to_perm_apply], refl,
end






-- #lint


#exit

end action_on_finsets

open equiv.perm equiv mul_action
variables (α : Type*) [decidable_eq α] (G : Type*) [group G] [mul_action G α]

variables {G α}

section Permutations

/-- The symmetric group is generated by permutations of the form (a x), for any fixed a -/
-- → group_theory.perm.sign
theorem equiv.perm.closure_is_based_swap (a : α) : subgroup.closure { f : perm α | ∃ (x : α), f = swap a x } = ⊤ :=
begin
  apply top_unique,
  rw ← closure_is_swap,
  let H := subgroup.closure { f : perm α | ∃ (x : α), f = swap a x },
  have h_swaps : ∀ (x : α), swap a x ∈ H ,
  { intro x,
    apply subgroup.subset_closure,
    simp only [exists_apply_eq_apply', set.mem_set_of_eq] },
  apply (subgroup.closure_le H).mpr,
  intros f hf,
  rw set.mem_set_of_eq at hf,
  obtain ⟨x, y, hxy, rfl⟩ := hf,
    -- (a x) (a y) (a x) = (x y)
    cases dec_em (x = a) with hxa hxa',
    { -- hxa : x = a
      rw hxa, exact h_swaps y, },
    -- hxa' : x ≠ a'
    cases dec_em (y = a) with hya hya',
    { -- hya : y = a
      rw hya, rw equiv.swap_comm, exact h_swaps x },

    rw ← swap_mul_swap_mul_swap hya' hxy.symm,
    apply subgroup.mul_mem H _ (h_swaps x),
    apply subgroup.mul_mem H (h_swaps x) _,
    rw equiv.swap_comm,
    exact h_swaps y,
end

/- now unused, is replaced by action on lists
/-- The standard action of perm α on α is multi-transitive -/
-- The proof is awfully long, maybe I should learn about finset
theorem standard_is_multi_transitive (n : ℕ) (hn : n ≤ fintype.card α) :
  mul_action.is_pretransitive (perm α) (func.inj_pow (perm α) α n) :=
begin
  induction n with n hrec,
  { apply mul_action.is_pretransitive.mk,
    intros x y,
    use (1 : perm α), rw one_smul,
    ext i, apply fin.elim0 i },
  { apply mul_action.is_pretransitive.mk,
    intros x y,
    -- définir x' et y' comme les restrictions de x et y à fin n
    let j := fin.cast_succ,
    let hj : function.injective j := fin.cast_succ_injective n,

    let x' := func.inj_map.comp j hj x,
    let y' := func.inj_map.comp j hj y,
    let this := (hrec (nat.le_of_succ_le hn)).exists_smul_eq,
    obtain ⟨g, hg⟩ := this x' y',

    have : g • (func.inj_map.comp j hj x) = func.inj_map.comp j hj (g • x),
    { simp only [mul_action_hom.map_smul] },

    have h_upto_n': ∀ (i : fin n.succ) (hi : i < fin.last n), (g • x).val i = y.val i,
    { intros i hi,
      let i' := fin.cast_lt i hi,
      simp only [perm.smul_def, func.smul_def, subtype.val_eq_coe, sub_mul_action.coe_smul_of_tower],
      have tx : x.val i = x'.val i',
      { let z:= func.inj_map.comp_eval j hj x i',
        simp only [fin.cast_succ_cast_lt, subtype.val_eq_coe] at z,
        exact z.symm, },
      have ty : y.val i = y'.val i',
      { let z:= func.inj_map.comp_eval j hj y i',
        simp only [fin.cast_succ_cast_lt, subtype.val_eq_coe] at z,
        exact z.symm, },
      have t' : g • x'.val i' = y'.val i',
      { let hg2 := congr_arg (λ x : func.inj_map _ _ _, x.val) hg ,
        exact congr_fun hg2 i',
      },
      simp only [perm.smul_def, subtype.val_eq_coe] at t' tx ty,
      rw ty, rw tx, exact t' },

    let g' := equiv.swap ((g • x).val (fin.last n)) (y.val (fin.last n)),
    have h_inj_n : ∀ (f : func.inj_pow (perm α) α n.succ) (i : fin n.succ) (hi : i < fin.last n), f.val i ≠ f.val (fin.last n),
    { intros f i hi hx,
      rw f.prop hx at hi,
      exact lt_irrefl (fin.last n) hi  },

    use g'*g,

    ext i,
    cases le_iff_lt_or_eq.mp (fin.le_last i) with hi hn,
    { have ht : g' • ((g • x).val i) = y.val i,
      { rw ← h_upto_n' i hi,
        refine equiv.swap_apply_of_ne_of_ne _ _ ,
        exact h_inj_n (g • x) i hi,
        rw h_upto_n' i hi,
        exact h_inj_n y i hi },
      simpa only using ht},
    { rw hn,
      have ht : g' • ((g • x).val (fin.last n)) = y.val (fin.last n),
      { apply equiv.swap_apply_left _ _ },
      simpa only using ht } }
end
-/

/- unused : is done by general case of finsets
/-- The square of an action minus the diagonal, has a sub_mul_action -/
def square' (G : Type*) [group G] (X : Type*) [mul_action G X] :
 sub_mul_action G (X × X) :=
{ carrier := { x : X × X | x.1 ≠ x.2 },
  smul_mem' := λ g x hx,
  begin
    rw set.mem_set_of_eq at hx ⊢,
    simp only [hx, prod.smul_snd, prod.smul_fst, ne.def, smul_left_cancel_iff, not_false_iff],
  end, }

lemma standard_is_two_transitive (α : Type*) [decidable_eq α] [fintype α] :
  mul_action.is_pretransitive (perm α) (square' (perm α) α) :=
begin
  apply mul_action.is_pretransitive.mk,
  intros x y,

  let g := equiv.swap x.val.1 y.val.1,
  let x' := g • x,
  have t1 : x'.val.1 = y.val.1,
  { simp only [perm.smul_def, prod.smul_fst, subtype.val_eq_coe, sub_mul_action.coe_smul_of_tower],
    refine equiv.swap_apply_left _ _,  },

  let h := equiv.swap x'.val.2 y.val.2,

  use h*g,

  apply subtype.ext_iff_val.mpr,
  apply prod.ext_iff.mpr,
  split,
  have : h • (x'.val.1) = y.val.1,
  { rw ← t1,
    refine equiv.swap_apply_of_ne_of_ne _ _ ,
    exact x'.prop,
    rw t1, exact y.prop  },
  exact this,
  refine equiv.swap_apply_left _ _,
end


theorem transitive_on_pairs {α : Type*} [decidable_eq α] [fintype α] :
 --  ∀ (x y : action_on_pairs_of (perm α) α) , ∃ (g : perm α), g • x = y :=
  mul_action.is_pretransitive (perm α) (action_on_pairs_of (perm α) α) :=
begin
  apply mul_action.is_pretransitive.mk,
  intros x y,
  let px : square' (perm α) α := ⟨pair.lift x, pair.lift.ne x⟩,
  let py : square' (perm α) α := ⟨pair.lift y, pair.lift.ne y⟩,
  have h := (standard_is_two_transitive α).exists_smul_eq,
  obtain ⟨g, hg⟩ := h px py,
  use g,
  apply set_like.coe_eq_coe.mp,
  rw sub_mul_action.coe_smul,
  rw pair.lift.spec x, rw pair.lift.spec y,
  change (λ a, g • a) '' {(pair.lift x).fst, (pair.lift x).snd} = {(pair.lift y).fst, (pair.lift y).snd},
  rw set.image_pair,
  let hg' := set_like.coe_eq_coe.mpr hg,
  simp only [sub_mul_action.coe_smul, subtype.coe_mk] at hg',
  rw ← hg',
  simp only [prod.smul_snd, prod.smul_fst],
end
-/

theorem transitive_on_nodup_list.exists_smul_eq
  (s t : list α) (hs : s.nodup) (ht : t.nodup) (hst : s.length = t.length) :
  ∃ (g : perm α), g • s = t :=
begin
  revert t,
  induction s,
  case nil { -- s = list.nil
    intros t ht hst,
    use 1,
    change list.map ⇑(1 : perm α) list.nil = t,
    rw list.map_nil,
    simp only [list.length] at hst,
    apply symm,
    apply list.length_eq_zero.mp,
    exact hst.symm, } ,
  case cons  :  a  s' ih { -- s = a :: s'
    specialize ih (list.nodup_of_nodup_cons hs),
    have has' : a ∉ s' := list.not_mem_of_nodup_cons hs,
    intros t ht hst,
    cases t with b t' ,
    case nil {  -- t = list.nil, absurd
      simp only [list.length, nat.succ_ne_zero] at hst,
      exfalso, assumption, },
    case cons {  -- t = b :: t'
    have hbt' : b ∉ t' := list.not_mem_of_nodup_cons ht,
    simp only [add_left_inj, list.length] at hst,
    obtain ⟨g' : perm α, hg' : g' • s' = t'⟩ := ih t' (list.nodup_of_nodup_cons ht) hst,
    use (equiv.swap b (g' • a)) * g',
    simp only [mul_smul, perm.smul_def],
    have hg'' : g' • (a :: s') = (g' • a) :: t',
    { change list.map ⇑g' (a :: s') = (g' • a) :: t',
      change list.map ⇑g' s' = t' at hg',
      rw list.map_cons _ _ _,
      rw hg',
      refl, },
    rw hg'',
    change list.map (swap b (g' • a)) (g' • a :: t')  = b :: t',
    rw list.map_cons _ _ _ ,
    simp only [true_and, perm.smul_def, eq_self_iff_true,swap_apply_right], -- only [perm.smul_def] at this ⊢,
    conv_rhs { rw ← list.map_id t', },
    apply list.map_congr ,
    intros x hx,
    simp only [id.def],
    apply equiv.swap_apply_of_ne_of_ne,
    -- b ∉ t'
    rintro ⟨rfl⟩, exact (list.nodup_cons.mp ht).left hx,
    -- g' • a ∉ t'
    rintro ⟨rfl⟩, rw ← hg' at hx,
    apply (list.nodup_cons.mp hs).left,
    exact (list.mem_map_of_injective (mul_action.injective g')).mp hx } }
end

example (s : finset α) : s.to_list.to_finset = s :=
begin
simp only [finset.to_list_to_finset],
end

lemma finset.map_to_list [decidable_eq β] (f : α → β) (s : finset α) :
  (list.map f s.to_list).to_finset = finset.image f s :=
begin
ext x,
split,
  { intro hx,
    rw list.mem_to_finset at hx,
    obtain ⟨a, ha, rfl⟩ := list.mem_map.mp hx,
    rw finset.mem_image,
    use a,
    split,
    rw finset.mem_to_list at ha, exact ha,
    refl },
  { intro hx,
    rw finset.mem_image at hx,
    obtain ⟨a, ha, rfl⟩ := hx,
    apply list.mem_to_finset.mpr,
    apply list.mem_map.mpr,
    use a, split,
    rw finset.mem_to_list, exact ha,
    refl, }
end

theorem transitive_on_fin_subsets.exists_smul_eq
  (s t : finset α) (hst : s.card = t.card) :
  ∃ (g : perm α), g • (s : set α) = t :=
begin
  rw ← finset.length_to_list s at hst,
  rw ← finset.length_to_list t at hst,
  obtain ⟨g : perm α, hg : list.map ⇑g s.to_list = t.to_list⟩ :=
    transitive_on_nodup_list.exists_smul_eq s.to_list t.to_list (finset.nodup_to_list s) (finset.nodup_to_list t) hst,
  use g,
  change (λx, g • x) '' (s : set α) = t,
  rw [← finset.coe_image, finset.coe_inj],

  rw ← finset.to_list_to_finset t,
  rw ← hg,
  rw ← finset.map_to_list (λ x, g • x) s,
  apply congr_arg,
  refl,
end

/- Direct proof for finsets, useless

theorem transitive_on_fin_subsets.exists_smul_eq' {α : Type*} [decidable_eq α]
  (s t : finset α) (hst : s.card = t.card) :
  ∃ (g : perm α), g • (s : set α) = t :=
begin
  /- Two possible approaches :
    1. enumerate s, t ; extend to enumerations of α ; and compose
    2. induction on cardinals.
        0 : g = 1
        n → n + 1 :
          - choose a ∈ s, b ∈ t
          - set s' = s \ {a}, t' = t \ {b}
          - choose g' such that g • s' = t'
          - set g = (swap b g' • a) * g'
          - g • s = g • (a ∪ s') = (swap b g'•a)  • g' • (a ∪ s')
              = (swap b g'•a) • (g'•a ∪ g'•s')
              = (swap b g'•a) • (g'•a ∪ t')
              = (swap b g'•a) • g'•a ∪ (swap b g'•a) • t'
              = b ∪ (swap b g'•a) • t'
          - b ∉  t',
          - g' • a ∉ t' = g' • s', sinon a ∈ s'
      I follow 2.
    -/
  suffices : ∀ (n : ℕ) (s t : finset α) (hs : s.card = n) (ht : t.card = n),
    ∃ (g : perm α), g • (s : set α) = t ,
    exact this (s.card) s t rfl hst.symm,
  intro n,
  induction n with n hrec,
  -- n = 0
  { intros s t hs ht,
    rw finset.card_eq_zero at hs ht,
    use 1,
    simp only [one_smul, finset.coe_inj],
    rw [ht, hs] },
  -- n → n.succ
  { intros s t hs ht,

    have hs' : 0 < s.card,  { rw hs, exact nat.succ_pos n,  },
    obtain ⟨a, ha⟩ := finset.card_pos.mp hs',
    let s' := s.erase a,
    have hs' : s'.card = n,
    { rw [← nat.pred_succ n, ← hs],
      apply finset.card_erase_of_mem ha, },

    have ht' : 0 < t.card, { rw ht, exact nat.succ_pos n, },
    obtain ⟨b, hb⟩ := finset.card_pos.mp ht',
    let t' := t.erase b,
    have ht' : t'.card = n,
    { rw [← nat.pred_succ n, ← ht],
      apply finset.card_erase_of_mem hb, },

    obtain ⟨g', hg'⟩ := hrec s' t' hs' ht',

    have finset.map_coe : ∀ (g : perm α) (s t : finset α),
      g • (s : set α) = t ↔ finset.image (λ x, g • x) s = t ,
    { intros g s t,
      split,
      { intro h,
        apply finset.coe_inj.mp,
        rw finset.coe_image,
        exact h },
      { intro h,
        change (λ x, g • x) '' ↑s = ↑t,
        rw ← finset.coe_image,
        exact finset.coe_inj.mpr h } },

    let hg' := (finset.map_coe _ _ _).mp hg',

    have hg₁ : g' • (s : set α) = insert (g' • a) t',
    { rw ← finset.coe_insert,
      apply (finset.map_coe g' s _).mpr,
      rw ← finset.insert_erase ha,
      rw finset.image_insert,
      apply congr_arg, exact hg', },

    let g := (equiv.swap b (g' • a)) * g',
    use g,
    rw mul_smul,
    rw hg₁,

    rw ← finset.coe_insert,
    rw (finset.map_coe (swap b (g' • a)) _ t).mpr,

    rw finset.image_insert,
    rw [perm.smul_def,  equiv.swap_apply_right],
    rw ← finset.insert_erase hb,
    apply congr_arg,

    have this : t.erase b = finset.image (λ x, (1 : perm α) • x) (t.erase b),
    { have this' : (λ (x : α), (1 : perm α) • x) = id,
        { funext, rw one_smul, refl,  },
      rw this',
      rw finset.image_id,  },
    rw this,
    apply (finset.map_coe _ _ _).mp,
    rw finset.coe_image,
    apply set.image_congr,
    intros x hx,
    rw perm.smul_def, apply equiv.swap_apply_of_ne_of_ne ,
      -- x ≠ b
      intro h, rw h at hx,
      exact (finset.not_mem_erase b t) hx,
      -- x ≠ g ' • a,
      intro h, rw h at hx, rw ← hg' at hx,
      simp only [perm.smul_def, set.mem_image, finset.coe_erase, set.mem_diff, set.mem_singleton_iff, eq_self_iff_true, not_true,
  exists_eq_right, apply_eq_iff_eq, and_false, finset.coe_image] at hx,
      exact hx },
end
-/

theorem transitive_on_pairs {α : Type*} [decidable_eq α] [fintype α] :
 --  ∀ (x y : action_on_pairs_of (perm α) α) , ∃ (g : perm α), g • x = y :=
  mul_action.is_pretransitive (perm α) (action_on_pairs_of (perm α) α) :=
begin
  apply mul_action.is_pretransitive.mk,
  intros x y,
  let fx := (pair.is_finite x).to_finset,
  let fy := (pair.is_finite y).to_finset,
  obtain ⟨g, hg⟩ := transitive_on_fin_subsets.exists_smul_eq fx fy _,
  swap,
    rw  (pair.card_eq_two x), rw (pair.card_eq_two y),
  use g,
    apply set_like.coe_eq_coe.mp,
    rw sub_mul_action.coe_smul,
    simp only [set.finite.coe_to_finset, set.coe_to_finset] at hg,
    exact hg,
end


end Permutations

section Subgroups

/--!
## Subgroups

Two lemmas to simplify stuff in presence of conjugation
-/

lemma subgroup.conj_of_mem_is_mem {G : Type*} [group G] (H : subgroup G) {g h : G} (hh : h ∈ H) :
    g ∈ H → h * g * h⁻¹ ∈ H  :=
begin
    intro hg,
    exact H.mul_mem (H.mul_mem hh hg) (H.inv_mem hh),
end

lemma subgroup.mem_conj_of_mem_iff {G : Type*} [group G] (H : subgroup G) {g h : G} (hh : h ∈ H) :
    h * g * h⁻¹ ∈ H ↔ g ∈ H :=
begin
  split,
  { intro hg,
    have hg' : g = h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹,
      by group,
    rw hg',
    exact subgroup.conj_of_mem_is_mem H (H.inv_mem hh) hg,
  /-
    rw ← mul_one g, rw ← inv_mul_self h,  rw ← mul_assoc,
    rw ← one_mul (g * h⁻¹ * h),
    rw ← inv_mul_self h,  rw  mul_assoc,
    apply H.mul_mem (H.inv_mem hh),
    rw ← mul_assoc,  apply H.mul_mem _ hh, rw ← mul_assoc,
    exact hg,  -/
  },
  exact  subgroup.conj_of_mem_is_mem H hh,
end

end Subgroups

section Gimme_Some

/-- Get a third element distinct from any two given -/
lemma out_of_three (α : Type*) [decidable_eq α] [fintype α] (hα: 3 ≤ fintype.card α) (x y : α) :
  ∃ (z : α), z ≠ x ∧ z ≠ y :=
begin
  let s := ({ y, x}: finset α),
  have : s.card < fintype.card α,
  exact calc s.card ≤ ({x} : finset α).card + 1 :
        by exact finset.card_insert_le y {x}
    ... ≤ 1 + 1 : by rw finset.card_singleton x
    ... ≤ 2 : by simp only [le_refl]
    ... < fintype.card α : by exact nat.succ_le_iff.mp hα,

  have : sᶜ.card > 0,
  exact calc sᶜ.card = (finset.univ).card - s.card :
        finset.card_univ_diff s
    ... > 0 : by refine lt_tsub_comm.mp this,

  obtain ⟨z, h⟩ := finset.card_pos.mp (gt_iff_lt.mp this),
  have h' : ¬(z ∈ s) := finset.mem_compl.mp h,
  use z,
  split,
  have hxs : x ∈ s,
  { apply finset.mem_insert.mpr ,
    apply or.intro_right,
    refine finset.mem_singleton.mpr rfl , },
  intro hx, rw hx at h', exact h' hxs,
  have hys : y ∈ s, by refine finset.mem_insert_self y {x},
  intro hy, rw hy at h', exact h' hys,
end

/-- Get an element distinct from those of a given list -/
lemma out_of_list (α : Type*) [decidable_eq α] [fintype α]
  (l : list α) (hα: l.length < fintype.card α) :
  ∃ (z : α), ∀ (x : α), x ∈ l → z ≠ x :=
begin
  let s := list.to_finset l,
  have : s.card < fintype.card α :=
    lt_of_le_of_lt (list.to_finset_card_le l) hα,

  have : sᶜ.card > 0,
  exact calc sᶜ.card = (finset.univ).card - s.card :
        finset.card_univ_diff s
    ... > 0 : by refine lt_tsub_comm.mp this,

  obtain ⟨z, h⟩ := finset.card_pos.mp (gt_iff_lt.mp this),
  simp only [finset.mem_compl, list.mem_to_finset] at h,
  use z,
  intros x hx,
  intro hz, rw ← hz at hx,
  exact h hx,
end

end Gimme_Some

section Iwasawa

/-!
## Iwasawa Criterion

We construct an Iwasawa structure for perm α acting on pairs of α.

TODO : Construct an Iwasawa structure for perm α acting on triples of α.

-/

open_locale pointwise
open classical

theorem faithful_on_pairs' (α : Type*) [decidable_eq α] [fintype α]
  (hα : 3 ≤ fintype.card α) (g : perm α) (hg : g ≠ 1) :
  ∃ (x : action_on_pairs_of (perm α) α), g • x ≠ x :=
  --  mul_action.fixed_by (perm α) (action_on_pairs_of (perm α) α) g ≠ ⊤ :=
begin
  have : ∃ (a : α), g • a ≠ a,
    by_contradiction,
    simp at h hg,
    apply hg,
    ext a,
    simp only [perm.coe_one, id.def],
    exact h a,
  obtain ⟨a, ha⟩ := this,
  obtain ⟨c, hc⟩ := out_of_list  α [a, g • a] _,
  swap,
    refine lt_of_lt_of_le _ hα,
    simp only [list.length, list.length_singleton, nat.lt.base],
  have hc : c ≠ a ∧ c ≠ g • a,
  split,
    refine hc _ _, simp,
    refine hc _ _, simp,
  simp only [perm.smul_def] at hc,
  let x : action_on_pairs_of (perm α) α := pair.mk hc.left,
  use x,

 --  intro htop,
 -- rw set.top_eq_univ at htop,
 -- let hx' := set.eq_univ_iff_forall.mp htop x,
 -- simp at hx',
  intro hx',
  let h' := set_like.coe_eq_coe.mpr hx',
  simp only [has_smul.subpair_apply, pair.is_def, sub_mul_action.coe_smul_of_tower] at h',
  have hc1 : g • a ∈ {g • c, g • a} := is_in_subpair_right ,
  rw h' at hc1, simp only [perm.smul_def] at hc1 ha,
  cases is_in_subpair_iff.mp hc1 with hh1 hh2,
    exact hc.right hh1.symm,
    exact ha hh2,
end


/- Now useless

/-- The stabilizer of a pair is not ⊤ -/
theorem pairs_stabilizers_is_not_top (α : Type*) [decidable_eq α] [fintype α]
  (hα : 3 ≤ fintype.card α) (x : action_on_pairs_of (perm α) α) :
  (stabilizer (perm α) x) ≠ ⊤ :=
begin
  revert x,
  rintro ⟨x,a, b, h_a_ne_b, rfl⟩,
  obtain ⟨c, hc⟩ := out_of_list α [a,b] (lt_of_lt_of_le (nat.lt.base 2) hα),
  let g := equiv.swap a c,
  have g_ab_ne_ab : g • { a, b} ≠ { a, b} ,
  { intro h,
    rw has_smul.subpair_apply g a b at h,
    have : c = g • a ,
      simp only  [swap_apply_left, perm.smul_def],
    have : c = a ∨ c = b,
    { apply is_in_subpair_iff.mp,
      rw this, rw ←h,
      apply is_in_subpair_left  },
    cases this with ha' hb',
    specialize hc a,
    refine (hc _) ha' ,
    simp only [list.mem_cons_iff, true_or, eq_self_iff_true],
    specialize hc b, refine (hc _) hb',
    simp only [list.mem_cons_iff, eq_self_iff_true, or_true, list.mem_singleton],     },

    have g_ne_stab : ¬(g ∈ (stabilizer (perm α)  ({a,b} : set α))),
    { intro h,
      exact g_ab_ne_ab (mem_stabilizer_iff.mp h), },

    intro h,
    let w := (stabilizer_of_sub_mul (perm α) (action_on_pairs_of (perm α) α)) ⟨{a,b},_⟩,
    rw set_like.coe_mk {a,b} _ at w,
    rw w at h,

    let hg := subgroup.mem_top g,
    rw ← h at hg,

    exact g_ab_ne_ab hg
end

/-- The stabilizer of a pair {a,b} contains the transposition (a b) -/
lemma pairs_stabilizers_maximal.has_swap' (α : Type*) [decidable_eq α] [fintype α]
  (a b : α) :
  equiv.swap a b ∈ stabilizer (perm α) ({a, b} : set α) :=
begin
  rw mem_stabilizer_iff,
  /- change swap a b ∈ { x : perm α | x • ({a, b} : set α) = {a, b} },
  rw set.mem_set_of_eq, -/
  rw has_smul.subpair_apply,
  simp only [swap_apply_left, perm.smul_def, swap_apply_right],
  exact subpair_symm  , -- b a
end

/-- The stabilizer of a pair {a, b} contains a transposition of the form (a c),
 for some c ∉ {a, b} -/
theorem pairs_stabilizers_maximal.has_swaps (α : Type*) [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α)
  (a b : α) (h_a_ne_b : a ≠ b)
  (H : subgroup (perm α))
  (hH : stabilizer (perm α) ({a,b} : set α) < H) :
  ∃ (c : α), c ≠ a ∧ c ≠ b ∧ swap a c ∈ H :=
begin
  let hH' := le_of_lt hH,
  obtain ⟨h, h_in_H, h_not_in_stab⟩ :=
    (set.ssubset_iff_of_subset hH').mp hH,

  have h_ab : h • ({a, b} : set α) = {h • a, h • b} :=
    has_smul.subpair_apply h a b,

  have h_ab_ne_ab : h • ({a, b} : set α) ≠ {a, b},
  { intro _,
    apply h_not_in_stab,
    apply mem_stabilizer_iff.mpr,
    assumption },

  have h_ab_H : equiv.swap a b ∈ H,
  { apply  hH',
    apply pairs_stabilizers_maximal.has_swap' },

  cases classical.em (h • a = a) with ha ha',
  { -- h • a = a; then h • b ≠ b
    rw ha at h_ab,
    use h • b,
    split, -- h • b ≠ a
    { intro hba,  apply h_a_ne_b,
      apply smul_left_cancel h,  rw [ha, hba] },
    split, -- h • b ≠ b
    { intro hb, rw hb at h_ab, exact h_ab_ne_ab h_ab, },
    -- swap a (h • b) ∈ H
    rw ← ha,
    simp only [perm.smul_def],
    rw equiv.swap_apply_apply h a b ,
    exact (subgroup.mem_conj_of_mem_iff H h_in_H).mpr h_ab_H },

  -- cas restants : h • a ≠ a
  cases classical.em (h • a = b) with hab hab',
  { -- h • a = b, donc h • b ≠ a,
    rw hab at h_ab,
    use h • b,
    have hb_ne_a : h • b ≠ a,
    { intro hba, rw hba at h_ab, rw h_ab at h_ab_ne_ab,
      apply  h_ab_ne_ab, exact subpair_symm, },
    have hb_ne_b : h • b ≠ b,
    { intro hb, rw ← hb at hab,
      exact h_a_ne_b (smul_left_cancel h hab),  },
    split, exact hb_ne_a,
    split, exact hb_ne_b,
    have : swap a (h • b) = (swap a b) * h * (swap a b) * h⁻¹ * (swap a b),
    { simp only [perm.smul_def],
      -- conjugation with (swap a b)
      apply (mul_right_inj (swap a b)).mp,
      apply (mul_left_inj (swap a b)⁻¹).mp,
      -- simplification of the LHS
      rw ← equiv.swap_apply_apply (swap a b) _ _ ,
      simp only [swap_apply_left, swap_inv],
      have : (swap a b) • (h • b) = h • b :=
        equiv.swap_apply_of_ne_of_ne hb_ne_a hb_ne_b,
      simp only [perm.smul_def] at this,
      rw this,
      -- simplification of the RHS
      simp  [mul_assoc, equiv.mul_swap_mul_self, equiv.swap_mul_self_mul],
      rw ← mul_assoc,
      rw ← equiv.swap_apply_apply h a b,

      simp only [perm.smul_def] at hab,
      rw hab, },
    rw this,

    -- ⊢ swap a b * h * swap a b * h⁻¹ * swap a b ∈ H
    apply subgroup.mul_mem H _ h_ab_H,
    apply subgroup.mul_mem H _ (subgroup.inv_mem H h_in_H),
    apply subgroup.mul_mem H _ h_ab_H,
    apply subgroup.mul_mem H h_ab_H h_in_H },

    -- cas restants : ha', hab' : h • a ≠ a, b
  cases classical.em (h • b = a) with hba hba',
  { -- hba : h • b = a
    use h • a,
    split, exact ha', split, exact hab',
    have : swap a (h • a) = h * (swap a b) * h⁻¹,
    { simp only [perm.smul_def],
      rw ← equiv.swap_apply_apply h _ _ ,
      simp only [perm.smul_def] at hba,
      rw hba,
      rw equiv.swap_comm },
    rw this,

    exact (subgroup.mem_conj_of_mem_iff H h_in_H).mpr h_ab_H  },

  -- cas restants : h • a ≠ a, b ; h • b ≠ a,
  cases classical.em (h • b = b) with hb hb',
  { -- h • b = b
    use h • a,
    split, exact ha',
    split, exact hab',
    have : swap a (h • a) = (swap a b) * h * (swap a b) * h⁻¹ * (swap a b),
    { simp only [perm.smul_def],
      -- conjugation with (swap a b)
      apply (mul_right_inj (swap a b)).mp,
      apply (mul_left_inj (swap a b)⁻¹).mp,
      -- simplification of the LHS
      rw ← equiv.swap_apply_apply (swap a b) _ _ ,
      simp only [swap_apply_left, swap_inv],
      have : (swap a b) • (h • a) = h • a :=
        equiv.swap_apply_of_ne_of_ne ha' hab',
      simp only [perm.smul_def] at this,
      rw this,
      -- simplification of the RHS
      simp  [mul_assoc, equiv.mul_swap_mul_self, equiv.swap_mul_self_mul],
      rw ← mul_assoc,
      rw ← equiv.swap_apply_apply h a b,

      simp only [perm.smul_def] at hb,
      rw hb,
      rw equiv.swap_comm },
    rw this,

    -- ⊢ swap a b * h * swap a b * h⁻¹ * swap a b ∈ H
    apply subgroup.mul_mem H _ h_ab_H,
    apply subgroup.mul_mem H _ (subgroup.inv_mem H h_in_H),
    apply subgroup.mul_mem H _ h_ab_H,
    apply subgroup.mul_mem H h_ab_H h_in_H },

  -- cas restants : a, b, h • a, h • b  are pairwise distinct
  obtain ⟨c, hc⟩ := out_of_list α [a, b, h⁻¹ • a, h⁻¹ • b] _,
  swap,

  exact calc [h⁻¹ • a, h⁻¹ • b, a, b].length = 4 : by simp
    ... < 5 : nat.lt.base 4
    ... ≤ fintype.card α : hα,

  use c,

  split, -- c ≠ a
  { refine hc a _, apply list.mem_cons_self , },
  split, -- c ≠ b
  { refine hc b _, simp only [list.mem_cons_of_mem, list.mem_cons_self] },


  have ta : swap (h • a) (h • c) • a = a,
  { apply equiv.swap_apply_of_ne_of_ne,
    exact ne.symm ha',
    intro hca, specialize hc (h⁻¹ • a), rw hca at hc,
    simp only [perm.smul_def, perm.inv_apply_self, list.mem_cons_iff, true_or, eq_self_iff_true, not_true, ne.def, forall_true_left,
or_true] at hc,
    exact hc },

  have tb : swap (h • a) (h • c) • b = b,
  { apply equiv.swap_apply_of_ne_of_ne, exact ne.symm hab',
    intro hcb,
    have chb : c = h⁻¹ • b,
    { rw hcb , simp, },
    -- specialize hc (h⁻¹ • b), rw chb at hc,
    specialize hc ([a, b, h⁻¹ • a, h⁻¹ • b].last _),
    apply list.cons_ne_nil,
    simp only [perm.smul_def, list.mem_cons_iff, eq_self_iff_true, list.last, ne.def, forall_true_left, or_true, list.mem_singleton,
apply_eq_iff_eq] at hc,
    trivial,  },

  have tH : swap (h • a) (h • c) ∈ H,
  { apply  hH',
    simp only [mem_stabilizer_iff],
    rw has_smul.subpair_apply,
    rw ta, rw tb },

  have tconj : h * (swap a c) * h⁻¹ = swap (h • a) (h • c),
  { simp only [perm.smul_def],
    rw equiv.swap_apply_apply h _ _, },

  -- subgroup.mul_mem H x y : x ∈ H → y ∈ H → x * y ∈ H
  have tconj' : (swap a c) = h⁻¹ * swap (h • a) (h • c) * h,
  { rw ← tconj,
    rw mul_assoc,
    simp only [inv_mul_cancel_left, inv_mul_cancel_right] },

  rw tconj',
  apply subgroup.mul_mem H _ h_in_H,
  exact subgroup.mul_mem H (subgroup.inv_mem H h_in_H) tH
end


/-- The stabilizers of pairs of elements of α are maximal subgroups -/
theorem pairs_stabilizers_maximal (α : Type*) [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α) (x : action_on_pairs_of (perm α) α) :
  (stabilizer (perm α) x).is_maximal :=
begin
  apply subgroup.is_maximal_iff.mpr,
  split,
  -- stabilizer is not ⊤
  refine pairs_stabilizers_is_not_top α _ x,
  exact le_trans (le_trans (nat.le_succ 3) (nat.le_succ 4)) hα,

  -- no larger subgroup than stabilizer except ⊤
  { intros H h hH hh hhH,
    let w := stabilizer_of_sub_mul (perm α) (action_on_pairs_of (perm α) α) x,
    obtain ⟨a, b, hab, hx⟩ := x.prop,
    rw hx at w,
    rw w at hH hh,

    have hH' : stabilizer (perm α) {a,b} < H,
    { apply (set.ssubset_iff_of_subset hH).mpr,
      exact ⟨h, hhH, hh⟩ },

    obtain ⟨c, hca, hcb, hc⟩ :=
      pairs_stabilizers_maximal.has_swaps α hα
        a b hab
        H hH',

    apply top_unique,
    rw ← equiv.perm.closure_is_based_swap a,
    apply (subgroup.closure_le H).mpr,
    rintros f ⟨x, rfl⟩ ,
    rw set_like.mem_coe,
    cases classical.em (x = a) with ha ha,
    { -- x = a, swap a a = one,
      rw ha, simp only [swap_self, set_like.mem_coe],
      rw ← equiv.perm.one_def, exact subgroup.one_mem H },
    change x ≠ a at ha,
    cases classical.em (x = b) with hb hb,
    { -- x = b,
      rw hb,
      apply hH,
      exact pairs_stabilizers_maximal.has_swap' α a b },
    change x ≠ b at hb,
    -- x ≠ a, x ≠ b, using (c x) (a c) (c x) = (x a)
    rw swap_comm,
    rw ← swap_mul_swap_mul_swap hca.symm ha.symm,
    have hcx : swap c x ∈ H,
    { apply  hH,
      simp only [mem_stabilizer_iff, has_smul.subpair_apply,perm.smul_def],
      rw equiv.swap_apply_of_ne_of_ne hca.symm ha.symm,
      rw equiv.swap_apply_of_ne_of_ne hcb.symm hb.symm },
    apply subgroup.mul_mem H _ hcx,
    exact subgroup.mul_mem H hcx hc  }
end

-/



lemma simp_2m_n {m n : ℕ} (h : 2*m < n) : m < n-m :=
begin
  have h' : m ≤ n,
    apply le_of_lt,
    exact calc m ≤ m + m : by simp
          ...    ≤ 2 * m : by rw ← two_mul
          ...    < n : h ,

  refine lt_of_add_lt_add_right _,
  use m, rw ← two_mul,
  rw [add_comm, nat.add_sub_of_le h'],
  exact h,
end


-- variables {α : Type*} [decidable_eq α] [decidable_mem α] [fintype α]

-- TODO
lemma swaps_in_stabilizer {s : set α} {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  swap a b ∈ stabilizer (perm α) s :=
begin
  simp only [mem_stabilizer_iff],
  suffices : swap a b • s ⊆ s,
    apply set.subset.antisymm_iff.mpr,
    split, exact this,
    intros x hx,
    have this' : x = (swap a b) • ((swap a b) • x),
      rw ← mul_smul,
      simp only [perm.smul_def, perm.coe_one, id.def, swap_mul_self],
    have hx' : (swap a b) • x ∈ s,
      apply this,
      use x, exact ⟨hx, rfl⟩,
      rw this',
      use (swap a b) • x, exact ⟨hx', rfl⟩,
  rintros _ ⟨x, hx, rfl⟩,
  cases classical.em (x = a) with hxa hxa',
    rw hxa, simp only [swap_apply_left, perm.smul_def], exact hb,
    cases classical.em (x = b) with hxb hxb',
    rw hxb, simp only [swap_apply_right, perm.smul_def], exact ha,
    rw [perm.smul_def, equiv.swap_apply_of_ne_of_ne hxa' hxb'], exact hx,
end


theorem subset_stabilizer_ne_top (α : Type*) [decidable_eq α] [fintype α]
  (s : set α) (hs : s.nonempty) (hs' : sᶜ.nonempty) :
  (stabilizer (perm α) s) ≠ ⊤ :=
begin
  obtain ⟨a : α, ha : a ∈ s⟩ := hs,
  obtain ⟨b : α, hb : b ∈ sᶜ⟩ := hs',
  intro h,
  let g := equiv.swap a b,
  have h' : g ∈ ⊤ :=  subgroup.mem_top g,
  rw [← h , mem_stabilizer_iff] at h',
  rw set.mem_compl_eq at hb,
  apply hb,
  rw ← h',
  use a,
  exact and.intro ha (equiv.swap_apply_left a b)
end


lemma ne_stabilizer_of_finite_ne_incl (α : Type*)  -- [decidable_eq α] [fintype α]
  (s : set α) (hfs : s.finite)
  (h : perm α) (hH : h ∉ stabilizer (perm α) s):
  ∃ x, (x ∈ s) ∧ (h • x ∉ s) :=
begin
  have hfhs : (h • s).finite,
    change ((λ x, h • x) '' s).finite,
    exact set.finite.image (λ (x : α), h • x) hfs,

  rw mem_stabilizer_iff at hH,

  by_contradiction hK,
  simp only [not_exists, perm.smul_def, not_and, set.not_not_mem] at hK,
  apply hH,
  apply set.subset.antisymm,

  rintros _ ⟨x, hx, rfl⟩, rw perm.smul_def, exact hK x hx,

  intros x hx,

  obtain ⟨a, ha, rfl⟩ :=
  let f : Π (a : α), a ∈ hfs.to_finset → α := λ x hx, h • x
  in
  let hf : ∀ (a : α) (ha : a ∈ hfs.to_finset), f a ha ∈ hfs.to_finset := λ x hx,
  begin
    simp only [set.finite.mem_to_finset] at hx ⊢,
    exact hK x hx
  end
  in
  let hinj : ∀ (a₁ a₂ : α)  (ha₁ : a₁ ∈ hfs.to_finset) (ha₂ : a₂ ∈ hfs.to_finset),  f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂ :=
    λ a₁ a₂ ha₁ ha₂ heq, mul_action.injective h heq
  in
  let hst : hfs.to_finset.card ≤ hfs.to_finset.card := rfl.le
  in
  finset.surj_on_of_inj_on_of_card_le f hf hinj hst
    x ((set.finite.mem_to_finset hfs).mpr hx),

  use a,
  exact ⟨(set.finite.mem_to_finset hfs).mp ha, rfl⟩,
end

lemma set.ne_mem_compl_eq (s : set α) (x : α) : x ∉ sᶜ = (x ∈ s) :=
begin
  conv_rhs {rw ← compl_compl s},
  apply symm,
  exact set.mem_compl_eq sᶜ _,
end


/-- Stabilizers of nontrivial subsets s of α are maximal subgroups of perm α
provided 2 * s.to_finset.card < fintype.card α -/
theorem  subset_stabilizer_maximal (α : Type*) [decidable_eq α] [fintype α]
  (s : set α) (hs0 : s.nonempty) (h_2s_lt_top : 2 * s.to_finset.card < fintype.card α) :
  (stabilizer (perm α) s).is_maximal :=
begin
  have hs_le_sc : s.to_finset.card < (s.to_finset)ᶜ.card,
    rw finset.card_compl ,
    exact simp_2m_n  h_2s_lt_top,

  rw subgroup.is_maximal_iff,
  split,
    apply subset_stabilizer_ne_top α s hs0,
    suffices : (s.to_finset)ᶜ.nonempty,
      obtain ⟨x, hx⟩ := this,
      simp only [finset.mem_compl, set.mem_to_finset] at hx,
      use x,
    apply finset.card_pos.mp,
    apply lt_of_le_of_lt (zero_le s.to_finset.card),
    exact hs_le_sc,

  intros H h hSH hhS hhH,
  apply top_unique,
  rw ← equiv.perm.closure_is_swap,
  apply (subgroup.closure_le H).mpr,
  rintros σ ⟨a, b, ha_ne_b, rfl⟩,
  suffices : ∀(a b : α), ((a ∈ s ∧ b ∈ s) ∨ (a ∈ s ∧ b ∉ s) ∨ (a ∉ s ∧ b ∉ s))
      → swap a b ∈ H,
    cases classical.em (a ∈ s) with ha ha',
    cases classical.em (b ∈ s) with hb hb',
      apply this a b,
      apply or.intro_left, exact ⟨ha, hb⟩,
      apply this a b,
      apply or.intro_right, apply or.intro_left,  exact ⟨ha, hb'⟩,

    cases classical.em (b ∈ s) with hb hb',
      rw equiv.swap_comm ,
      apply this b a,
      apply or.intro_right, apply or.intro_left, exact ⟨hb, ha'⟩,
      apply this a b,
      apply or.intro_right, apply or.intro_right, exact ⟨ha', hb'⟩,

  intros a b hab,
  cases hab with hab hab',
  -- a ∈ s ∧ b ∈ s
    apply hSH,
    exact swaps_in_stabilizer hab.left hab.right,
  cases hab' with hab hab,
  swap,
  -- a ∉ s ∧ b ∉ s
    apply hSH,
    rw stabilizer_compl,
    exact swaps_in_stabilizer hab.left hab.right,

  -- a ∈ s ∧ b ∉ s
  have hhSc : h ∉ stabilizer (perm α) sᶜ,
    rw stabilizer_compl at hhS, exact hhS,

  -- we construct a transposition (a b) in H
  -- that maps some a ∈ s to some b ∉ s
   have : ∃(a b : α) (ha : a ∈ s) (hb : b ∉ s), swap a b ∈ H,
   { -- there is an element of sᶜ that is mapped to s
    -- this uses the hypothesis on h
    have this_x : ∃ x, x ∈ sᶜ ∧ h • x ∉ sᶜ,
    { apply ne_stabilizer_of_finite_ne_incl,
      exact set.finite.of_fintype sᶜ,
      rw stabilizer_compl at hhS,
      exact hhS },

    -- there is some element of sᶜ that is mapped to sᶜ
    -- only uses that s.card < sᶜ.card
    have this_y : ∃ y, y ∈ sᶜ ∧ h • y ∈ sᶜ,
    { by_contradiction hyp_H,
      simp only [not_and, not_exists] at hyp_H,
        apply not_le.mpr hs_le_sc,
        refine finset.card_le_card_of_inj_on _ _ _,
          exact λ x, h • x,
          { intros x hx,
            simp only [set.mem_to_finset],
            rw ← compl_compl s,
            apply set.mem_compl,
            apply hyp_H x,
            simpa using hx },
          { intros a₁ ha₁ a₂ ha₂ hf,
            exact mul_action.injective h hf } },

    -- h (x y) h⁻¹ = (hx hy) = (a b)
    obtain ⟨x, hx⟩ := this_x,
    obtain ⟨y, hy⟩ := this_y,
    use h • x, use h • y,
    simp only [exists_prop, perm.smul_def, set.not_not_mem, set.mem_compl_eq] at hx hy ⊢,
    apply and.intro hx.right,
    apply and.intro hy.right,

    rw equiv.swap_apply_apply,
    rw (subgroup.mem_conj_of_mem_iff H hhH),

    apply hSH,    rw stabilizer_compl,
    apply swaps_in_stabilizer,
    exact hx.left, exact hy.left },

  obtain ⟨a', b', ha', hb', this⟩ := this,

  have haa' : swap a a' ∈ H := hSH (swaps_in_stabilizer hab.left ha'),
  apply (subgroup.mem_conj_of_mem_iff H haa').mp,
  rw equiv.swap_inv,
  rw equiv.swap_comm a b,
  rw equiv.swap_mul_swap_mul_swap _ _,
   swap, -- b ≠ a
  { intro h, rw h at hab, exact hab.right hab.left, },
  swap, -- b ≠ a'
  { intro h, rw ← h at ha', exact hab.right ha', },

  have hbb' : swap b b' ∈ H,
  { rw stabilizer_compl at hSH,
    exact hSH (swaps_in_stabilizer (hab.right) hb') },
  apply (subgroup.mem_conj_of_mem_iff H hbb').mp,
  rw equiv.swap_inv,
  rw equiv.swap_mul_swap_mul_swap _ _,
  rw equiv.swap_comm, exact this,
  -- a' ≠ b,  bis repetita
  { intro h, rw h at ha', exact hab.right ha', },
  -- a' ≠ b',
  { intro h, rw h at ha', exact hb' ha', },
end

/-- If α has at least 5 elements, then
the stabilizers of pairs of elements of α are maximal subgroups -/
theorem pairs_stabilizers_maximal (α : Type*) [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α) (x : action_on_pairs_of (perm α) α) :
  (stabilizer (perm α) x).is_maximal :=
begin
  rw stabilizer_of_sub_mul,
  apply subset_stabilizer_maximal,

  apply (set.finite.to_finset.nonempty _).mp,
  apply finset.card_pos.mp,
  rw pair.card_eq_two x,
  simp only [nat.succ_pos'],

  have : (x : set α).to_finset = (pair.is_finite x).to_finset,
  { apply finset.coe_inj.mp,
    rw [set.finite.coe_to_finset, set.coe_to_finset], },
  rw [this, pair.card_eq_two x],
  exact le_trans (le_refl _) hα,
end

/-- If α has at least 5 elements, then
the action of the symmetric groups on pairs is primitive -/
def perm.action_on_pairs.primitive {α : Type*} [decidable_eq α] [fintype α] (hα : 5 ≤ fintype.card α) :
  is_primitive (perm α) (action_on_pairs_of (perm α) α) :=
{
is_nonempty :=
  begin
  have h1 : ∀ (a : α), [a].length < fintype.card α,
  { intro a,
    rw list.length_singleton _,
    refine lt_of_lt_of_le _ hα,
    simp only [nat.one_lt_succ_succ] },
  have h0 : ([] : list α).length < fintype.card α,
  { simp, refine lt_of_lt_of_le _ hα, refine nat.succ_pos',  },
  obtain ⟨a, ha⟩ := out_of_list α ([] : list α) h0,
  obtain ⟨b, hb⟩ := out_of_list α [a] (h1 a),
  have hab : b ≠ a,
    apply (hb a),
    simp only [list.mem_singleton],
  use (pair.mk hab),
end,
exists_smul_eq := transitive_on_pairs.exists_smul_eq ,
has_maximal_stabilizers := λ x,
begin
  refine pairs_stabilizers_maximal α hα x,
end
}

noncomputable
def pair.swap (x : action_on_pairs_of (perm α) α) : perm α :=
  swap (pair.lift x).1 (pair.lift x).2

def pair.swap.is_swap (x : action_on_pairs_of (perm α) α) :
  equiv.perm.is_swap (pair.swap x)  :=
begin
  use (pair.lift x).1, use (pair.lift x).2,
  split,
  exact pair.lift.ne x,
  refl,
end

def pair.apply_eq (g : perm α) (x : action_on_pairs_of (perm α) α) :
  (g • x : set α) = { g • ((pair.lift x).1) , g • ((pair.lift x).2) } :=
begin
  rw ← has_smul.subpair_apply,
  rw pair.lift.spec x,
 end

def pair.swap.swap_eq (x : action_on_pairs_of (perm α) α) {a b : α}
  (h : (x : set α) = {a, b}) : pair.swap x = swap a b :=
begin
  have : ({(pair.lift x).1, (pair.lift x).2 } : set α) = {a, b},
  { rw pair.lift.spec x at h, exact h,  },
  unfold pair.swap,
  cases subpair_eq_iff.mp this with H H,
  rw [H.left, H.right],
  rw [H.left, H.right, equiv.swap_comm]
end

def pair.swap.conj_swap (g : perm α) (x : action_on_pairs_of (perm α) α) :
  pair.swap (g • x) = (mul_aut.conj g).to_monoid_hom (pair.swap x) :=
begin
  unfold pair.swap,
  simp only [perm.smul_def, mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply],
  rw ← equiv.swap_apply_apply,
  apply pair.swap.swap_eq, apply pair.apply_eq,
end


/- Useless
/-- An Iwasawa structure on the product α × α -/
def perm.iwasawa (α : Type*) [decidable_eq α] [fintype α]:
Iwasawa_Criterion.has_iwasawa_structure (perm α) (α × α) :=
{ T := λ x, subgroup.closure { equiv.swap x.1 x.2 },
  is_comm := λ x, subgroup.closure.of_singleton_is_commutative (equiv.swap x.1 x.2),
  is_conj := λ g x,
  begin
    have : (mul_aut.conj g).to_monoid_hom '' ({swap x.1 x.2} : set (perm α))
      = { swap ((g • x).1) ((g • x).2) },
    { simp only [set.image_singleton, perm.smul_def, mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply, set.singleton_eq_singleton_iff],
      apply symm,
      apply equiv.swap_apply_apply,  },
    rw ← this,
    rw ← monoid_hom.map_closure (mul_aut.conj g).to_monoid_hom ({ swap x.1 x.2} : set (perm α)),
    simp only [subgroup.pointwise_smul_def,
    mul_distrib_mul_action.to_monoid_End_apply],
    refl,
  end,
  is_generator :=
  begin
    apply top_unique,
    rw ← closure_is_swap,
    let H := ⨆ (x : α × α), subgroup.closure {swap x.fst x.snd},
    -- refine w _,
    refine (subgroup.closure_le H).mpr _,
    intros σ hσ,
    obtain ⟨a,b, hab, rfl⟩ := hσ,
    refine subgroup.mem_supr_of_mem _ _,
    use ⟨a,b⟩,
    simp only,
    generalize : swap a b = σ,
    exact subgroup.subset_closure (set.mem_singleton σ),
  end,
}
-/

/-- An Iwasawa structure for (perm α) acting on pairs -/
def perm.iwasawa' (α : Type*) [decidable_eq α] [fintype α]:
Iwasawa_Criterion.has_iwasawa_structure (perm α) (action_on_pairs_of (perm α) α) :=
{ T := λ x, subgroup.closure ({ pair.swap x } : set (perm α)),
  is_comm := λ x, subgroup.closure.of_singleton_is_commutative _ ,
  is_conj := λ g x,
  begin
    have : { pair.swap (g • x) } = (mul_aut.conj g).to_monoid_hom '' ({ pair.swap x } : set (perm α)),
    { rw pair.swap.conj_swap g x,
      simp only [set.image_singleton],
    },
    rw this,
    rw ← monoid_hom.map_closure (mul_aut.conj g).to_monoid_hom ({ pair.swap x } : set (perm α)),
    simp only [subgroup.pointwise_smul_def,
    mul_distrib_mul_action.to_monoid_End_apply],
    refl
  end,
  is_generator :=
  begin
    apply top_unique,
    rw ← closure_is_swap,
    let H := ⨆ x, subgroup.closure {pair.swap x},
    refine (subgroup.closure_le H).mpr _,
    intros σ hσ,
    obtain ⟨a,b, hab, rfl⟩ := hσ,
    let x : action_on_pairs_of (perm α) α := ⟨({a,b} : set α), _ ⟩,
      swap,
      split, swap, use a, use b, split, exact hab, exact rfl,
    suffices : pair.swap x = swap a b,
      rw ← this,
      refine subgroup.mem_supr_of_mem x _,
      apply subgroup.subset_closure,
      apply set.mem_singleton,

    apply pair.swap.swap_eq x,
    simp only [subtype.coe_mk],
  end,
}

-- The main theorem, unfortunately weaker than expected
/-- If α has at least 5 elements, then
the only nontrivial normal sugroup of (perm α) is the alternating_group. -/
theorem perm.normal_subgroup {α : Type*} [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α)
  {N : subgroup (perm α)} (hnN : N.normal) (ntN : nontrivial N) : alternating_group α  ≤ N :=
begin
  rw ← alternating_group.is_commutator hα,
  refine Iwasawa_Criterion.Iwasawa_mk (perm α) (action_on_pairs_of (perm α) α) _ _ N hnN _,
  exact perm.action_on_pairs.primitive hα,
  exact perm.iwasawa' α ,

  intro h,
  obtain ⟨g, hgN, hg_ne⟩ := N.nontrivial_iff_exists_ne_one.mp ntN,
  obtain ⟨x, hx⟩ := faithful_on_pairs' α _ g hg_ne,
  swap,
    refine le_trans _ hα,
    simp only [bit1_le_bit1, nat.lt_one_iff, nat.one_le_bit0_iff],
  apply hx,
  let hx' := set.eq_univ_iff_forall.mp h x,
  simp at hx',

  change (subtype.mk g hgN) • x = x,
  apply hx' ,
end


/-
subtype.coe_mk : ∀ (a : ?M_1) (h : ?M_2 a), ↑⟨a, h⟩ = a
set_like.coe_mk : ∀ (x : ?M_2) (hx : x ∈ ?M_4), ↑⟨x, hx⟩ = x

set_like.mem_coe : ?M_5 ∈ ↑?M_4 ↔ ?M_5 ∈ ?M_4
set_like.coe_mem : ∀ (x : ↥?M_4), ↑x ∈ ?M_4

set_like.eta : ∀ (x : ↥?M_4) (hx : ↑x ∈ ?M_4), ⟨↑x, hx⟩ = x
-/

open list

lemma list.cycle_type_form_perm' (l : list α) (hl : l.nodup) (hn : 2 ≤ l.length) :
  l.form_perm.cycle_type = {l.length} :=
begin
  rw cycle_type_eq [l.form_perm],
  { simp only [map, function.comp_app],
    rw [support_form_perm_of_nodup _ hl, card_to_finset, erase_dup_eq_self.mpr hl],
    { simpa },
    { intros x h,
      simpa [h, nat.succ_le_succ_iff] using hn } },
  { simp },
  { simpa using is_cycle_form_perm hl hn },
  { simp }
end

namespace alternating_group

theorem subset_stabilizer_ne_top (α : Type*) [decidable_eq α] [fintype α]
  (s : finset α) (hs : s.nonempty) (hs' : sᶜ.card ≥ 2) :
  (stabilizer (alternating_group α) s) ≠ ⊤ :=
begin
  obtain ⟨a : α, ha : a ∈ s⟩ := hs,
  have : sᶜ.nonempty,
  { rw ← finset.card_pos, apply lt_of_lt_of_le _ hs', norm_num,},
  obtain ⟨b : α, hb : b ∈ sᶜ⟩ := this,
  have : ∃ (c : α), c ≠ b ∧ c ∈ sᶜ,
  { suffices : (sᶜ.erase b).nonempty,
      obtain ⟨c, hc⟩ := this,
      use c, rw ← finset.mem_erase, exact hc,
    rw ← finset.card_pos,
    apply lt_of_lt_of_le _ finset.pred_card_le_card_erase ,
    simp only [tsub_pos_iff_lt],
    apply lt_of_lt_of_le _ hs', norm_num },
  obtain ⟨c, hc', hc⟩ := this,
  rw finset.mem_compl at hb hc,
  let l := [a,b,c],
  have hl : l.nodup,
  -- g.is_cycle,
  { -- apply list.is_cycle_form_perm _, norm_num,
    rw list.nodup_cons, split,
    { intro habc,
      simp only [list.mem_cons_iff, list.mem_singleton] at habc,
      cases habc with h h,
        rw h at ha, exact hb ha,
        rw h at ha, exact hc ha,  },
    simp only [list.not_mem_nil, and_true, not_false_iff, list.nodup_cons, list.mem_singleton, list.nodup_nil],
    exact hc'.symm },
  let g := l.form_perm,
  have hg : g ∈ alternating_group α,
  { apply equiv.perm.is_three_cycle.mem_alternating_group ,
    rw equiv.perm.is_three_cycle,
    apply list.cycle_type_form_perm',
    exact hl, norm_num, },

  intro h,
  let hg' := subgroup.mem_top (⟨g,hg⟩ : alternating_group α),
  rw ← h at hg',
  rw @mem_stabilizer_iff (alternating_group α) _ _ _ _ _ at hg',
  unfold has_smul.smul at hg',
  simp only [perm.smul_def, submonoid.coe_subtype, has_smul.comp.smul, subgroup.coe_mk] at hg',
  apply hb, rw ← hg',
  rw finset.mem_image,
  use a, apply and.intro ha,
  rw list.form_perm_apply_mem_eq_next hl,
  norm_num,
  apply list.mem_cons_self
end

/-- Stabilizers of nontrivial subsets s of α are maximal subgroups of perm α
provided 2 * s.to_finset.card < fintype.card α -/
theorem  subset_stabilizer_maximal (α : Type*) [decidable_eq α] [fintype α]
  (s : finset α) (hs0 : s.nonempty) (h_2s_lt_top : 2 * s.card < fintype.card α) :
  (stabilizer (alternating_group α) s).is_maximal :=
begin
  have hs_le_sc : s.card < sᶜ.card,
    { rw finset.card_compl ,  exact simp_2m_n  h_2s_lt_top },
  rw subgroup.is_maximal_iff,
  split,
  { apply subset_stabilizer_ne_top,
    exact hs0,
    apply lt_of_le_of_lt _ hs_le_sc ,
    rw nat.succ_le_iff, exact finset.card_pos.mpr hs0 },

  sorry
end


theorem is_simple
  (hα : 5 ≤ fintype.card α) : is_simple_group (alternating_group α) :=
{exists_pair_ne :=
begin
  apply (alternating_group.nontrivial_of_three_le_card _).exists_pair_ne,
  apply le_trans _ hα,
  simp only [bit1_le_bit1, nat.lt_one_iff, nat.one_le_bit0_iff],
end,
  eq_bot_or_eq_top_of_normal := λ N nN,
begin
  sorry,
end}


/- Apparently, one cannot conclude by this method -/
theorem is_simple' {α : Type*} [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α) : is_simple_group (alternating_group α) :=
{ exists_pair_ne :=
begin
  apply (alternating_group.nontrivial_of_three_le_card _).exists_pair_ne,
  apply le_trans _ hα,
  simp only [bit1_le_bit1, nat.lt_one_iff, nat.one_le_bit0_iff],
end,
  eq_bot_or_eq_top_of_normal := λ N nN,
begin
  cases classical.em (N = ⊥) with htN hntN,
    exact or.intro_left _ htN,
  apply or.intro_right _,
  let j := subgroup.subtype (alternating_group α),
  let N' := subgroup.map j N,
  have hnN' : N'.normal,


  sorry,
end
}



end Iwasawa
