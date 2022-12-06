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

import .perm_iwasawa
import .alternating_maximal
import .V4

open_locale pointwise
-- open_locale classical

open mul_action


variables  {α : Type*} [fintype α] [decidable_eq α]

namespace alternating_group

lemma mul_aut_smul_subgroup_of_eq {G : Type*} [group G] {N H : subgroup G} (f : mul_aut G) (f' : mul_aut N)
  (hff' : ∀ (n : N), f n = f' n) :
  (f • H).subgroup_of N = f' • (H.subgroup_of N) :=
begin
  dsimp [has_smul.smul, mul_distrib_mul_action.to_monoid_hom],
  -- change (subgroup.map f.to_monoid_hom H).subgroup_of N = subgroup.map f'.to_monoid_hom _,
  ext,
  simp only [subgroup.mem_subgroup_of, subgroup.mem_map,
    mul_equiv.coe_to_monoid_hom, monoid_hom.coe_mk, exists_prop],
  split,
  { rintro ⟨y, hy, hyx⟩,
    use y,
    { -- y ∈ N
      suffices : y = (f'.symm x),
      { rw this, apply set_like.coe_mem, },
      rw [← mul_equiv.apply_eq_iff_eq f, hyx, hff', subtype.coe_inj,
        mul_equiv.apply_symm_apply], },
    apply and.intro hy,
    apply subtype.coe_injective,
    rw ← hff' _,
    exact hyx, },
  { rintro ⟨y, hy, rfl⟩,
    use ↑y,
    apply and.intro hy,
    apply hff', },
end

lemma Iw_conj_sign (s : finset α) (g : equiv.perm α) (k : equiv.perm s) :
  equiv.perm.sign ((Iw_conj s g) k) = equiv.perm.sign k :=
begin
  let e : s ≃ (g • s : finset α) :=
  begin
    apply equiv.subtype_equiv g,
    { intro a,
      rw [← finset.smul_mem_smul_finset_iff g, equiv.perm.smul_def], },
  end,
  suffices : ∀ k, (Iw_conj s g) k = (equiv.perm_congr e) k,
  { rw this,
    dsimp only [equiv.perm_congr, equiv.equiv_congr],
    simp only [equiv.coe_fn_mk],
    rw equiv.perm.sign_symm_trans_trans k e, },
  { intro k, refl, },
end

lemma Iw_conj_symm_sign   (s : finset α) (g : equiv.perm α) (k : equiv.perm (g • s : finset α)) :
  equiv.perm.sign ((Iw_conj s g).symm k) = equiv.perm.sign k :=
begin
  let e : s ≃ (g • s : finset α) :=
  begin
    apply equiv.subtype_equiv g,
    { intro a,
      rw [← finset.smul_mem_smul_finset_iff g, equiv.perm.smul_def], },
  end,
  suffices : ∀ k, (Iw_conj s g).symm k = (equiv.perm_congr e.symm) k,
  { rw this,
    dsimp only [equiv.perm_congr, equiv.equiv_congr],
    simp only [equiv.coe_fn_mk],
    rw equiv.perm.sign_symm_trans_trans k e.symm, },
  { intro k, refl, },
end


lemma Iw_is_conj_alt (s : finset α) (g : alternating_group α) :
  (subgroup.map
    (equiv.perm.of_subtype : equiv.perm ((g • s) : finset α) →* (equiv.perm α))
    (alternating_group ((g • s) : finset α))).subgroup_of (alternating_group α) =
  (mul_aut.conj g) •
  (subgroup.map
    (equiv.perm.of_subtype : equiv.perm s →* equiv.perm α)
    (alternating_group s)).subgroup_of (alternating_group α) :=
begin
  rw ← mul_aut_smul_subgroup_of_eq (mul_aut.conj ↑g) (mul_aut.conj g),
  apply congr_arg,

  suffices : subgroup.map (equiv.perm.of_subtype :
    equiv.perm (g • s : finset α) →* equiv.perm α) (alternating_group (g • s : finset α))
    = subgroup.map ((equiv.perm.of_subtype).comp (Iw_conj s g).to_monoid_hom)
      (alternating_group (s : finset α)),
  { rw this,
    change _ = subgroup.map (mul_aut.conj ↑g).to_monoid_hom _,
    rw subgroup.map_map,
    apply congr_arg2,
    apply Iw_is_conj',
    refl, },

  { simp only [← subgroup.map_map],
      apply congr_arg,
      ext k,
      simp only [subgroup.mem_map, equiv.perm.mem_alternating_group,
        mul_equiv.coe_to_monoid_hom, exists_prop],
      split,
      { intro hk,
        use (Iw_conj s ↑ g).symm k,
        simp only [Iw_conj_symm_sign, mul_equiv.apply_symm_apply],
        exact ⟨equiv.perm.mem_alternating_group.mp hk, rfl⟩, },

      { rintro ⟨x, hx, hx'⟩,
        rw ← hx',
        apply  equiv.perm.mem_alternating_group.mpr,
        simp only [Iw_conj_sign],
        exact hx, }, },

  { -- ∀ n…
   intro n, refl, },
end


lemma is_three_cycle_is_of_subtype (g : alternating_group α) (hg : equiv.perm.is_three_cycle (g : equiv.perm α)) :
  ∃ (s : finset α), (s.card = 3) ∧ g ∈ (subgroup.map
    (equiv.perm.of_subtype : equiv.perm s →* equiv.perm α)
    (alternating_group s)).subgroup_of (alternating_group α) :=
begin
  use (g : equiv.perm α).support,
  split,
  exact equiv.perm.is_three_cycle.card_support hg,
  rw subgroup.mem_subgroup_of,
  simp only [subgroup.mem_map],

  let k : equiv.perm (g : equiv.perm α).support := equiv.perm.subtype_perm (g : equiv.perm α) (λ a, by simp only [equiv.perm.apply_mem_support]),
  use k,
  suffices : equiv.perm.of_subtype k = g,
  split,
  -- because `rw equiv.perm.mem_alternating_group` does not work
  rw @equiv.perm.mem_alternating_group (g : equiv.perm α).support _ _,
  rw [← equiv.perm.sign_of_subtype, this],
  exact equiv.perm.is_three_cycle.sign hg,
  exact this,
  { -- k.of_subtype = g
    apply equiv.perm.of_subtype_subtype_perm,
    { intro a, simp only [equiv.perm.mem_support, imp_self] }, },
end


lemma subgroup.map_closure_eq {G H : Type*} [group G] [group H] (f : H →* G) (s : set H) :
  subgroup.map f (subgroup.closure s) = subgroup.closure (set.image f s) :=
begin
  apply symm,
  apply subgroup.closure_eq_of_le,
  { intro g, rintro ⟨k, hk, rfl⟩,
    exact ⟨k, subgroup.subset_closure hk, rfl⟩, },
  { rw subgroup.map_le_iff_le_comap,
    rw subgroup.closure_le ,
    intros g hg,
    simp only [subgroup.coe_comap, set.mem_preimage, set_like.mem_coe],
    apply subgroup.subset_closure,
    apply set.mem_image_of_mem, exact hg, },
end


lemma subgroup.closure_subgroup_of_eq {G : Type*} [group G] (N : subgroup G) (s : set G) (hs : s ≤ ↑N) :
  subgroup.closure (N.subtype ⁻¹' s) = (subgroup.closure s).subgroup_of N :=
begin
  dsimp only [subgroup.subgroup_of],
  have hN : function.injective N.subtype,
    by simp only [subgroup.coe_subtype, subtype.coe_injective],
  apply subgroup.map_injective hN,
  rw subgroup.map_closure_eq,
  suffices : (N.subtype) '' ((N.subtype) ⁻¹' s) = s,
  rw this,
  rw subgroup.map_comap_eq,
  simp only [subgroup.subtype_range, right_eq_inf, subgroup.closure_le],
  exact hs,

  rw [set.image_preimage_eq_inter_range, subgroup.coe_subtype, subtype.range_coe_subtype,
    set.inter_eq_left_iff_subset],
  exact hs,
end


lemma closure_three_cycles_alternating_eq_top :
  subgroup.closure
  { g : alternating_group α | equiv.perm.is_three_cycle (g : equiv.perm α)} = ⊤ :=
begin
  suffices : function.injective (alternating_group α).subtype,
  apply subgroup.map_injective this,
  rw subgroup.map_closure_eq,
  suffices : (alternating_group α).subtype '' { g : alternating_group α | equiv.perm.is_three_cycle (g : equiv.perm α)}
    = {g : equiv.perm α | equiv.perm.is_three_cycle g },
  rw this,
  rw equiv.perm.closure_three_cycles_eq_alternating,
  rw [← subgroup.comap_top _, subgroup.map_comap_eq, subgroup.subtype_range, inf_top_eq],
  { ext g,
    simp only [subgroup.coe_subtype, set.mem_image, set.mem_set_of_eq],
    split,
    rintro ⟨k, hk, rfl⟩, exact hk,
    intro hg,
    use g,
    rw equiv.perm.mem_alternating_group,
    exact equiv.perm.is_three_cycle.sign hg,
    exact ⟨hg, rfl⟩, },
  simp only [subgroup.coe_subtype, subtype.coe_injective],
end


lemma is_three_cycles_exists_of_subtype (g : alternating_group α) (hg : equiv.perm.is_three_cycle (g : equiv.perm α)) :
  ∃ (s : finset α), (s.card = 3) ∧ g ∈ (subgroup.map
    (equiv.perm.of_subtype : equiv.perm s →* equiv.perm α)
    (alternating_group s)).subgroup_of (alternating_group α) :=
begin
  use (g : equiv.perm α).support,
  split,
  exact equiv.perm.is_three_cycle.card_support hg,
  rw subgroup.mem_subgroup_of,
  simp only [subgroup.mem_map],

  let k : equiv.perm (g : equiv.perm α).support := equiv.perm.subtype_perm (g : equiv.perm α) (λ a, by simp only [equiv.perm.apply_mem_support]),
  use k,
  suffices : equiv.perm.of_subtype k = g,
  split,
  -- because `rw equiv.perm.mem_alternating_group` does not work
  rw @equiv.perm.mem_alternating_group (g : equiv.perm α).support _ _,
  rw [← equiv.perm.sign_of_subtype, this],
  exact equiv.perm.is_three_cycle.sign hg,
  exact this,
  { -- k.of_subtype = g
    apply equiv.perm.of_subtype_subtype_perm,
    { intro a, simp only [equiv.perm.mem_support, imp_self] }, },
end


lemma Iw_is_generator_alt : supr (λ (s : { s : finset α // s.card = 3}),
     (subgroup.map equiv.perm.of_subtype
      (alternating_group (s : finset α))).subgroup_of (alternating_group α)) =  ⊤ :=
begin
  rw ← closure_three_cycles_alternating_eq_top,
  have lemma1 : {g : alternating_group α | (g : equiv.perm α).is_three_cycle} =
    (alternating_group α).subtype ⁻¹' {g : equiv.perm α | g.is_three_cycle },
    { ext g, simp only [subgroup.coe_subtype, set.preimage_set_of_eq], },
  have lemma2 : {g : equiv.perm α | g.is_three_cycle} ≤ alternating_group α,
  { intros k hk,
    -- simp only [set_like.mem_coe],
    apply equiv.perm.is_three_cycle.mem_alternating_group,
    exact hk, },

  apply le_antisymm,
  { -- supr ≤ closure
    rw lemma1,
    rw subgroup.closure_subgroup_of_eq (alternating_group α) _ lemma2,
    rw equiv.perm.closure_three_cycles_eq_alternating,
    rw supr_le_iff,
    rintro ⟨s, hs⟩,
    dsimp only [subgroup.subgroup_of],
    refine subgroup.comap_mono _,
    intro g,
    rintro ⟨k, hk, rfl⟩,
    simp only [set_like.mem_coe] at hk,
    rw equiv.perm.mem_alternating_group,
    rw equiv.perm.sign_of_subtype,
    exact equiv.perm.mem_alternating_group.mp hk, },
  { -- closure ≤ supr
    rw subgroup.closure_le,
    intros g hg,
    obtain ⟨s, hs3, hsg⟩ := is_three_cycles_exists_of_subtype g hg,
    simp only [set_like.mem_coe],
    apply subgroup.mem_supr_of_mem,
    swap, exact ⟨s, hs3⟩,
    exact hsg, },
end


def Iw3 : iwasawa_structure (alternating_group α) (nat.finset α 3) :=
{ T := λ (s : nat.finset α 3), (subgroup.map
    (equiv.perm.of_subtype : equiv.perm (s : finset α) →* equiv.perm α)
    (alternating_group (s : finset α))).subgroup_of (alternating_group α),
  is_comm := λ ⟨s, hs⟩,
  begin
    apply subgroup.subgroup_of_is_commutative _,
    haveI : (alternating_group (s : finset α)).is_commutative := { is_comm :=
    begin
      apply alternating_group.is_commutative_of_order_three,
      rw fintype.card_coe, exact hs,
    end },
    apply subgroup.map_is_commutative (alternating_group (s : finset α)),
  end,
  is_conj := λ g ⟨s, hs⟩, Iw_is_conj_alt s g,
  is_generator := Iw_is_generator_alt,
}

example : Π {α : Type*} [fintype α] [decidable_eq α],
  by exactI subgroup (alternating_group α) :=
begin
  intros α _ _,
  exact ⊤,
end

example : Σ G : subgroup (alternating_group α), G := sorry

example : Σ G : subgroup (alternating_group α), Prop :=
sorry


def Iw3T : Π (σ : Type*) [fintype σ] [decidable_eq σ],
  (by exactI Π (hσ : nat.card σ = 3),
    (Σ (G : subgroup (alternating_group σ)), subgroup.normal G)) :=
begin
  intros σ _ _ hσ,
  resetI,
  exact subgroup.top_characteristic
end


def IwnT (n : ℕ) : Π (σ : Type*) [fintype σ] [decidable_eq σ],
  (by exactI Π (hσ : nat.card σ = n),
    subgroup.normal (alternating_group σ)) :=
begin
λ σ hσ
sorry
end

lemma finset.mem_doubleton_iff (a b x : α) : x ∈ ({a, b} : finset α) ↔ (x = a ∨ x = b) :=
begin
  rw [finset.mem_insert, finset.mem_singleton],
end


/-- If α has at least 5 elements, but not 6,
then the only nontrivial normal sugroup of (perm α) is the alternating_group. -/
theorem alternating_group.normal_subgroups {α : Type*} [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α) (hα' : fintype.card α ≠ 6)
  {N : subgroup (alternating_group α)} (hnN : N.normal) (ntN : nontrivial N) : N = ⊤ :=
begin
  rw eq_top_iff,
  rw ← alternating_group_is_perfect hα,

  have hprim : is_preprimitive (alternating_group α) (nat.finset α 3),
  { apply nat.finset_is_preprimitive_of_alt,
    norm_num,
    apply lt_of_lt_of_le _ hα, norm_num,
    exact hα', },
  apply commutator_le_iwasawa hprim Iw3 hnN ,

  -- N acts nontrivially
  intro h,
  obtain ⟨g, hgN, hg_ne⟩ := N.nontrivial_iff_exists_ne_one.mp ntN,
  have hg_ne' : (to_perm g : equiv.perm α) ≠ 1,
  { intro hg_ne', apply hg_ne,
    ext, simp only [subgroup.coe_one, ← hg_ne'],
    refl, },

  obtain ⟨s, hs⟩ := @nat.finset.mul_action_faithful α _ _ _ _ 3 _ _ _ g hg_ne',
  apply hs,
  suffices : s ∈ fixed_points N (nat.finset α 3),
  rw mem_fixed_points at this, exact this ⟨g, hgN⟩,
  rw h, rw set.top_eq_univ, apply set.mem_univ,
  norm_num,
  apply lt_of_lt_of_le _ hα, norm_num,
end

/-
def Iw4 : iwasawa_structure (alternating_group α) (nat.finset α 4) :=
{ T := λ (s : nat.finset α 4), (subgroup.map
    (equiv.perm.of_subtype : equiv.perm (s : finset α) →* equiv.perm α)
    (alternating_group (s : finset α))).subgroup_of (alternating_group α),
  is_comm := λ ⟨s, hs⟩,
  begin
    apply subgroup.subgroup_of_is_commutative _,
    haveI : (alternating_group (s : finset α)).is_commutative := { is_comm :=
    begin
      apply alternating_group.is_commutative_of_order_three,
      rw fintype.card_coe, exact hs,
    end },
    apply subgroup.map_is_commutative (alternating_group (s : finset α)),
  end,
  is_conj := λ g ⟨s, hs⟩, Iw_is_conj_alt s g,
  is_generator := Iw_is_generator_alt,
}
-/


/-- If α has at least 5 elements, but not 8,
then the only nontrivial normal sugroup of (perm α) is the alternating_group. -/
theorem alternating_group.normal_subgroups' {α : Type*} [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α) (hα' : fintype.card α ≠ 8)
  {N : subgroup (alternating_group α)} (hnN : N.normal) (ntN : nontrivial N) : N = ⊤ :=
begin
  rw eq_top_iff,
  rw ← alternating_group_is_perfect hα,

  have hprim : is_preprimitive (alternating_group α) (nat.finset α 4),
  { apply nat.finset_is_preprimitive_of_alt,
    norm_num,
    apply lt_of_lt_of_le _ hα, norm_num,
    exact hα', },
  apply commutator_le_iwasawa hprim Iw4 hnN ,

  -- N acts nontrivially
  intro h,
  obtain ⟨g, hgN, hg_ne⟩ := N.nontrivial_iff_exists_ne_one.mp ntN,
  have hg_ne' : (to_perm g : equiv.perm α) ≠ 1,
  { intro hg_ne', apply hg_ne,
    ext, simp only [subgroup.coe_one, ← hg_ne'],
    refl, },

  obtain ⟨s, hs⟩ := @nat.finset.mul_action_faithful α _ _ _ _ 3 _ _ _ g hg_ne',
  apply hs,
  suffices : s ∈ fixed_points N (nat.finset α 3),
  rw mem_fixed_points at this, exact this ⟨g, hgN⟩,
  rw h, rw set.top_eq_univ, apply set.mem_univ,
  norm_num,
  apply lt_of_lt_of_le _ hα, norm_num,
end



#exit

/-
def Iw_t (s : finset α) : (equiv.perm s) →* (equiv.perm α) := equiv.perm.of_subtype

def Iw_T (s : finset α) :=
  (subgroup.map (Iw_t s) (alternating_group s)).subgroup_of (alternating_group α)

example {G : Type*} [group G] (N : subgroup G) (hN : N.normal) :
  has_smul N (subgroup G) := {
smul := λ n K,  subgroup.map (mul_aut.conj ↑n).to_monoid_hom K
  }


example {G : Type*} [group G] (N : subgroup G) (hN : N.normal) :
  mul_action N (subgroup G) := {
    one_smul := sorry,
    mul_smul := sorry,
  }

/-
  f : G →* G
  N, K ≤ G
  j : N →* G


   f (j⁻¹ K) = j⁻¹ (f (K))
-/ -/


lemma map_comap_equiv {G : Type*} [group G] (N K : subgroup G) (f : G ≃* G) (f' : N ≃* N)
  (hff' : ∀ (y : N), f ↑y = f' y) :
  subgroup.map f'.to_monoid_hom (subgroup.comap N.subtype K) =
    subgroup.comap N.subtype (subgroup.map f.to_monoid_hom K)  :=
begin
  ext x,
  simp only [subgroup.mem_map, subgroup.mem_comap, subgroup.coe_subtype, exists_prop],
  split,
  { rintro ⟨y, hy, rfl⟩,
    use ↑y, apply and.intro hy,exact hff' y, },
  { rintro ⟨z, hz, hz'⟩,
    simp only [mul_equiv.coe_to_monoid_hom] at hz',
    use z,
--     use f'.symm x,
--    simp only [mul_equiv.coe_to_monoid_hom, mul_equiv.apply_symm_apply, eq_self_iff_true, and_true],
    { -- z ∈ N
      suffices : z = f'.symm x,
      rw this, apply set_like.coe_mem,
      apply mul_equiv.injective f,
      rw hz', rw hff', simp only [mul_equiv.apply_symm_apply],  },
    -- z ∈ K
    apply and.intro hz,
    -- f' z = x
    simp only [← subtype.coe_inj, ← hz', mul_equiv.coe_to_monoid_hom, ← hff'],
    refl, },
end


example {G : Type*} [group G] (N : subgroup G) (g : N) (K : subgroup G) :
  (mul_aut.conj g) • K.subgroup_of N = (mul_aut.conj (g : G) • K).subgroup_of N :=
begin
  change subgroup.map _ _ = (subgroup.map _ K).subgroup_of N,
  simp only [subgroup.subgroup_of],
  simp only [mul_distrib_mul_action.to_monoid_End_apply],
  apply map_comap_equiv,
  { intro y,refl, },
end


lemma IwT_is_conj (s : finset α) (g : alternating_group α) :
  Iw_T (g • s) = mul_aut.conj g • (Iw_T s) :=
begin
  unfold Iw_T,
  let ts := Iw_t s, let tgs := Iw_t (g • s),
  let Ts := Iw_T s, let Tgs := Iw_T (g • s),
  let kg : ↥s ≃ ↥(g • s) := equiv.subtype_equiv g (
    begin
      intro a,
      rw ← finset.smul_mem_smul_finset_iff g,
      refl,
    end),
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


  simp only [subgroup.subgroup_of],
  change _ = subgroup.map _ _,
  simp only [mul_distrib_mul_action.to_monoid_End_apply],
  change _ = subgroup.map (mul_aut.conj g).to_monoid_hom _,
  rw map_comap_equiv _ _
    (mul_aut.conj (g: equiv.perm α)) (mul_aut.conj g),
  apply congr_arg,
  rw subgroup.map_map,


  have : (mul_aut.conj ↑g).to_monoid_hom.comp (Iw_t s) =
    λ k, (Iw_t (↑g • s)) (Iw_c s ↑g k),

  ext,
  let hzz :=  Iw_conj' s ↑g,
  simp only [Iw_t] at hzz,

  sorry,
  {intro y, refl,},


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


  ext,
  split,
  rintro ⟨k,rfl⟩, use pg' k, conv_rhs {rw hpgg' k}, rw Iw_conj',
  rintro ⟨k, rfl⟩, use pg k, rw Iw_conj',


end

example (G : Type*) [group G] (H K : subgroup G) (hH : H.is_commutative) :
  (H.subgroup_of K).is_commutative :=
begin
  resetI,
  apply subgroup.subgroup_of_is_commutative H,
end
