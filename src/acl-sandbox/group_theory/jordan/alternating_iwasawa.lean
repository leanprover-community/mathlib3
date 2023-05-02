/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/


-- import tactic.basic tactic.group
-- import group_theory.solvable
import group_theory.group_action.sub_mul_action
import group_theory.specific_groups.alternating
import .for_mathlib.alternating
import .index_normal
import .primitive
import .multiple_transitivity
import .perm_iwasawa
import .alternating_maximal
import .V4

open_locale pointwise

open mul_action


lemma subgroup.smul_le_iff_le_inv_smul {G : Type*} [group G] (g : G) (H K : subgroup G) :
  mul_aut.conj g • H ≤ K ↔ H ≤ mul_aut.conj g⁻¹ • K :=
by simp only [← set_like.coe_subset_coe,subgroup.coe_pointwise_smul, map_inv, set.set_smul_subset_iff]

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

def subgroup.mul_equiv_of_mul_equiv {G G' : Type*} [group G] [group G'] (f : G ≃* G') {H : subgroup G} {H': subgroup G'} (h : ∀ g : G, g ∈ H ↔ f g ∈ H') : H ≃* H' :=
begin
  refine monoid_hom.to_mul_equiv _ _ _ _,
  { apply monoid_hom.cod_restrict (monoid_hom.restrict f.to_monoid_hom H) H',
    rintro ⟨g, hg⟩,
    simp only [monoid_hom.restrict_apply, subgroup.coe_mk, mul_equiv.coe_to_monoid_hom],
    rw ← h, exact hg, },
  { apply monoid_hom.cod_restrict (monoid_hom.restrict f.symm.to_monoid_hom H') H,
    rintro ⟨g', hg'⟩,
    rw h _,
    simp only [monoid_hom.restrict_apply, subgroup.coe_mk, mul_equiv.coe_to_monoid_hom, mul_equiv.apply_symm_apply],
    exact hg', },
  { ext, simp, },
  { ext, simp, },
end

variables  {α : Type*} [fintype α] [decidable_eq α]

namespace equiv.perm

def Iw_conj (s : finset α) (g : equiv.perm α) : equiv.perm s ≃* equiv.perm ((g • s) : finset α) :=
{ map_mul' := λ h k, equiv.ext (λ x, by simp only [equiv.to_fun_as_coe, equiv.perm_congr_apply,
    equiv.subtype_equiv_symm, equiv.subtype_equiv_apply, equiv.perm.coe_mul,
    function.comp_app, subtype.coe_mk, equiv.symm_apply_apply, finset.mk_coe])
  ..
  equiv.perm_congr (@equiv.subtype_equiv α α (λ a, a ∈ s) (λ a, a ∈ g • s) (g : α ≃ α)
  ((λ a, by rw [← finset.smul_mem_smul_finset_iff g, equiv.perm.smul_def]) :
    ∀ (a : α), a ∈ s ↔ g a ∈ g • s)) }

def Iw_conj' {s t : finset α} {g : equiv.perm α} (htgs : t = g • s) : equiv.perm s ≃* equiv.perm t := {
map_mul' := λ h k, equiv.ext (λ x, by simp only [equiv.to_fun_as_coe, equiv.perm_congr_apply,
    equiv.subtype_equiv_symm, equiv.subtype_equiv_apply, equiv.perm.coe_mul,
    function.comp_app, subtype.coe_mk, equiv.symm_apply_apply, finset.mk_coe])
..
equiv.perm_congr (@equiv.subtype_equiv α α _ _ (g : α ≃ α)
  (begin
    intro a,
    rw [htgs, ← equiv.perm.smul_def, ← finset.smul_mem_smul_finset_iff g]
  end)) }

lemma Iw_conj'_trans {s t u : finset α} {g k : equiv.perm α}
  (htgs : t = g • s) (hukt : u = k • t) :
  let hukgs : u = (k * g) • s := by rw [mul_smul, ← htgs, hukt]
in  (Iw_conj' htgs).trans (Iw_conj' hukt) = Iw_conj' hukgs :=
begin
  intro hukgs,
  refl,
end

lemma Iw_conj'_symm {s t : finset α} {g : equiv.perm α} (htgs : t = g • s) :
  let hsg't : s = g⁻¹ • t := by rw [htgs, inv_smul_smul]
in  (Iw_conj' htgs).symm = Iw_conj' hsg't :=
begin
  intro hsg't,
  refl,
end

lemma Iw_conj'_eq_apply {s t : finset α} {g : equiv.perm α} (htgs : t = g • s) (k : equiv.perm s) :
  ((mul_aut.conj g).to_monoid_hom.comp (equiv.perm.of_subtype : (equiv.perm s) →* (equiv.perm α)) k) =
  (equiv.perm.of_subtype : equiv.perm t →* equiv.perm α) (Iw_conj' htgs k) :=
begin
  dsimp only [Iw_conj'],
  ext x,
  simp only [monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, function.comp_app, mul_aut.conj_apply, coe_mul, equiv.to_fun_as_coe,
  mul_equiv.coe_mk],
  cases em (x ∈ t) with hx hx,
  { -- x ∈ t
    rw equiv.perm.of_subtype_apply_of_mem,
    rw equiv.perm.of_subtype_apply_of_mem,
    refl, exact hx, },
  { -- x ∉ t
    rw equiv.perm.of_subtype_apply_of_not_mem,
    rw equiv.perm.of_subtype_apply_of_not_mem,
    simp only [apply_inv_self],
    exact hx,
    rw [htgs, ← finset.inv_smul_mem_iff] at hx,
    exact hx, }
end

lemma Iw_conj'_eq {s t : finset α} {g : equiv.perm α} (htgs : t = g • s) :
equiv.perm.of_subtype.comp (Iw_conj' htgs).to_monoid_hom =
    ((mul_aut.conj g).to_monoid_hom).comp equiv.perm.of_subtype :=
begin
  ext k x,
  rw Iw_conj'_eq_apply,
  refl,
end

lemma Iw_conj_eq (s : finset α) (g : equiv.perm α )(k : equiv.perm ↥s) :
  ((mul_aut.conj g).to_monoid_hom.comp
    (equiv.perm.of_subtype :(equiv.perm s) →* (equiv.perm α)) k)  =
  (equiv.perm.of_subtype : equiv.perm ((g • s) : finset α) →* (equiv.perm α)) (Iw_conj s g k) :=
begin
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

lemma Iw_conj'_sign {s t : finset α} {g : equiv.perm α} (htgs : t = g • s) (k : equiv.perm s):
  ((Iw_conj' htgs) k).sign = k.sign :=
begin
  dsimp only [Iw_conj', equiv.perm_congr, equiv.equiv_congr],
  refine equiv.perm.sign_symm_trans_trans k _,
end

lemma Iw_conj_symm'_sign {s t : finset α} {g : equiv.perm α} (htgs : t = g • s) (k : equiv.perm t):
  ((Iw_conj' htgs).symm k).sign = k.sign :=
begin
  conv_rhs { rw ← mul_equiv.apply_symm_apply (Iw_conj' htgs) k, },
  rw Iw_conj'_sign,
/-  dsimp only [Iw_conj', equiv.perm_congr, equiv.equiv_congr],
  refine equiv.perm.sign_symm_trans_trans k _, -/
end

lemma Iw_conj_sign (s : finset α) (g : equiv.perm α) (k : equiv.perm s) :
  equiv.perm.sign ((Iw_conj s g) k) = equiv.perm.sign k :=
begin
  dsimp only [Iw_conj, equiv.perm_congr, equiv.equiv_congr],
  refine equiv.perm.sign_symm_trans_trans k _,
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


end equiv.perm

namespace alternating_group

open equiv.perm

def subgroup.equiv_mk {G G' : Type*} [group G] [group G'] (e : G ≃* G') {H : subgroup G} {H' : subgroup G'} (h : ∀ g : G, g ∈ H ↔ e g ∈ H') : H ≃* H' := {
to_fun := λ g, ⟨e g, (h g).mp g.prop⟩,
inv_fun := λ g', ⟨e.symm g', (h _).mpr (by simp only [mul_equiv.apply_symm_apply, set_like.coe_mem])⟩,
left_inv := λ g, by simp only [subgroup.coe_mk, mul_equiv.symm_apply_apply, set_like.eta],
right_inv := λ g', by simp only [mul_equiv.apply_symm_apply, subgroup.coe_mk, set_like.eta],
map_mul' := λ x y, by simp only [subgroup.coe_mul, map_mul, mul_mem_class.mk_mul_mk], }

def Iw_conj' {s t : finset α} {g : equiv.perm α} (htgs : t = g • s) :
  alternating_group s ≃* alternating_group t := subgroup.equiv_mk (equiv.perm.Iw_conj' htgs)
  (λ k, by simp only [equiv.perm.mem_alternating_group, equiv.perm.Iw_conj'_sign])

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
    = subgroup.map ((equiv.perm.of_subtype).comp (equiv.perm.Iw_conj s g).to_monoid_hom)
      (alternating_group (s : finset α)),
  { rw this,
    change _ = subgroup.map (mul_aut.conj ↑g).to_monoid_hom _,
    rw subgroup.map_map,
    apply congr_arg2,
    apply equiv.perm.Iw_is_conj',
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
  is_generator := Iw_is_generator_alt, }

/-- If α has at least 5 elements, but not 6, then
the only nontrivial normal sugroup of (alternating_group α) is the alternating_group itself. -/
theorem is_normal_subgroup_iff_of_ne_6 {α : Type*} [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α) (hα' : fintype.card α ≠ 6)
  {N : subgroup (alternating_group α)} (hnN : N.normal) :
  N = ⊥ ∨ N = ⊤ :=
begin
  cases subgroup.bot_or_nontrivial N with hN hN,
  apply or.intro_left, exact hN,
  apply or.intro_right,
  rw eq_top_iff,
  rw ← alternating_group_is_perfect hα,
  apply commutator_le_iwasawa _ Iw3 hnN _,
  { apply is_preprimitive.is_quasipreprimitive,
    apply alternating_group.nat.finset_is_preprimitive_of_alt 3,
    norm_num,
    exact lt_of_lt_of_le (by norm_num) hα,
    exact hα', },
  { intro h,
    obtain ⟨g, hgN, hg⟩ := N.nontrivial_iff_exists_ne_one.mp hN,
    obtain ⟨s, hs⟩ := nat.finset.mul_action_faithful 3 (by norm_num) _ _,
    apply hs,
    suffices : s ∈ fixed_points N (nat.finset α 3),
    rw mem_fixed_points at this, exact this ⟨g, hgN⟩,
    rw h, rw set.top_eq_univ, apply set.mem_univ,
    apply_instance,
    exact lt_of_lt_of_le (by norm_num) hα,
    intro hg', apply hg,
    ext, simp only [subgroup.coe_one, ← hg'], refl, },
end

def Iw4T (s : finset α) : subgroup (alternating_group α) :=
 (subgroup.map (monoid_hom.comp ((equiv.perm.of_subtype : equiv.perm (s : finset α) →* equiv.perm α)) (alternating_group (s : finset α)).subtype) (commutator (alternating_group (s : finset α)))).subgroup_of (alternating_group α)

def alternating_group.of_subtype {α : Type*} [decidable_eq α] [fintype α] {s : finset α} :
alternating_group s →* alternating_group α :=
begin
  apply monoid_hom.cod_restrict
    (monoid_hom.restrict (equiv.perm.of_subtype) (alternating_group s)),
  intro k,
  simpa only [mem_alternating_group, monoid_hom.restrict_apply, sign_of_subtype] using k.prop,
end

def Iw4T' (s : finset α) : subgroup (alternating_group α) :=
  subgroup.map (alternating_group.of_subtype) (commutator (alternating_group s))

lemma Iw4T'_is_conj (g : alternating_group α) (s : finset α) :
  Iw4T' (g • s : finset α) = mul_aut.conj g • (Iw4T' s) :=
begin
  dsimp [Iw4T'],
  simp only [commutator, subgroup.map_commutator],
  change _ = subgroup.map (mul_aut.conj g).to_monoid_hom _,

  have htop : ⊤ = subgroup.map (Iw_conj' (rfl : g • s = g • s)).to_monoid_hom ⊤,
  { rw subgroup.map_top_of_surjective, exact mul_equiv.surjective _, },
  simp only [htop, subgroup.map_map, subgroup.map_commutator],

  suffices,
  refine congr_arg2 _ this this,
  { apply congr_arg2,
    ext ⟨k, hk⟩ x,
    dsimp only [Iw_conj', subgroup.equiv_mk, alternating_group.of_subtype],
    simp only [monoid_hom.comp_apply],
    dsimp,
    rw ←  equiv.perm.Iw_conj'_eq_apply, refl,
    refl, },
end

lemma Iw4T_is_conj (g : (alternating_group α)) (s : finset α) (hs : s.card = 4) :
  Iw4T (g • s : finset α) = mul_aut.conj g • (Iw4T s) :=
begin
  dsimp [Iw4T],
  rw ← mul_aut_smul_subgroup_of_eq (mul_aut.conj ↑g) (mul_aut.conj g),
  apply congr_arg,
  change _ = subgroup.map (mul_aut.conj ↑g).to_monoid_hom _,
  simp only [subgroup.map_map],
  simp only [commutator, subgroup.map_commutator],
  suffices : subgroup.map (equiv.perm.of_subtype.comp (alternating_group ↥(g • s)).subtype) ⊤
   = subgroup.map
  ((mul_equiv.to_monoid_hom (mul_aut.conj ↑g)).comp (equiv.perm.of_subtype.comp (alternating_group ↥s).subtype))
  ⊤,
  rw this,
  have hg : g • s = g • s, refl,
  suffices : (equiv.perm.of_subtype.comp (alternating_group ↥(g • s)).subtype).comp
    (Iw_conj' hg).to_monoid_hom = ((mul_equiv.to_monoid_hom (mul_aut.conj ↑g)).comp (equiv.perm.of_subtype.comp (alternating_group ↥s).subtype)),
  rw ← this,
  conv_rhs { rw ← subgroup.map_map, },
  apply congr_arg2,
  refl,
  rw subgroup.map_top_of_surjective ,
  exact mul_equiv.surjective _,

  { ext ⟨k, hk⟩ x, dsimp only [Iw_conj', subgroup.equiv_mk],
    simp only [monoid_hom.comp_apply],
    dsimp,
    rw ←  equiv.perm.Iw_conj'_eq_apply, refl, },

  { intro n, refl, },
end

open equiv.perm equiv alternating_group subgroup

lemma is_swap_iff_cycle_type_eq {g : equiv.perm α} : g.is_swap ↔ g.cycle_type = {2} :=
begin
  split,
  { intro hg,
    rw equiv.perm.is_cycle.cycle_type (equiv.perm.is_swap.is_cycle hg),
    rw ← card_support_eq_two at hg,
    rw hg,
    simp only [multiset.coe_singleton], },
  { intro hg,
    suffices hg' : g.is_cycle,
    rw equiv.perm.is_cycle.cycle_type hg' at hg,
    simp only [multiset.coe_singleton, multiset.singleton_inj, card_support_eq_two] at hg,
    exact hg,
    simp only [← equiv.perm.card_cycle_type_eq_one, hg, multiset.card_singleton], }
end

lemma is_swap_eq' {g : equiv.perm α} (hg : is_swap g) {a : α} (ha : a ∈ g.support) :
   g = equiv.swap a (g a) :=
begin
  obtain ⟨x, y, hxy, h⟩ := hg,
  rw [equiv.perm.mem_support, h, equiv.swap_apply_ne_self_iff] at ha,
/-  wlog hx : a = x using [x y, y x],
  exact ha.2,
  { suffices hy : y = g a,
    rw [← hy, hx, h],
    rw [h, hx, swap_apply_left], },
  apply this (ne.symm hxy),
  rw [equiv.swap_comm, h],
  exact ⟨ne.symm ha.1, or.symm ha.2⟩, -/
  cases ha.2 with hx hy,
  { suffices hy : y = g a,
    rw [← hy, hx, h],
    rw [h, hx, swap_apply_left], },
  { suffices hx : x = g a,
    rw [← hx, hy, equiv.swap_comm, h],
    rw [h, ← equiv.swap_apply_eq_iff , swap_apply_left, hy], },
end

lemma swap_mul_swap_mem (hα : 5 ≤ fintype.card α) {g k : equiv.perm α}
  (hg : is_swap g) (hk : is_swap k)  :
  g * k ∈ subgroup.closure { g : equiv.perm α | g.cycle_type = {2,2} } :=
begin
  suffices hdis : ∀ {g k : equiv.perm α} (hg : is_swap g) (hk : is_swap k) (hgk : g.disjoint k),
      g * k ∈ subgroup.closure { g : equiv.perm α | g.cycle_type = {2,2} },

  by_cases h22 : g.disjoint k,
  -- case disjoint
  exact hdis hg hk h22,
  -- case not disjoint
  rw [equiv.perm.disjoint_iff_disjoint_support, finset.not_disjoint_iff] at h22,
  obtain ⟨a, hag, hak⟩ := h22,
  rw is_swap_eq' hg hag, rw is_swap_eq' hk hak,
  by_cases h1 : k a = g a,
  { rw h1, rw equiv.swap_mul_self , refine subgroup.one_mem _, },
  { suffices : ∃ (b c : α), b ∉ ({a, g a, k a} : finset α) ∧ c ∉ ({a, g a, k a} : finset α) ∧ b ≠ c,
    obtain ⟨b, c, hb, hc, hbc⟩ := this,
    simp only [finset.mem_insert, finset.mem_singleton] at hb hc,
    simp only [not_or_distrib] at hb hc,
    rw ← one_mul (swap a (k a)),
    rw ← equiv.swap_mul_self b c,
    nth_rewrite 0 mul_assoc, rw ← mul_assoc,
    refine subgroup.mul_mem _ _ _,
    { rw equiv.perm.mem_support at hag,
      apply hdis _ _,
      rw [disjoint_iff_disjoint_support, equiv.perm.support_swap _, equiv.perm.support_swap _],
      simp only [finset.disjoint_insert_right, finset.mem_insert,
        finset.mem_singleton, finset.disjoint_insert_left,
        finset.disjoint_singleton, ne.def, not_or_distrib],
      exact ⟨⟨ne.symm hb.1, ne.symm hc.1⟩, ⟨hb.2.1, ne.symm hc.2.1⟩⟩,
      exact hbc,
      exact ne.symm hag,
      exact ⟨a, g a, ne.symm hag, rfl⟩,
      exact ⟨b, c, hbc, rfl⟩, },
    { rw equiv.perm.mem_support at hak,
      apply hdis _ _,
      rw [disjoint_iff_disjoint_support, equiv.perm.support_swap _, equiv.perm.support_swap _],
      simp only [finset.disjoint_insert_right, finset.mem_insert,
        finset.mem_singleton, finset.disjoint_insert_left,
        finset.disjoint_singleton, ne.def, not_or_distrib],
      exact ⟨⟨hb.1, hb.2.2⟩, ⟨ne.symm hc.1, hc.2.2⟩⟩,
      exact ne.symm hak,
      exact hbc,
      exact ⟨b, c, hbc, rfl⟩,
      exact ⟨a, k a, ne.symm hak, rfl⟩, },
    { simp_rw ← finset.mem_compl,
      rw ← finset.one_lt_card_iff,
      rw finset.card_compl ,
      rw nat.lt_iff_add_one_le,
      apply le_tsub_of_add_le_right,
      apply le_trans _ hα,
      suffices : finset.card {a, g a, k a} ≤ 3,
      apply le_trans (add_le_add_left this 2), norm_num,
      apply le_trans (finset.card_insert_le _ _), rw nat.succ_le_succ_iff ,
      apply le_trans (finset.card_insert_le _ _), rw nat.succ_le_succ_iff ,
      simp only [finset.card_singleton], } },
  -- hdis
  { intros g k hg hk h22,
    apply subgroup.subset_closure, simp only [set.mem_set_of_eq],
    rw equiv.perm.disjoint.cycle_type h22,
    rw is_swap_iff_cycle_type_eq at hg hk,
    rw [hg, hk, multiset.singleton_add, multiset.insert_eq_cons], },
end

lemma closure_perm22_eq_top (hα : 5 ≤ fintype.card α) :
  subgroup.closure  { g : equiv.perm α | g.cycle_type = {2,2} } = alternating_group α :=
begin
  apply subgroup.closure_eq_of_le,
  { intros g hg,
    simp only [set_like.mem_coe, mem_alternating_group, equiv.perm.sign_of_cycle_type],
    simp only [set.mem_set_of_eq] at hg,
    rw hg, norm_num, },
  suffices hind : ∀ (n : ℕ) (l : list (equiv.perm α)) (hl : ∀ g, g ∈ l → is_swap g)
    (hn : l.length = 2 * n), l.prod ∈ subgroup.closure {σ : perm α | σ.cycle_type = {2,2}},
  { intros g hg,
    obtain ⟨l, rfl, hl⟩ := trunc_swap_factors g,
    obtain ⟨n, hn⟩ := (prod_list_swap_mem_alternating_group_iff_even_length hl).1 hg,
    rw ← two_mul at hn,
    exact hind n l hl hn, },
  intro n,
  induction n with n hrec,
  { intros l hl hn,
    simp only [nat.nat_zero_eq_zero, mul_zero, list.length_eq_zero] at hn,
    rw [hn, list.prod_nil],
    refine one_mem _, },
  { intros l hl hn,
    suffices : 2 * n.succ = (2 * n).succ.succ,
    rw this at hn,
    obtain ⟨a, l1, rfl⟩ := l.exists_of_length_succ hn,
    simp only [list.length, nat.succ_inj'] at hn,
    obtain ⟨b, l2, rfl⟩ := l1.exists_of_length_succ hn,
    simp only [list.length, nat.succ_inj'] at hn,
    simp only [list.prod_cons, ← mul_assoc],
    refine subgroup.mul_mem _ _ _,
    { simp only [list.mem_cons_iff, forall_eq_or_imp] at hl,
      /- obtain ⟨a1, a2, ha, rfl⟩ := hl.1,
      obtain ⟨b1, b2, hb, rfl⟩ := hl.2.1, -/
      exact swap_mul_swap_mem hα hl.1 hl.2.1, },
    refine hrec l2 _ hn,
    { intros g hg, apply hl g, apply list.mem_cons_of_mem,
      apply list.mem_cons_of_mem, exact hg, },
    rw nat.mul_succ,  },
end



lemma closure_perm22_alternating_eq_top (hα : 5 ≤ fintype.card α):
  subgroup.closure
  { g : alternating_group α | (g : equiv.perm α).cycle_type = {2, 2} } = ⊤ :=
begin
  suffices : function.injective (alternating_group α).subtype,
  apply subgroup.map_injective this,
  rw subgroup.map_closure_eq,
  suffices : (alternating_group α).subtype ''
    { g : alternating_group α | (g : equiv.perm α).cycle_type = {2, 2}}
    = {g : equiv.perm α | g.cycle_type = {2, 2} },
  rw this,
  rw closure_perm22_eq_top hα,
  rw [← subgroup.comap_top _, subgroup.map_comap_eq, subgroup.subtype_range, inf_top_eq],
  { ext g,
    simp only [subgroup.coe_subtype, set.mem_image, set.mem_set_of_eq],
    split,
    rintro ⟨k, hk, rfl⟩, exact hk,
    intro hg,
    use g,
    rw equiv.perm.mem_alternating_group,
    rw equiv.perm.sign_of_cycle_type, rw hg, norm_num,
    exact ⟨hg, rfl⟩, },
  simp only [subgroup.coe_subtype, subtype.coe_injective],
end


lemma is_perm22_exists_of_subtype (g : alternating_group α) (hg : (g : equiv.perm α).cycle_type = {2, 2} ) :
  ∃ (s : finset α), (s.card = 4) ∧ g ∈ Iw4T s :=
begin
  have hs4 : (g : equiv.perm α).support.card = 4,
  { rw ← equiv.perm.sum_cycle_type, rw hg, refl, },

  use (g : equiv.perm α).support,
  apply and.intro hs4,
  simp only [Iw4T],

  rw subgroup.mem_subgroup_of,
  simp only [subgroup.mem_map],

  let k : equiv.perm (g : equiv.perm α).support := equiv.perm.subtype_perm (g : equiv.perm α) (λ a, by simp only [equiv.perm.apply_mem_support]),
  suffices : equiv.perm.of_subtype k = g,
  use k,
  simp only [mem_alternating_group],
  rw ← equiv.perm.sign_of_subtype , rw this,
  rw equiv.perm.sign_of_cycle_type, rw hg, refl,

  split,
  rw ← V4_eq_commutator,
  rw ← subgroup.mem_carrier,
  rw V4_carrier_eq,
  apply or.intro_right,
  rw subgroup.coe_mk,
  rw ← equiv.perm.cycle_type_of_subtype,
  rw this,
  exact hg,

  simp only [fintype.card_coe, hs4],
  simp only [fintype.card_coe, hs4],

  simp only [monoid_hom.coe_comp, subgroup.coe_subtype, function.comp_app, subgroup.coe_mk],
  exact this,

  { -- k.of_subtype = g
    apply equiv.perm.of_subtype_subtype_perm,
    { intro a, simp only [equiv.perm.mem_support, imp_self] }, },
end


lemma Iw4_is_generator_alt (hα : 5 ≤ fintype.card α) :
  supr (λ (s : nat.finset α 4), Iw4T (s : finset α)) =  ⊤ :=
--  supr (λ (s : { s : finset α // s.card = 4}), Iw4T (s : finset α)) =  ⊤ :=
begin
  rw ← closure_perm22_alternating_eq_top hα,
  have lemma1 : {g : alternating_group α | (g : equiv.perm α).cycle_type = {2, 2} } =
    (alternating_group α).subtype ⁻¹' {g : equiv.perm α | g.cycle_type = {2, 2} },
    { ext g, simp only [subgroup.coe_subtype, set.preimage_set_of_eq], },
  have lemma2 : {g : equiv.perm α | g.cycle_type = {2, 2}} ≤ alternating_group α,
  { intros k hk,
    -- simp only [set_like.mem_coe],
    simp only [set.mem_set_of_eq] at hk,
    simp only [set_like.mem_coe, mem_alternating_group, equiv.perm.sign_of_cycle_type, hk],
    norm_num, },

  apply le_antisymm,
  { -- supr ≤ closure
    rw lemma1,
    rw subgroup.closure_subgroup_of_eq (alternating_group α) _ lemma2,
    rw closure_perm22_eq_top hα,
    rw supr_le_iff,
    rintro ⟨s, hs⟩,
    dsimp only [subgroup.subgroup_of],
    refine subgroup.comap_mono _,
    intro g,
    rintro ⟨k, hk, rfl⟩,
    simp only [set_like.mem_coe] at hk,
    rw equiv.perm.mem_alternating_group,
    simp only [monoid_hom.coe_comp, subgroup.coe_subtype, sign_of_subtype],
    simpa only using subtype.prop k, },
  { -- closure ≤ supr
    rw subgroup.closure_le,
    intros g hg,
    obtain ⟨s, hs4, hsg⟩ := is_perm22_exists_of_subtype g hg,
    simp only [set_like.mem_coe],
    apply subgroup.mem_supr_of_mem,
    swap, exact ⟨s, hs4⟩,
    exact hsg, },
end

def Iw4 (hα : 5 ≤ fintype.card α) : iwasawa_structure (alternating_group α) (nat.finset α 4) :=
{ T := λ s, Iw4T (s : finset α),
  is_comm := λ ⟨s, hs⟩,
  begin
    have hs' : fintype.card (s : finset α) = 4,
    { rw fintype.card_coe, exact hs, },
    apply subgroup.subgroup_of_is_commutative _,
    haveI: (commutator (alternating_group (s : finset α))).is_commutative,
    { rw ← V4_eq_commutator _ hs',
      apply V4_is_commutative _ hs', },
    apply subgroup.map_is_commutative  (commutator (alternating_group (s : finset α))),
  end,
  is_conj := λ g ⟨s, hs⟩, Iw4T_is_conj g s hs,
  is_generator := Iw4_is_generator_alt hα, }

lemma finset.mem_doubleton_iff (a b x : α) : x ∈ ({a, b} : finset α) ↔ (x = a ∨ x = b) :=
begin
  rw [finset.mem_insert, finset.mem_singleton],
end


/-- If α has at least 5 elements, but not 6,
then the only nontrivial normal sugroup of (perm α) is the alternating_group. -/
theorem alternating_group.normal_subgroups_6 {α : Type*} [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α) (hα' : fintype.card α ≠ 6)
  {N : subgroup (alternating_group α)} (hnN : N.normal) (ntN : nontrivial N) : N = ⊤ :=
begin
  rw eq_top_iff,
  rw ← alternating_group_is_perfect hα,

  refine commutator_le_iwasawa _ Iw3 hnN _,
  { -- quasipreprimitive action
    apply is_preprimitive.is_quasipreprimitive,
    apply nat.finset_is_preprimitive_of_alt,
    norm_num,
    apply lt_of_lt_of_le _ hα, norm_num,
    exact hα', },

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

/-- If α has at least 5 elements, but not 8,
then the only nontrivial normal sugroup of (alternating_group α) is the alternating_group. -/
theorem alternating_group.normal_subgroups_8 {α : Type*} [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α) (hα' : fintype.card α ≠ 8)
  {N : subgroup (alternating_group α)} (hnN : N.normal) (ntN : nontrivial N) : N = ⊤ :=
begin
  rw eq_top_iff,
  rw ← alternating_group_is_perfect hα,

  refine commutator_le_iwasawa _ (Iw4 hα) hnN _,
  { -- quasipreprimitive action
    apply is_preprimitive.is_quasipreprimitive,
    apply nat.finset_is_preprimitive_of_alt,
    norm_num,
    apply lt_of_lt_of_le _ hα, norm_num,
    exact hα', },

  -- N acts nontrivially
  intro h,
  obtain ⟨g, hgN, hg_ne⟩ := N.nontrivial_iff_exists_ne_one.mp ntN,
  have hg_ne' : (to_perm g : equiv.perm α) ≠ 1,
  { intro hg_ne', apply hg_ne,
    ext, simp only [subgroup.coe_one, ← hg_ne'],
    refl, },

  obtain ⟨s, hs⟩ := @nat.finset.mul_action_faithful α _ _ _ _ 4 _ _ _ g hg_ne',
  apply hs,
  suffices : s ∈ fixed_points N (nat.finset α 4),
  rw mem_fixed_points at this, exact this ⟨g, hgN⟩,
  rw h, rw set.top_eq_univ, apply set.mem_univ,
  norm_num,
  apply lt_of_lt_of_le _ hα, norm_num,
end

/-- If α has at least 5 elements,
then the only nontrivial normal sugroup of (alternating_group α) is ⊤. -/
theorem alternating_group.normal_subgroups {α : Type*}
  [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α)
  {N : subgroup (alternating_group α)}
  (hnN : N.normal) (ntN : nontrivial N) : N = ⊤ :=
begin
  by_cases hα' : fintype.card α = 6,
  { apply alternating_group.normal_subgroups_8 hα _ hnN ntN,
    rw hα', norm_num, },
  exact alternating_group.normal_subgroups_6 hα hα' hnN ntN,
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
