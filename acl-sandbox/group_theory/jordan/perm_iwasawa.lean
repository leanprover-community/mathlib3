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
import .perm_maximal

/-!
# Normal subgroups of the symmetric group

* `equiv.perm.normal_subgroups` : a nontrivial normal subgroup of `equiv.perm α` contains the alternating group.
* `Iw2`: the Iwasawa structure for the symmetric group `equiv.perm α` acting on ordered pairs.

-/
open_locale pointwise


namespace equiv.perm

open mul_action

variables {α : Type*} [decidable_eq α] [fintype α]

def Iw_t (s : finset α) : (equiv.perm s) →* (equiv.perm α) := equiv.perm.of_subtype

def Iw_T(s : finset α) : subgroup (equiv.perm α):= (Iw_t s).range

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
/- Useless
  have hpg'g : ∀ k, k = pg' (pg k) ,
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
    dsimp only [tgs, Iw_T, Iw_t],
    rw equiv.perm.of_subtype_apply_of_mem,
    dsimp only [pg],
    simp only [subtype.coe_mk, monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, function.comp_app, mul_aut.conj_apply,
  equiv.perm.coe_mul, equiv.subtype_equiv_symm, equiv.coe_trans, equiv.subtype_equiv_apply,
  embedding_like.apply_eq_iff_eq],
    dsimp [ts, Iw_T, Iw_t], rw equiv.perm.of_subtype_apply_of_mem,
    apply congr_arg, apply congr_arg,
    rw ← subtype.coe_inj, simp only [subtype.coe_mk],
    refl,

    { rw [← equiv.perm.smul_def, finset.inv_smul_mem_iff], exact hx, },
    exact hx, },

  { -- x ∉ g • s
    dsimp only [tgs, Iw_T, Iw_t],
    rw equiv.perm.of_subtype_apply_of_not_mem,
    dsimp only [ts, Iw_T, Iw_t],
    simp only [monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, function.comp_app, mul_aut.conj_apply, equiv.perm.coe_mul],
    rw equiv.perm.of_subtype_apply_of_not_mem,
    simp only [equiv.perm.apply_inv_self],
    { intro hx, apply hx', rw [← finset.inv_smul_mem_iff], exact hx, },
    exact hx', },

end

/- The Iwasawa structure for the symmetric group acting on ordered pairs -/
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

/-
lemma finset.mem_doubleton_iff (a b x : α) : x ∈ ({a, b} : finset α) ↔ (x = a ∨ x = b) :=
begin
  rw [finset.mem_insert, finset.mem_singleton],
end
 -/

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
  apply hs,
  suffices : s ∈ fixed_points N (nat.finset α 2),
  rw mem_fixed_points at this, exact this ⟨g, hgN⟩,
  rw h, rw set.top_eq_univ, apply set.mem_univ,
  apply_instance,
  norm_num,
  apply lt_of_lt_of_le _ hα, norm_num,
  convert hg_ne, ext x, refl,
end

end equiv.perm
