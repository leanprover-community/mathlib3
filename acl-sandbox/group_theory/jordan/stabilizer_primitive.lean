/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/


import .for_mathlib.alternating
import .for_mathlib.stabilizer
import .for_mathlib.set
import .for_mathlib.group_theory__subgroup__basic
import .for_mathlib.alternating

import .index_normal
import .primitive
import .multiple_transitivity
import .mul_action_finset

-- import group_theory.specific_groups.alternating

open_locale pointwise classical

variables {α : Type*} [fintype α] [decidable_eq α]

open mul_action

namespace equiv.perm


lemma of_subtype_mem_stabilizer (s : set α) (g : equiv.perm s) :
  g.of_subtype ∈ stabilizer (equiv.perm α) s :=
begin
  rw mem_stabilizer_of_finite_iff,
  intro x,
  rw set.mem_smul_set ,
  rintro ⟨y, hy, rfl⟩,
  simp only [equiv.perm.smul_def],
  rw equiv.perm.of_subtype_apply_of_mem g hy,
  refine subtype.mem _,
end

lemma of_subtype_mem_stabilizer' (s : set α) (g : equiv.perm (sᶜ : set α)) :
  g.of_subtype  ∈ stabilizer (equiv.perm α) s :=
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
end

lemma stabilizer_is_preprimitive (s : set α) : is_preprimitive (stabilizer (equiv.perm α) s) s :=
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
    apply of_subtype_mem_stabilizer,
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
  apply stabilizer_is_preprimitive,
end

end equiv.perm

namespace alternating_group

lemma stabilizer.is_preprimitive (s : set α) (hs : (sᶜ : set α).nontrivial):
  is_preprimitive (stabilizer (alternating_group α) s) s :=
begin
  let φ : stabilizer (alternating_group α) s → equiv.perm s := mul_action.to_perm,
  suffices hφ : function.surjective φ,

  let f : s →ₑ[φ] s := {
  to_fun := id,
  map_smul' := λ ⟨g, hg⟩ ⟨x, hx⟩,
    by simp only [id.def, equiv.perm.smul_def, to_perm_apply], },
  have hf : function.bijective f := function.bijective_id,
  rw is_preprimitive_of_bijective_map_iff hφ hf,
  exact equiv.perm.is_preprimitive s,

  suffices : ∃ k : equiv.perm (sᶜ : set α), equiv.perm.sign k = -1,
  obtain ⟨k, hk_sign⟩ := this,
  have hks : (equiv.perm.of_subtype k) • s = s,
  { rw ← mem_stabilizer_iff,
    exact equiv.perm.of_subtype_mem_stabilizer' s k, },

  -- function.surjective φ
  have hφ : function.surjective φ,
  { have hminus_one_ne_one : (-1 : units ℤ) ≠ 1,
    { intro h, rw [← units.eq_iff, units.coe_one, units.coe_neg_one] at h, norm_num at h, },

    intro g,
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
      exact equiv.perm.of_subtype_mem_stabilizer s g, },
    { simp only [hsg, hminus_one_ne_one, if_false, mul_smul, hks],
      exact equiv.perm.of_subtype_mem_stabilizer s g, },

    dsimp [φ],
    cases int.units_eq_one_or (equiv.perm.sign g) with hsg hsg,
    { dsimp [g'], simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false],
      ext,
      -- simp only [to_perm_apply, has_smul.stabilizer_def, subtype.coe_mk],
      change equiv.perm.of_subtype g ↑x = ↑(g x),
      exact equiv.perm.of_subtype_apply_coe g x, },
    { dsimp [g'], simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false],
      ext,
      -- simp only [to_perm_apply, has_smul.stabilizer_def, subtype.coe_mk],
      change ((equiv.perm.of_subtype g) * (equiv.perm.of_subtype k)) ↑x = ↑(g x),
      rw equiv.perm.mul_apply ,
      rw equiv.perm.of_subtype_apply_of_not_mem k _,
      exact equiv.perm.of_subtype_apply_coe g x,
      rw set.not_mem_compl_iff, exact x.prop, }, },
  exact hφ,

  -- ∃ k : equiv.perm (sᶜ : set α), equiv.perm.sign k = -1,
  obtain ⟨a, ha, b, hb, hab⟩ := hs,
  use equiv.swap ⟨a, ha⟩ ⟨b, hb⟩,
  rw equiv.perm.sign_swap _,
  rw ← function.injective.ne_iff (subtype.coe_injective),
  simp only [subtype.coe_mk], exact hab,
end

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

end alternating_group
