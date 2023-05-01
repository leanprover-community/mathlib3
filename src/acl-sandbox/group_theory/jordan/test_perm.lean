/-
Copyright (c) 2022 ACL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ACL
-/

import tactic
import logic.equiv.basic
import .mul_action_finset

variables {α β γ : Type*} [decidable_eq α] [decidable_eq β] [decidable_eq γ]

def equiv_ulift : α ≃ ulift α := {
    to_fun := λ a, {down := a},
    inv_fun := λ b, b.down,
    left_inv := λ a, rfl,
    right_inv := λ b, by simp only [ulift.up_down], }

/- def equiv.perm_ulift : equiv.perm (ulift α) ≃* equiv.perm α := {
to_fun := λ k, {
  to_fun := λ x, (k {down := x}).down,
  inv_fun := λ x, (k.symm {down := x}).down,
  left_inv := λ x,
    by simp only [ulift.down_up, ulift.up_down, k.left_inv, equiv.symm_apply_apply],
  right_inv := λ x,
    by simp only [ulift.down_up, ulift.up_down, k.right_inv, equiv.apply_symm_apply], },
inv_fun := λ k, {
  to_fun := λ x, {down := k x.down},
  inv_fun := λ x, {down := k.symm x.down},
  left_inv := λ x,
    by simp only [ulift.down_up, ulift.up_down, k.left_inv, equiv.symm_apply_apply],
  right_inv := λ x,
    by simp only [ulift.down_up, ulift.up_down, k.right_inv, equiv.apply_symm_apply], },
left_inv := λ k, equiv.perm.ext (λ x,
    by simp only [equiv.coe_fn_mk, ulift.down_inj, embedding_like.apply_eq_iff_eq, ulift.up_down]),
right_inv := λ k, equiv.perm.ext (λ x,by simp only [equiv.coe_fn_mk]),
map_mul' := λ h k, equiv.perm.ext (λ x, by
    simp only [ulift.up_down, equiv.perm.coe_mul, equiv.coe_fn_mk, ulift.down_inj]),
     } -/

def equiv.of_perm_of_equiv (f : α ≃ β) : equiv.perm α ≃* equiv.perm β := {
  map_mul' := λ h k, equiv.perm.ext ( λ x, by simp only [equiv.to_fun_as_coe,
    equiv.equiv_congr_apply_apply, equiv.perm.coe_mul, function.comp_app, equiv.symm_apply_apply] ),
  .. equiv.equiv_congr f f , }

def equiv.of_perm_of_equiv' (f : α ≃ β) : equiv.perm α ≃* equiv.perm β := {
  to_fun := λ k, {
    to_fun := λ x, f (k (f.symm x)),
    inv_fun := λ x, f (k.symm (f.symm x)),
    left_inv := λ x, by simp only [equiv.symm_apply_apply, equiv.apply_symm_apply],
    right_inv := λ x, by simp only [equiv.symm_apply_apply, equiv.apply_symm_apply]},
  inv_fun := λ k, {
    to_fun := λ x, f.symm (k (f x)),
    inv_fun := λ x, f.symm (k.symm (f x)),
    left_inv := λ x, by simp only [equiv.symm_apply_apply, equiv.apply_symm_apply],
    right_inv := λ x, by simp only [equiv.symm_apply_apply, equiv.apply_symm_apply] },
  left_inv := λ k, equiv.perm.ext (λ x, by simp only [equiv.symm_apply_apply, equiv.coe_fn_mk] ),
  right_inv := λ k, equiv.perm.ext (λ x, by simp only [equiv.apply_symm_apply, equiv.coe_fn_mk] ),
  map_mul' := λ h k, equiv.perm.ext (λ x,
    by simp only [equiv.symm_apply_apply, equiv.perm.coe_mul, equiv.coe_fn_mk,
      embedding_like.apply_eq_iff_eq] ), }

lemma equiv.of_perm_of_equiv_trans (f : α ≃ β) (g : β ≃ γ) :
  equiv.of_perm_of_equiv (f.trans g) =
    (equiv.of_perm_of_equiv f).trans (equiv.of_perm_of_equiv g) :=
mul_equiv.ext (λ k, equiv.perm.ext (λx, rfl))

lemma equiv.of_perm_of_equiv_symm (f : α ≃ β):
  equiv.of_perm_of_equiv (f.symm) = (equiv.of_perm_of_equiv f).symm :=
mul_equiv.ext (λ x, equiv.perm.ext (λ x, rfl))

example : equiv.perm α ≃* equiv.perm (ulift α):=
equiv_ulift.of_perm_of_equiv

variables {s : finset α} {f : α ≃ β}

-- f s
example : finset β := s.image f.to_fun

-- s ≃ f s
def f' : s ≃ (s.image f.to_fun) := equiv.subtype_equiv f (λ a,
  by simp only [equiv.to_fun_as_coe, finset.mem_image, embedding_like.apply_eq_iff_eq,
    exists_prop, exists_eq_right])

-- F : equiv.perm s ≃* equiv.perm (f s) := equiv.of_perm_of_equiv f'
example : equiv.perm s ≃* equiv.perm (s.image f.to_fun) := equiv.of_perm_of_equiv (f')

example (g : equiv.perm s) : equiv.perm β :=
  (equiv.of_perm_of_equiv f) (equiv.perm.of_subtype g)

example (g : equiv.perm s) : equiv.perm (s.image f.to_fun) :=
  (equiv.of_perm_of_equiv (f') g)

example (g : equiv.perm s) : equiv.perm β :=
  equiv.perm.of_subtype (equiv.of_perm_of_equiv (f') g : equiv.perm (s.image f.to_fun))

lemma test (g : equiv.perm s) :
  equiv.perm.of_subtype (equiv.of_perm_of_equiv (f') g : equiv.perm (s.image f.to_fun)) =
    (equiv.of_perm_of_equiv f) (equiv.perm.of_subtype g)  :=
begin
  ext,
  cases em (x ∈ s.image f.to_fun) with hx hx',
  { rw equiv.perm.of_subtype_apply_of_mem,
    simp only [equiv.of_perm_of_equiv, f', mul_equiv.has_coe_to_fun ],
    simp only [subtype.coe_mk, equiv.subtype_equiv_symm, equiv.to_fun_as_coe, mul_equiv.coe_mk,
      equiv.equiv_congr_apply_apply, equiv.subtype_equiv_apply, embedding_like.apply_eq_iff_eq],
    rw equiv.perm.of_subtype_apply_of_mem,
    exact hx, },
  { rw equiv.perm.of_subtype_apply_of_not_mem,
    simp only [equiv.of_perm_of_equiv, f', mul_equiv.has_coe_to_fun ],
    simp only [equiv.to_fun_as_coe, mul_equiv.coe_mk, equiv.equiv_congr_apply_apply],
    rw equiv.perm.of_subtype_apply_of_not_mem,
    { simp only [equiv.apply_symm_apply], },
    { intro hx, apply hx', rw ← equiv.apply_symm_apply f x,
      rw finset.mem_image,
      use f.symm x, use hx, refl, },
    exact hx', },
end

-- To access the mul_action on finset
open_locale pointwise

/-
example {s' : finset α} (g : equiv.perm α)
  (f : equiv.perm s →* equiv.perm α) (f' : equiv.perm s' →* equiv.perm α) :
  (mul_aut.conj g) • f.range = f'.range := sorry

def Iw_t' (s : finset α) : (equiv.perm s) →* (equiv.perm α) := equiv.perm.of_subtype

def Iw_T'(s : finset α) : subgroup (equiv.perm α) := (equiv.perm.of_subtype :
  (equiv.perm s) →* (equiv.perm α)).range

def Iw_k' (s : finset α) (g : equiv.perm α) :  ↥s ≃ ↥(g • s) :=
  equiv.subtype_equiv g (λ a,
    by rw [← equiv.perm.smul_def, finset.smul_mem_smul_finset_iff])

def Iw_c' (s : finset α) (g : equiv.perm α) (k : equiv.perm ↥s) :=
  ((Iw_k s g).symm.trans k).trans (Iw_k s g)
-/

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

#check Iw_conj_eq

example {G H K : Type*} [group G] [group H] [group K] (f : G →* H) (g : H →* K) :
  (g.comp f).range = subgroup.map g f.range :=
by  simp only [monoid_hom.range_eq_map, ← subgroup.map_map]

example {G H K : Type*} [group G] [group H] [group K] (f : G →* H) (g : H →* K) :
  (g.comp f).range = subgroup.map g f.range :=
by  simp only [monoid_hom.range_eq_map, ← subgroup.map_map]

example {G H K : Type*} [group G] [group H] [group K] (f : G ≃* H) (g : H →* K) :
  (g.comp f.to_monoid_hom).range = g.range :=
begin

  simp only [monoid_hom.range_eq_map, ← subgroup.map_map],
  apply congr_arg,
  simp only [← monoid_hom.range_eq_map],
  -- Via sets :
  apply set_like.coe_injective,
  simp only [monoid_hom.coe_range, mul_equiv.coe_to_monoid_hom, subgroup.coe_top,
  ← mul_equiv.coe_to_equiv, equiv.range_eq_univ],
  /- -- Via groups :
  rw eq_top_iff,
  intros k _,
  simp only [monoid_hom.mem_range, mul_equiv.coe_to_monoid_hom],
  use f.symm k, simp only [mul_equiv.apply_symm_apply],
  rw subgroup.mem_map_equiv ,
  apply subgroup.mem_top, -/
end
#check mul_equiv.coe_to_equiv

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


variable [fintype α]


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



example {α β : Type*} [decidable_eq α] [decidable_eq β] [fintype α] [fintype β] (e : α ≃ β)
   (k : equiv.perm α) :
  equiv.perm.sign k = equiv.perm.sign ((equiv.perm_congr e) k) :=
begin
  dsimp [equiv.perm_congr, equiv.equiv_congr],
  rw equiv.perm.sign_symm_trans_trans,
end

example (G ι : Type*) [monoid G] (N : submonoid G) (s : ι → submonoid G)
  (hs : ∀ i, s i ≤ N) :
  submonoid.comap N.subtype (supr s) = supr (λ i, submonoid.comap N.subtype (s i)) :=
begin
  have : function.injective N.subtype,
  simp,refine subtype.coe_injective,
  let hzz := submonoid.gci_map_comap this,
  apply hzz.u_supr_of_lu_eq_self s,
  intro i,
sorry
end


example (G ι : Type*) [group G] (N : subgroup G) (s : ι → subgroup G)
  (hs : ∀ i, s i ≤ N) :
  (supr s).subgroup_of N = supr (λ i, (s i).subgroup_of N) :=
begin
  -- dsimp only [subgroup.subgroup_of],
  apply (galois_connection.to_galois_coinsertion
    (subgroup.gc_map_comap (N.subtype)) _).u_supr_of_lu_eq_self s,
  { intro i,
    rw subgroup.map_comap_eq,
    rw inf_eq_right,
    simp only [subgroup.subtype_range],
    exact hs i, },
  { intro K,
    rw subgroup.comap_map_eq_self_of_injective,
    exact le_refl K,
    simp only [subgroup.coe_subtype, subtype.coe_injective], },
end

lemma example3 (g : alternating_group α) (hg : equiv.perm.is_three_cycle (g : equiv.perm α)) :
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

lemma example4 :
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


example {G : Type*} [group G] (N : subgroup G) :
  N = subgroup.map (N.subtype) ⊤ :=
begin
  rw ← subgroup.comap_top (N.subtype),
  rw subgroup.map_comap_eq,
  simp only [subgroup.subtype_range, inf_top_eq],
end


lemma Iw_is_generator_alt : supr (λ (s : { s : finset α // s.card = 3}),
     (subgroup.map equiv.perm.of_subtype
      (alternating_group (s : finset α))).subgroup_of (alternating_group α)) =  ⊤ :=
begin
  rw ← example4,
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
    obtain ⟨s, hs3, hsg⟩ := example3 g hg,
    simp only [set_like.mem_coe],
    apply subgroup.mem_supr_of_mem,
    swap, exact ⟨s, hs3⟩,
    exact hsg, },
end




lemma equiv.perm.of_subtype_eq_extend_domain {α : Type*} [decidable_eq α] [fintype α]
  {p : α → Prop} [decidable_pred p]
  {g : equiv.perm (subtype p)} : g.of_subtype = g.extend_domain (equiv.refl (subtype p)) :=
begin
  ext x,
  cases dec_em (p x),
    { rw equiv.perm.extend_domain_apply_subtype g (equiv.refl (subtype p)) h,
      rw equiv.perm.of_subtype_apply_of_mem g h,
      refl, },
    { rw equiv.perm.extend_domain_apply_not_subtype g (equiv.refl (subtype p)) h,
      rw equiv.perm.of_subtype_apply_of_not_mem g h, },
end

lemma equiv.perm.of_subtype.cycle_type {α : Type*} [decidable_eq α] [fintype α]
  {p : α → Prop} [decidable_pred p]
  {g : equiv.perm (subtype p)} :  (g.of_subtype).cycle_type = g.cycle_type :=
begin
  rw equiv.perm.of_subtype_eq_extend_domain,
  rw equiv.perm.cycle_type_extend_domain,
end


lemma example3' (g : equiv.perm α)  :
  ∃ (s : finset α) (k : equiv.perm s),
    k.cycle_type = g.cycle_type ∧
    (equiv.perm.of_subtype : equiv.perm s →* equiv.perm α) k = g :=
begin
  use (g : equiv.perm α).support,
  let k : equiv.perm (g : equiv.perm α).support := equiv.perm.subtype_perm (g : equiv.perm α) (λ a, by simp only [equiv.perm.apply_mem_support]),
  use k,
  suffices : (equiv.perm.of_subtype : equiv.perm g.support →* equiv.perm α) k = g,
  split,
  { -- cycle_type
    simp_rw ← this,
    rw equiv.perm.of_subtype.cycle_type, },
  exact this,
  { -- k.of_subtype = g
    apply equiv.perm.of_subtype_subtype_perm,
    { intro a, simp only [equiv.perm.mem_support, imp_self] }, },
end
