/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import group_theory.index
import group_theory.quotient_group
import group_theory.subgroup.pointwise

/-!
# Commensurability for subgroups

This file defines commensurability for subgroups of a group `G`. It then goes on to prove that
commensurability defines an equivalence relation and finally defines the commensurator of a subgroup
of `G`.

## Main definitions

* `commensurable`: defines commensurability for two subgroups `H`, `K` of  `G`
* `commensurator`: defines the commensurator of a a subgroup `H` of `G`
* `conj_subgroup`: defined the conjugate subgroup of a subgroup `H` by an element `g : G`,
 i.e. `g H g⁻¹` --maybe this should be moved somewhere else?
-/

open_locale pointwise

variables {G G' : Type*} [group G] [group G']

/--Two subgroups `H K` of `G` are commensurable if `H ⊓ K` has finite index in both `H` and `K` -/
def commensurable (H K : subgroup G) : Prop :=
  subgroup.index (H.subgroup_of K) ≠ 0 ∧ subgroup.index (K.subgroup_of H) ≠ 0

namespace commensurable

lemma comap_self_subtype (H : subgroup G) : H.comap H.subtype = ⊤ :=
eq_top_iff.2 $ λ x _, x.prop

lemma subgroup_of_top (H : subgroup G) : subgroup.subgroup_of H H = ⊤ :=
comap_self_subtype H

lemma index_of_top  : ( ⊤ : subgroup G).index = 1 :=
begin
  rw subgroup.index,
  have h3 : (cardinal.mk  (quotient_group.quotient (⊤ : subgroup G))) = 1 ,
    by {rw cardinal.eq_one_iff_unique,
        split,
        apply quotient_group.subsingleton_quotient_top,
        simp only [nonempty_of_inhabited],},
  simp only [h3, cardinal.one_to_nat],
end

lemma reflex (H : subgroup G) : commensurable H H :=
begin
  rw commensurable,
  simp only [ne.def, and_self],
  have := subgroup_of_top H,
  rw this,
  have h2 := index_of_top,
  rw h2,
  simp only [h2, nat.one_ne_zero, not_false_iff],
end

lemma symm (H K : subgroup G) : commensurable H K ↔ commensurable K H :=
begin
  simp_rw commensurable,
  rw and_comm,
end

/--The conjugate of a subgroup `H` of `G` by `g`  -/
def conj_subgroup (g : G) (H : subgroup G) : subgroup G := mul_aut.conj g •  H

@[simp] lemma conj_mem'  (g : G)  (H : subgroup G) (h : G) :
  (h ∈ conj_subgroup g H) ↔ ∃ x : H, g * x * g⁻¹ = h  :=
subgroup.mem_map.trans subtype.exists'

lemma conj_subgroup_mul (g h : G) (H : subgroup G) :
  conj_subgroup (g*h) H = conj_subgroup g (conj_subgroup h H) :=
begin
  simp_rw conj_subgroup,
  simp only [monoid_hom.map_mul] at *,
  exact mul_smul (mul_aut.conj g) (mul_aut.conj h) H,
end

lemma conj_map  (g : G) (H : subgroup G) :
  subgroup.map ((mul_aut.conj g).to_monoid_hom) H  = conj_subgroup g H :=
begin
 rw conj_subgroup,
 refl,
end

namespace subgroup
/--`mul_hom` on subgroups induced by `mul_hom` of parent group-/
def img_mul_hom  (H : subgroup G) (f : G →* G') :
  H →* H.map f :=
{ to_fun := λ x, ⟨f x, by {use x,
    simp only [set_like.coe_mem, eq_self_iff_true, set_like.mem_coe, and_self],}⟩,
  map_one' := by {simp only [subgroup.coe_one, monoid_hom.map_one],
    refl,},
  map_mul':= by {intros x y,
    simp only [monoid_hom.map_mul, subgroup.coe_mul], refl,}}

/--Isomorphism of a subgroup with its image under an isomorphism-/
def img_mul_equiv  (H : subgroup G) (f : G ≃* G') :
  H ≃* (subgroup.map f.to_monoid_hom) H :=
{ to_fun := λ x, ⟨f.1 x, by {simp only [exists_prop, set_like.coe_mem,
    mul_equiv.coe_to_monoid_hom, mul_equiv.to_fun_eq_coe, subgroup.mem_map,
    exists_eq_right, mul_equiv.apply_eq_iff_eq]}⟩,
  inv_fun := λ x, ⟨f.2 x, by {simp only [mul_equiv.inv_fun_eq_symm],
    have xp := x.property,
    simp_rw subgroup.map_equiv_eq_comap_symm at xp,
    simp only [mul_equiv.coe_to_monoid_hom, subgroup.mem_comap, subtype.val_eq_coe] at xp,
    apply xp,}⟩,
  left_inv := by {intro x,
    simp only [set_like.eta, mul_equiv.inv_fun_eq_symm, mul_equiv.symm_apply_apply,
      mul_equiv.to_fun_eq_coe, subgroup.coe_mk],},
  right_inv := by {intro x,
    simp only [mul_equiv.apply_symm_apply, set_like.eta, mul_equiv.inv_fun_eq_symm,
      mul_equiv.to_fun_eq_coe, subgroup.coe_mk],},
  map_mul' := by {intros x y,
      simp only [mul_equiv.to_fun_eq_coe, subgroup.coe_mul, mul_equiv.map_mul], refl,},}

/--Image of a sub_subgroup under a `mul_hom`-/
def mul_hom_sub_subgroup (H : subgroup G) (K : subgroup H) (f : G →* G') :
  subgroup (H.map f) :=  subgroup.map (img_mul_hom H f) K

lemma equiv_sub_subgroup_of (H K: subgroup G) (f : G ≃* G') :
  (mul_hom_sub_subgroup H (K.subgroup_of H) f.to_monoid_hom) =
  (K.map f.to_monoid_hom).subgroup_of (H.map f.to_monoid_hom) :=
begin
  rw mul_hom_sub_subgroup,
  rw img_mul_hom,
  simp_rw subgroup.map,
  ext,
  simp only [subgroup.mem_subgroup_of, mul_equiv.coe_to_monoid_hom, set.mem_image, set_like.mem_coe,
  subgroup.mem_mk, monoid_hom.coe_mk],
  split,
  intro h,
  cases h with y,
  use y,
  simp only [h_h, true_and],
  rw ← h_h.2,
  simp only [subgroup.coe_mk],
  intro h,
  cases h with y,
  cases x.property with z,
  simp only [mul_equiv.coe_to_monoid_hom, set_like.mem_coe, subtype.val_eq_coe] at *,
  have h1 := h_h.2,
  rw ← h.2 at h1,
  simp only [mul_equiv.apply_eq_iff_eq] at h1,
  use z,
  apply h.1,
  simp_rw ← h1,
  simp only [h_h, set_like.eta, eq_self_iff_true, and_self, subgroup.coe_mk],
end

lemma subgroup_of_le (H K L : subgroup G) (h : H ≤ K) : H.subgroup_of L ≤ K.subgroup_of L :=
begin
  intros x h,
  cases x,
  solve_by_elim,
end

end subgroup

/--Isomorphism of a subgroup with its conjugate-/
def conj_equiv (g : G) (H : subgroup G) : H ≃* conj_subgroup g H :=
begin
  rw ← conj_map,
  apply subgroup.img_mul_equiv,
end

@[simp]
lemma cong_subgroup_id_eq_self (H : subgroup G) : conj_subgroup 1 H = H :=
begin
  rw conj_subgroup,
  simp only [one_smul, monoid_hom.map_one],
end

namespace quotient_group
/--The map induced by a `mul_hom` on a quotient-/
noncomputable def quot_map (H : subgroup G) (H' : subgroup G')
(f : G →* G') :  quotient_group.quotient H →  quotient_group.quotient H' :=
λ x, quotient_group.mk (f x.out')

lemma quot_map_inj (H : subgroup G) (H' : subgroup G') (f : G →* G') (h : H.map f  = H') :
  (function.injective f) →  function.injective (quot_map H H' f) :=
begin
  intro hf,
  rw function.injective at *,
  intros a b,
  rw quot_map,
  rw quotient_group.eq',
  intro hab,
  have ha :=  quotient.out_eq' a,
  have hb :=  quotient.out_eq' b,
  rw ← ha,
  rw ← hb,
  rw quotient_group.eq',
  simp_rw ← h at hab,
  have r1 : ∀ (a b : G), (f(a))⁻¹*f(b)=f(a⁻¹*b), by {
    simp only [forall_const, monoid_hom.map_mul, eq_self_iff_true, monoid_hom.map_inv],},
  cases hab with t,
  have hab2 := hab_h.2,
  have rab := r1 a.out' b.out',
  rw rab at hab2,
  have := hf hab2,
  rw ← this,
  exact hab_h.1,
end

end quotient_group

/--`mul_hom` from `subgroup_of` to `inf`-/
def subgroup_of_to_inf (K L : subgroup G) : (K.subgroup_of L) →* (K ⊓ L : subgroup G) := {
  to_fun := λ x, ⟨L.subtype x,
    by {have xp := x.property,
        simp_rw [subgroup.mem_subgroup_of] at xp,
        simp only [set_like.coe_mem, subgroup.coe_subtype, and_true, subgroup.mem_inf],
        exact xp}⟩,
  map_one' := by {simp only [subgroup.coe_subtype, subgroup.coe_one], refl, },
  map_mul' := by {intros x y,simp only [subgroup.coe_subtype, subgroup.coe_mul], refl},
}

lemma subgroup_of_to_inf_inj ( K L : subgroup G) : function.injective (subgroup_of_to_inf K L) :=
begin
  rw function.injective,
  rw subgroup_of_to_inf,
  simp only [imp_self, forall_const, subgroup.coe_subtype, subtype.mk_eq_mk, monoid_hom.coe_mk,
    set_like.coe_eq_coe],
end

lemma subgroup_of_to_inf_img (H K L : subgroup G) :
  subgroup.map (subgroup_of_to_inf  K L) (((H ⊓ K).subgroup_of L).subgroup_of (K.subgroup_of L)) =
  (H.subgroup_of (K ⊓ L)) :=
begin
  rw subgroup_of_to_inf,
  ext,
  simp only [exists_prop, subgroup.coe_subtype, subgroup.mem_map, monoid_hom.coe_mk],
  split,
  intro hx,
  cases hx,
  rw ← hx_h.2,
  simp only [subgroup.mem_subgroup_of, subgroup.mem_inf, subgroup.coe_mk] at *,
  apply hx_h.1.1,
  intro hx,
  simp_rw [subgroup.mem_subgroup_of] at *,
  have := x.property,
  simp only [subgroup.mem_inf, subtype.val_eq_coe] at *,
  use x,
  apply this.2,
  simp only [subgroup.mem_subgroup_of, subgroup.coe_mk] at *,
  apply this.1,
  simp only [hx, this.left, set_like.eta, eq_self_iff_true, and_self, subgroup.coe_mk],
end

lemma subgroup_of_index_zero_index_zero (H K L : subgroup G) :
  (((H ⊓ K).subgroup_of L).subgroup_of (K.subgroup_of L)).index = 0  →
  (H.subgroup_of (K ⊓ L)).index = 0 :=
begin
  simp_rw subgroup.index,
  intro h,
  have H0 := quotient_group.quot_map_inj (((H ⊓ K).subgroup_of L).subgroup_of (K.subgroup_of L))
            (H.subgroup_of (K ⊓ L)) (subgroup_of_to_inf  K L) (subgroup_of_to_inf_img H K L)
            (subgroup_of_to_inf_inj K L),
  have H1 := cardinal.to_nat_zero_of_injective' (H0),
  apply H1 h,
end

lemma index_subgroup_le {H K : subgroup G} (h : H ≤ K)  : K.index = 0 → H.index = 0 :=
begin
  intro h1,
  have := subgroup.index_eq_mul_of_le h,
  rw h1 at this,
  simp only [zero_mul] at this,
  apply this,
end

lemma inf_ind_prod (H K L : subgroup G) :
  ((H ⊓ K).subgroup_of L).index = 0  →
  (H.subgroup_of L).index = 0 ∨ (K.subgroup_of (L ⊓ H)).index = 0 :=
begin
  have h1 : (subgroup.subgroup_of (H ⊓ K)  L) ≤ (subgroup.subgroup_of H  L),
    by {apply subgroup.subgroup_of_le, simp only [inf_le_left],},
  have h2 := subgroup.index_eq_mul_of_le h1,
  intro h,
  rw h at h2,
  simp only [nat.zero_eq_mul] at h2,
  cases h2,
  simp only [h2, true_or, eq_self_iff_true],
  have := (subgroup_of_index_zero_index_zero K H L),
  rw inf_comm at this,
  have ht := this h2,
  rw inf_comm at ht,
  simp only [ht, eq_self_iff_true, or_true],
 end

/--Map from `L ⊓ K/(L ⊓ H ⊓ K)` to `K/(H ⊓ K)`-/
noncomputable def  inf_quot_map (H K L : subgroup G) :
  quotient_group.quotient (H.subgroup_of (L ⊓ K)) → quotient_group.quotient ((H.subgroup_of K)) :=
  λ x, quotient_group.mk (⟨x.out', by
    {let y := x.out',
    have := y.property,
    simp only [subgroup.mem_inf, subtype.val_eq_coe] at this,
    simp_rw ← y,
    exact this.2, }⟩ : K)

lemma inf_quot_map_injective (H K L : subgroup G) : function.injective (inf_quot_map H K L) :=
begin
  rw function.injective ,
  rw inf_quot_map,
  intros a b,
  intro hab,
  have ha :=  quotient.out_eq' a,
  have hb :=  quotient.out_eq' b,
  rw ← ha,
  rw ← hb,
  simp only [quotient.eq'] at *,
  convert hab,
end

lemma inf_index_zero_subgroup_of_index_zero (H K L : subgroup G) :
  (H.subgroup_of (L ⊓ K)).index = 0  → (H.subgroup_of K).index = 0 :=
begin
  simp_rw subgroup.index,
  intro h,
  have H1 := cardinal.to_nat_zero_of_injective' (inf_quot_map_injective H K L),
  apply H1 h,
end

lemma trans' (H K L : subgroup G) (hhk : (H.subgroup_of K).index ≠ 0)
  (hkl : (K.subgroup_of L).index ≠ 0) : (H.subgroup_of L).index ≠ 0 :=
begin
  by_contradiction,
  simp only [not_not, ne.def] at *,
  have s1 : (H ⊓ K).subgroup_of L ≤ H.subgroup_of L ,
    by {apply subgroup.subgroup_of_le, simp only [inf_le_left],},
  have H2 := (index_subgroup_le s1) h,
  have H3 := inf_ind_prod K H L,
  have H4 := inf_index_zero_subgroup_of_index_zero H K L,
  rw inf_comm at H2,
  have H5 := H3 H2,
  cases H5,
  rw H5 at hkl,
  simp only [eq_self_iff_true, not_true, false_and] at hkl,
  exact hkl,
  have H6 := H4 H5,
  rw H6 at hhk,
  simp only [eq_self_iff_true, not_true, false_and] at hhk,
  exact hhk,
end

lemma trans {H K L : subgroup G} (hhk : commensurable H K ) (hkl : commensurable K L) :
  commensurable H L :=
begin
  simp_rw commensurable at *,
  split,
  apply trans' H K L hhk.1 hkl.1,
  apply trans' L K H hkl.2 hhk.2,
end

lemma equivalence : equivalence (@commensurable G _) :=
begin
  rw equivalence,
  split,
  apply reflex,
  split,
  rw symmetric,
  simp only [symm, imp_self, forall_const],
  apply trans,
end

lemma cong_sub_image (H K : subgroup G) (g : G) :
  subgroup.map (conj_equiv g K).to_monoid_hom (H.subgroup_of K) =
  (conj_subgroup g H).subgroup_of (conj_subgroup g K) :=
begin
apply subgroup.equiv_sub_subgroup_of,
end

lemma cong_sub_image' (H K : subgroup G) (g : G) :
  subgroup.map ((conj_equiv g K).symm).to_monoid_hom
  ((conj_subgroup g H).subgroup_of (conj_subgroup g K)) = (H.subgroup_of K) :=
begin
   rw ←  cong_sub_image H K g,
   simp_rw subgroup.map,
   ext,
   simp only [mul_equiv.coe_to_monoid_hom, set.mem_image, mul_equiv.symm_apply_apply,
    exists_eq_right, exists_exists_and_eq_and, set_like.mem_coe, subgroup.mem_mk],
end

/--Equivalence of `K/H ⊓ K` with `gKg⁻¹/gHg⁻¹ ⊓ gKg⁻¹`-/
noncomputable def  quot_conj_equiv (H K : subgroup G) (g : G) :
   quotient_group.quotient (H.subgroup_of K) ≃
   quotient_group.quotient ((conj_subgroup g H).subgroup_of (conj_subgroup g K)) :=
begin
  have h1 := quotient_group.quot_map_inj (H.subgroup_of K) ((conj_subgroup g H).subgroup_of
    (conj_subgroup g K))(conj_equiv g K).to_monoid_hom (cong_sub_image H K g)
    (conj_equiv g K).injective,
  have h2 :=  quotient_group.quot_map_inj ((conj_subgroup g H).subgroup_of (conj_subgroup g K))
    (H.subgroup_of K) ((conj_equiv g K).symm).to_monoid_hom (cong_sub_image' H K g)
    (conj_equiv g K).symm.injective,
  have := function.embedding.schroeder_bernstein  h1 h2,
  apply equiv.of_bijective this.some,
  apply this.some_spec,
end

lemma commensurable_conj {H K : subgroup G} (g : G) :
  commensurable H K  ↔ commensurable (conj_subgroup g H) (conj_subgroup g K) :=
begin
  simp_rw commensurable,
  simp_rw subgroup.index,
  have h1 := quot_conj_equiv H K g,
  have h11 := cardinal.mk_congr h1,
  have h2 := quot_conj_equiv K H g,
  have h22 := cardinal.mk_congr h2,
  rw [h11, h22],
end

lemma commensurable_inv (H : subgroup G) (g : G) :
  commensurable (conj_subgroup g H) H ↔ commensurable H (conj_subgroup g⁻¹ H)  :=
begin
  rw commensurable_conj g⁻¹ ,
  rw ← conj_subgroup_mul g⁻¹ g,
  simp only [mul_left_inv, cong_subgroup_id_eq_self],
end

/--For `H` a subgroup of `G`, this is the subgroup of all elements `g : G`
such that `commensurable (conj_subgroup g H) H`   -/

def commensurator (H : subgroup G) : subgroup G :=
{ carrier := {g : G | commensurable (conj_subgroup g H) H },
  one_mem' := by {simp, apply reflex, },
  mul_mem' := by {intros a b ha hb,
      simp only [set.mem_set_of_eq] at *,
      rw conj_subgroup_mul,
      have h1 : commensurable (conj_subgroup a (conj_subgroup b H)) (conj_subgroup a H),
      { have hab := trans ha ((symm _ _).1 hb),
        rw (commensurable_conj a⁻¹) at hab,
        rw ← conj_subgroup_mul at hab,
        simp only [mul_left_inv, cong_subgroup_id_eq_self] at hab,
        have r1 := commensurable_inv (conj_subgroup b H) a,
        have hab2 := trans hb hab,
        have r2 := r1.2 hab2,
        apply trans r2 (trans hb ((symm _ _).1 ha)),},
      exact trans h1 ha,},
  inv_mem' := by {simp only [set.mem_set_of_eq],
      intros x hx,
      rw symm,
      apply (commensurable_inv H x).1 hx,},}

@[simp]
lemma commensurator_mem_iff (H : subgroup G) (g : G) :
  g ∈ (commensurator H) ↔ commensurable (conj_subgroup g H) H := iff.rfl

lemma commensurable_subgroups_have_eq_commensurator (H K : subgroup G) :
  commensurable H K → commensurator H = commensurator K :=
begin
  intro hk,
  ext,
  simp only [commensurator_mem_iff],
  have h1 := (commensurable_conj x).1 hk,
  split,
  intro h,
  have h2 := trans h hk,
  apply trans ((symm _ _).1 h1) h2,
  intro h,
  apply trans (trans h1 h) ((symm _ _).1 hk),
end

end commensurable
