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

variables {G G' : Type*} [group G] [group G']

/--Two subgroups `H K` of `G` are commensurable if `H ⊓ K` has finite index in both `H` and `K` -/
def commensurable (H K : subgroup G) : Prop :=
H.relindex K ≠ 0 ∧ K.relindex H ≠ 0

namespace commensurable

@[refl] protected lemma refl (H : subgroup G) : commensurable H H :=
begin
  rw commensurable,
  simp [subgroup.relindex_self H],
end

lemma comm (H K : subgroup G) : commensurable H K ↔ commensurable K H :=
begin
  simp_rw commensurable,
  rw and_comm,
end

@[symm]
lemma symm {H K : subgroup G}  : commensurable H K →  commensurable K H :=
begin
  simp_rw comm,
  simp only [imp_self],
end

@[trans]
lemma trans {H K L : subgroup G} (hhk : commensurable H K ) (hkl : commensurable K L) :
  commensurable H L :=
begin
  simp_rw commensurable at *,
  simp_rw subgroup.relindex at *,
  split,
  apply subgroup.relindex_ne_zero_trans H K L hhk.1 hkl.1,
  apply subgroup.relindex_ne_zero_trans L K H hkl.2 hhk.2,
end

lemma equivalence : equivalence (@commensurable G _) :=
begin
  rw equivalence,
  split,
  apply commensurable.refl,
  split,
  rw symmetric,
  simp only [comm, imp_self, forall_const],
  apply trans,
end

lemma cong_sub_image (H K : subgroup G) (g : G) :
  subgroup.map (subgroup.conj_equiv g K).to_monoid_hom (H.subgroup_of K) =
  (subgroup.conj_subgroup g H).subgroup_of (subgroup.conj_subgroup g K) :=
begin
  apply monoid_hom.equiv_sub_subgroup_of,
end

lemma cong_sub_image' (H K : subgroup G) (g : G) :
  subgroup.map ((subgroup.conj_equiv g K).symm).to_monoid_hom
  ((subgroup.conj_subgroup g H).subgroup_of (subgroup.conj_subgroup g K)) = (H.subgroup_of K) :=
begin
   rw ← cong_sub_image H K g,
   simp_rw subgroup.map,
   ext,
   simp only [mul_equiv.coe_to_monoid_hom, set.mem_image, mul_equiv.symm_apply_apply,
   exists_eq_right, exists_exists_and_eq_and, set_like.mem_coe, subgroup.mem_mk],
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

/--Equivalence of `K/H ⊓ K` with `gKg⁻¹/gHg⁻¹ ⊓ gKg⁻¹`-/
noncomputable def  quot_conj_equiv (H K : subgroup G) (g : G) :
   quotient_group.quotient (H.subgroup_of K) ≃
   quotient_group.quotient ((subgroup.conj_subgroup g H).subgroup_of (subgroup.conj_subgroup g K)) :=
begin
  have h1 := quotient_group.quot_map_inj (H.subgroup_of K) ((subgroup.conj_subgroup g H).subgroup_of
    (subgroup.conj_subgroup g K))(subgroup.conj_equiv g K).to_monoid_hom (cong_sub_image H K g)
    (subgroup.conj_equiv g K).injective,
  have h2 :=  quotient_group.quot_map_inj ((subgroup.conj_subgroup g H).subgroup_of
    (subgroup.conj_subgroup g K)) (H.subgroup_of K) ((subgroup.conj_equiv g K).symm).to_monoid_hom
    (cong_sub_image' H K g) (subgroup.conj_equiv g K).symm.injective,
  have := function.embedding.schroeder_bernstein  h1 h2,
  apply equiv.of_bijective this.some,
  apply this.some_spec,
end

lemma commensurable_conj {H K : subgroup G} (g : G) :
  commensurable H K  ↔ commensurable (subgroup.conj_subgroup g H) (subgroup.conj_subgroup g K) :=
begin
  simp_rw [commensurable, subgroup.relindex, subgroup.index],
  have h1 := quot_conj_equiv H K g,
  have h11 := cardinal.mk_congr h1,
  have h2 := quot_conj_equiv K H g,
  have h22 := cardinal.mk_congr h2,
  simp_rw [nat.card, h11, h22],
end

lemma commensurable_inv (H : subgroup G) (g : G) :
  commensurable (subgroup.conj_subgroup g H) H ↔ commensurable H (subgroup.conj_subgroup g⁻¹ H)  :=
begin
  rw [commensurable_conj g⁻¹ ,← subgroup.conj_subgroup_mul g⁻¹ g],
  simp only [mul_left_inv, subgroup.cong_subgroup_id_eq_self],
end

/--For `H` a subgroup of `G`, this is the subgroup of all elements `g : G`
such that `commensurable (conj_subgroup g H) H`   -/

def commensurator (H : subgroup G) : subgroup G :=
{ carrier := {g : G | commensurable (subgroup.conj_subgroup g H) H },
  one_mem' := by {simp only [set.mem_set_of_eq, subgroup.cong_subgroup_id_eq_self], },
  mul_mem' := by {intros a b ha hb,
      simp only [set.mem_set_of_eq] at *,
      rw subgroup.conj_subgroup_mul,
      have h1 : commensurable (subgroup.conj_subgroup a (subgroup.conj_subgroup b H))
        (subgroup.conj_subgroup a H),
      { have hab := trans ha ((comm _ _).1 hb),
        rw (commensurable_conj a⁻¹) at hab,
        rw ← subgroup.conj_subgroup_mul at hab,
        simp only [mul_left_inv, subgroup.cong_subgroup_id_eq_self] at hab,
        have r1 := commensurable_inv (subgroup.conj_subgroup b H) a,
        have hab2 := trans hb hab,
        have r2 := r1.2 hab2,
        apply trans r2 (trans hb (symm  ha)),},
      exact trans h1 ha,},
  inv_mem' := by {simp only [set.mem_set_of_eq],
      intros x hx,
      rw comm,
      apply (commensurable_inv H x).1 hx,},}

@[simp]
lemma commensurator_mem_iff (H : subgroup G) (g : G) :
  g ∈ (commensurator H) ↔ commensurable (subgroup.conj_subgroup g H) H := iff.rfl

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
  apply trans (symm h1) h2,
  intro h,
  apply trans (trans h1 h) (symm hk),
end

end commensurable
