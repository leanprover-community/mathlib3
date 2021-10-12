import group_theory.index
import group_theory.quotient_group
import tactic.linarith
import group_theory.subgroup.pointwise

namespace commensurable

open_locale pointwise
universe u
variables {G G' : Type*} [group G][group G']

def commensurable (H K : subgroup G) : Prop :=
  subgroup.index (subgroup.subgroup_of H K) ≠ 0 ∧
  subgroup.index (subgroup.subgroup_of K H) ≠ 0

lemma inf_self_eq_self (H :subgroup G)  : (H ⊓ H).comap H.subtype = ⊤ :=
begin
simp only [inf_idem],
ext,
simp only [set_like.coe_mem, subgroup.coe_subtype, subgroup.mem_top, iff_self, subgroup.mem_comap],
end

lemma subgroup_of_top (H : subgroup G) : subgroup.subgroup_of H H = ⊤ :=
begin
rw subgroup.subgroup_of,
have:= inf_self_eq_self H,
simp at *,
exact this,
end

lemma index_of_top  : ( ⊤ : subgroup G).index = 1 :=
begin
rw subgroup.index,
have h3: (cardinal.mk  (quotient_group.quotient (⊤ : subgroup G))) = 1 ,
  by {rw cardinal.eq_one_iff_unique, split, apply quotient_group.subsingleton_quotient_top,
    simp only [nonempty_of_inhabited],},
simp [h3],
end

lemma reflex (H : subgroup G) : commensurable H H :=
begin
rw commensurable,
simp,
have:= subgroup_of_top H,
rw this,
have h2:= index_of_top,
rw h2,
simp,
end


lemma symm (H K : subgroup G) : commensurable H K ↔ commensurable K H :=
begin
simp_rw commensurable,
rw and_comm,
end

def conj_subgroup (g : G) (Γ : subgroup G) : subgroup G := mul_aut.conj g •  Γ


lemma conj_mem  (g : G) (Γ : subgroup G) (h : G) :
  (h ∈ conj_subgroup g Γ) ↔ ∃ x : G, x ∈ Γ ∧ g * x * g⁻¹ = h  :=
iff.rfl
@[simp] lemma conj_mem'  (g : G)  (Γ : subgroup G) (h : G) :
  (h ∈ conj_subgroup g Γ) ↔ ∃ x : Γ, g * x * g⁻¹ = h  :=
subgroup.mem_map.trans subtype.exists'

lemma conj_subgroup_mul (g h : G) (Γ : subgroup G) :
  conj_subgroup (g*h) Γ = conj_subgroup g (conj_subgroup h Γ) :=
begin
simp_rw conj_subgroup,
simp only [monoid_hom.map_mul] at *,
exact mul_smul (mul_aut.conj g) (mul_aut.conj h) Γ,
end

@[simp]
lemma cong_subgroup_id_eq_self (H : subgroup G) : conj_subgroup 1 H = H :=
begin
  ext1, simp at *,
  fsplit,
  work_on_goal 0 { intros h, cases h, rw ← h_h, simp, },
  intros h,
  fsplit,
  work_on_goal 0 { fsplit, work_on_goal 1 { assumption } }, refl,
end

lemma subgroup_of_le (H K L : subgroup G) (h : H ≤ K) : H.subgroup_of L ≤ K.subgroup_of L :=
begin
intros x h, cases x, solve_by_elim,
end


lemma mem_subgroup_of' {H K : subgroup G} {h : K} :
  h ∈ H.subgroup_of K ↔ (h : G) ∈ H ⊓ K :=
begin
rw subgroup.mem_subgroup_of,
simp,
end

def subgroup_of_to_inf (H K : subgroup G) : (H.subgroup_of K) →  H ⊓ K :=
λ x, ⟨K.subtype x, by { simp, cases x, solve_by_elim, }⟩


noncomputable def mapto (H K L : subgroup G) :
  quotient_group.quotient (((H ⊓ K).subgroup_of L).subgroup_of (K.subgroup_of L)) →
  quotient_group.quotient (H.subgroup_of (K ⊓ L)) :=
  λ x, quotient_group.mk (subgroup_of_to_inf K L (x.out'))

lemma maptoinj (H K L : subgroup G) : function.injective (mapto H K L) :=

begin
  rw function.injective,
  intros a b,
  rw mapto,
  simp_rw subgroup_of_to_inf,
  rw quotient_group.eq',
  simp,
  simp_rw ← coe_coe,
  have ha:=  quotient.out_eq' a,
  have hb:=  quotient.out_eq' b,
  rw ← ha,
  rw ← hb,
  intro hab,
  rw quotient_group.eq',
  simp [mem_subgroup_of'] at hab,
  simp [subgroup.mem_subgroup_of, hab],
end



lemma subgroup_of_index_zero_index_zero (H K L : subgroup G) :
  (((H ⊓ K).subgroup_of L).subgroup_of (K.subgroup_of L)).index =0  →
  (H.subgroup_of (K ⊓ L)).index =0 :=
begin
simp_rw subgroup.index,
intro h,
have H1:=cardinal.to_nat_zero_of_injective' (maptoinj H K L),
apply H1 h,
end


lemma index_subgroup_le {H K : subgroup G} (h : H ≤ K)  : K.index =0 → H.index=0 :=
begin
  intro h1,
  have :=subgroup.index_eq_mul_of_le h,
  rw h1 at this,
  simp only [zero_mul] at this,
  apply this,
end

lemma inf_ind_prod (H K L : subgroup G) :
  ((H ⊓ K).subgroup_of L).index =0  →
  (H.subgroup_of L).index=0 ∨ (K.subgroup_of (L ⊓ H)).index = 0 :=
  begin
  have h1: (subgroup.subgroup_of (H ⊓ K)  L) ≤ (subgroup.subgroup_of H  L),
    by {apply subgroup_of_le, simp,},
  have h2:= subgroup.index_eq_mul_of_le h1,
  intro h,
  rw h at h2,
  simp at h2,
  cases h2,
  simp only [h2, true_or, eq_self_iff_true],
  have:= (subgroup_of_index_zero_index_zero K H L),
  have r1 : K ⊓ H = H ⊓ K, by {exact inf_comm,},
  rw r1 at this,
  have ht:= this h2,
  have r2 : H ⊓ L = L ⊓ H, by {exact inf_comm,},
  rw r2 at ht,
  simp only [ht, eq_self_iff_true, or_true],
 end


noncomputable def  inf_quot_map (H K L : subgroup G) :
  quotient_group.quotient (H.subgroup_of (L ⊓ K)) →
  quotient_group.quotient ((H.subgroup_of K)) :=
λ x, quotient_group.mk (⟨x.out', by
  {let y:= x.out', have:=y.property,
    simp only [subgroup.mem_inf, subtype.val_eq_coe] at this, simp_rw ← y, exact this.2, }⟩ : K)

lemma inf_quot_map_injective (H K L : subgroup G) : function.injective (inf_quot_map H K L) :=

begin
  rw function.injective ,
  rw inf_quot_map,
  intros a b,
  intro hab,
  have ha:=  quotient.out_eq' a,
  have hb:=  quotient.out_eq' b,
  rw ← ha,
  rw ← hb,
  simp only [quotient.eq'] at *,
  convert hab,
end



lemma inf_index_zero_subgroup_of_index_zero(H K L : subgroup G) :
  (H.subgroup_of (L ⊓ K)).index =0  →
   (H.subgroup_of K).index =0 :=
begin
  simp_rw subgroup.index,
  intro h,
  have H1:=cardinal.to_nat_zero_of_injective' (inf_quot_map_injective H K L),
  apply H1 h,
end


lemma trans {H K L : subgroup G} (hhk : commensurable H K ) (hkl : commensurable K L) :
  commensurable H L :=
begin
  simp_rw commensurable at *,
  split,
  by_contradiction,
  simp only [not_not, ne.def] at *,
  have s1: (H ⊓ K).subgroup_of L ≤ H.subgroup_of L , by {apply subgroup_of_le, simp,},
  have H1:= index_subgroup_le s1,
  have H2:= H1 h,
  have H3:= inf_ind_prod K H L,
  have H4:= inf_index_zero_subgroup_of_index_zero H K L,
  have r1: H ⊓ K = K ⊓ H, by {apply inf_comm},
  rw r1 at H2,
  have H5:= H3 H2,
  cases H5,
  rw H5 at hkl,
  simp only [eq_self_iff_true, not_true, false_and] at hkl,
  exact hkl,
  have H6:=H4 H5,
  rw H6 at hhk,
  simp only [eq_self_iff_true, not_true, false_and] at hhk,
  exact hhk,
  by_contradiction,
  simp only [not_not, ne.def] at *,
   have s1: (L ⊓ K).subgroup_of H ≤ L.subgroup_of H , by {apply subgroup_of_le, simp,},
  have H1:= index_subgroup_le s1,
  have H2:= H1 h,
  have H3:= inf_ind_prod K L H,
  have H4:= inf_index_zero_subgroup_of_index_zero L K H,
  have r1: L ⊓ K = K ⊓ L, by {apply inf_comm},
  rw r1 at H2,
  have H5:= H3 H2,
  cases H5,
  rw H5 at hhk,
  simp only [eq_self_iff_true, not_true, and_false] at hhk,
  exact hhk,
  have H6:=H4 H5,
  rw H6 at hkl,
  simp only [eq_self_iff_true, not_true, and_false] at hkl,
  exact hkl,
end

noncomputable def conj_map (H K : subgroup G) (g : G) :  quotient_group.quotient (H.subgroup_of K) →
   quotient_group.quotient (  (conj_subgroup g H).subgroup_of (conj_subgroup g K)) :=
  λ x , quotient_group.mk (⟨mul_aut.conj g x.out', by {simp } ⟩ : (conj_subgroup g K))

lemma conj_map_inj (H K : subgroup G) (g : G) : function.injective (conj_map H K g) :=
begin
  rw function.injective,
  intros a b,
  rw conj_map,
  rw quotient_group.eq',
  simp only [mul_aut.conj_apply],
  have ha:=  quotient.out_eq' a,
  have hb:=  quotient.out_eq' b,
  rw ← ha,
  rw ← hb,
  intro hab,
  rw quotient_group.eq',
  simp only [subgroup.mem_subgroup_of, mul_right_inj, conj_mul, quotient.out_eq', conj_inv,
    eq_self_iff_true, conj_mem', subgroup.coe_inv, subgroup.coe_mul, mul_left_inj,
    subgroup.coe_mk] at *,
  cases hab,
  simp_rw  ← hab_h,
  simp only [set_like.coe_mem],
end

lemma conj_mem'' (g x: G ) (H : subgroup G) : g⁻¹ * x * g ∈ H ↔ x ∈ (conj_subgroup g H) :=
begin
  simp only [conj_mem'],
  split,
  intro h,
  use g⁻¹*x*g,
  apply h,
  simp only [subgroup.coe_mk],
  simp_rw ← mul_assoc,
  simp only [one_mul, mul_right_inv, mul_inv_cancel_right],
  intro h,
  cases h,
  rw ← h_h,
  simp_rw ← mul_assoc,
  simp only [set_like.coe_mem, one_mul, mul_left_inv, inv_mul_cancel_right],
end

noncomputable def conj_map_inv (H K : subgroup G) (g : G) :
  quotient_group.quotient (  (conj_subgroup g H).subgroup_of (conj_subgroup g K)) →
  quotient_group.quotient (H.subgroup_of K) :=
   λ x , quotient_group.mk (⟨(mul_aut.conj g)⁻¹ x.out', by
   {simp,
    rw conj_mem'' _ _ _,
    exact set_like.coe_mem (quotient.out' x),} ⟩ :  K)


lemma conj_map_inv_inj (H K : subgroup G) (g : G) : function.injective (conj_map_inv H K g) :=
begin
  rw function.injective,
  intros a b,
  rw conj_map_inv,
  rw quotient_group.eq',
  simp only [mul_aut.conj_inv_apply],
  have ha:=  quotient.out_eq' a,
  have hb:=  quotient.out_eq' b,
  rw ← ha,
  rw ← hb,
  intro hab,
  rw quotient_group.eq',
  simp only [subgroup.mem_subgroup_of, mul_inv_rev, quotient.out_eq', eq_self_iff_true, conj_mem',
   subgroup.coe_inv,  subgroup.coe_mul, inv_inv, subgroup.coe_mk] at *,
  simp_rw ← mul_assoc at hab,
  simp only [mul_inv_cancel_right] at hab,
  use  g⁻¹ * (↑(quotient.out' a))⁻¹ * ↑(quotient.out' b) * g,
  apply hab,
  simp only [subgroup.coe_mk],
  simp_rw ← mul_assoc ,
  simp only [one_mul, mul_right_inv, mul_inv_cancel_right],
end

noncomputable lemma Cantor_Bernstein {α : Type u} {β : Type u} (f: α → β) (g : β → α )
    (h1 : function.injective f) (h2 :function.injective g) : α ≃ β :=
begin
have c1 := cardinal.mk_le_of_injective h1,
have c2 :=cardinal.mk_le_of_injective h2,
have c3 : cardinal.mk α =cardinal.mk β , by {exact le_antisymm c1 c2,  },
have:= (cardinal.eq.1 c3),
apply this.some,
end



noncomputable lemma  quot_conj_equiv (H K : subgroup G) (g : G) :
   quotient_group.quotient (H.subgroup_of K) ≃
   quotient_group.quotient (  (conj_subgroup g H).subgroup_of (conj_subgroup g K)) :=
begin
apply Cantor_Bernstein _ _ (conj_map_inj H K g) (conj_map_inv_inj H K g),
end



lemma comm_conj {H K : subgroup G} (g : G):
  commensurable H K  ↔ commensurable (conj_subgroup g H) (conj_subgroup g K) :=
begin
  simp_rw commensurable,
  simp_rw subgroup.index,
  have h1:= quot_conj_equiv H K g,
  have h11:= cardinal.mk_congr h1,
  have h2:= quot_conj_equiv K H g,
  have h22:= cardinal.mk_congr h2,
  rw h11,
  rw h22,
end

lemma comm_inv (H : subgroup G) (g : G) :
  commensurable (conj_subgroup g H) H ↔ commensurable H (conj_subgroup g⁻¹ H)  :=
begin
  rw comm_conj g⁻¹ ,
  rw ← conj_subgroup_mul g⁻¹ g,
  simp only [mul_left_inv, cong_subgroup_id_eq_self],
end

def commensurator (H : subgroup G) : subgroup G :={
carrier := {g : G | commensurable (conj_subgroup g H) H },
one_mem' := by {simp, apply reflex, },
mul_mem' := by {intros a b ha hb,
    simp only [set.mem_set_of_eq] at *,
    rw conj_subgroup_mul,
    have h1: commensurable (conj_subgroup a (conj_subgroup b H)) (conj_subgroup a H), by {
    have hab:= trans ha hb.symm,
    rw (comm_conj a⁻¹) at hab,
    rw ← conj_subgroup_mul at hab,
    simp only [mul_left_inv, cong_subgroup_id_eq_self] at hab,
    have r1:= comm_inv (conj_subgroup b H) a,
    have hab2:= trans hb hab,
    have r2:= r1.2 hab2,
    apply trans r2 (trans hb ha.symm),},
    exact trans h1 ha,},
inv_mem' := by {simp only [set.mem_set_of_eq],
    intros x hx,
    rw symm,
    apply (comm_inv H x).1 hx,},
}


end commensurable
