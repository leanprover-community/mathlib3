import group_theory.index
import group_theory.quotient_group
import tactic.linarith
import group_theory.subgroup.pointwise

namespace commensurable

open_locale pointwise

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


def conj_subgroup (g : G) (Γ : subgroup G) : subgroup G := mul_aut.conj g •  Γ


lemma conj_mem  (g : G) (Γ : subgroup G) (h : G) :
  (h ∈ conj_subgroup g Γ) ↔ ∃ x : G, x ∈ Γ ∧ g * x * g⁻¹ = h  :=
iff.rfl
@[simp] lemma conj_mem'  (g : G)  (Γ : subgroup G) (h : G) :
  (h ∈ conj_subgroup g Γ) ↔ ∃ x : Γ, g * x * g⁻¹ = h  :=
subgroup.mem_map.trans subtype.exists'

lemma cong_subgroup_id_eq_self (H : subgroup G) : conj_subgroup 1 H = H :=
begin
  ext1, simp at *,
  fsplit,
  work_on_goal 0 { intros h, cases h, rw ← h_h, simp, },
  intros h,
  fsplit,
  work_on_goal 0 { fsplit, work_on_goal 1 { assumption } }, refl,
end

lemma sub_to_inter (H K : subgroup G) ( x : (H.subgroup_of K)) : x.1.1 ∈  H :=
begin
simp,
cases x,
assumption,
end

def maap (H K : subgroup G) : (H.subgroup_of K) →  H ⊓ K :=
λ x, (⟨x.1, by { have:= sub_to_inter H K x,simp, apply this, }⟩ :  H ⊓ K)

def paam (H K : subgroup G) : H ⊓ K → (H.subgroup_of K) :=
λ x, ( ⟨(⟨x.1, by {cases x, tidy,} ⟩ : K), by {tidy,}⟩ : (H.subgroup_of K))



noncomputable def quotient_map_subgroup_of_of_le' {A' A B' B : subgroup G}
  (h' : A' ≤ B') (h : A ≤ B) :
  quotient_group.quotient (A'.subgroup_of A) → quotient_group.quotient (B'.subgroup_of B) :=
λ x, quotient_group.mk (⟨x.out', by {sorry} ⟩  : B)

lemma a1 (H K L : subgroup G) :
    ((H ⊓ K).subgroup_of L).map L.subtype = (H .subgroup_of (K ⊓ L)).map (K ⊓ L).subtype :=
begin
have h1:= subgroup.subgroup_of_map_subtype (H ⊓ K) L,
have h2:=  subgroup.subgroup_of_map_subtype H (K ⊓ L),
rw ← inf_assoc at h2,rw h1, rw h2,
end


lemma subgroup_of_le (H K L : subgroup G) (h : H ≤ K) : H.subgroup_of L ≤ K.subgroup_of L :=
begin
intros x h, cases x, solve_by_elim,
end

lemma a2 (H K L : subgroup G):
  ((((H ⊓ K).subgroup_of L).subgroup_of (K.subgroup_of L)).map (K.subgroup_of L).subtype).map L.subtype  =
  (( H.subgroup_of (K ⊓ L) ).map ((K ⊓ L)).subtype) :=
 begin
simp_rw [subgroup.subgroup_of_map_subtype],
have h1:= subgroup.subgroup_of_map_subtype ((H ⊓ K).subgroup_of L) (K.subgroup_of L),
have : ((H ⊓ K).subgroup_of L) ⊓  (K.subgroup_of L) =  ((H ⊓ K).subgroup_of L),
  by {simp, apply subgroup_of_le, simp,},
rw this,
simp_rw [subgroup.subgroup_of_map_subtype],
rw inf_assoc,
 end


noncomputable def  inf_quot_cast (H K L : subgroup G) :
  quotient_group.quotient (((H ⊓ K).subgroup_of L).subgroup_of (K.subgroup_of L)) ≃
  quotient_group.quotient (H.subgroup_of (K ⊓ L)) :={
    to_fun := λ x, maap K L (x.out'),
    inv_fun:= λ x, paam K L x.out',
    left_inv:= by {rw maap, rw paam, simp, intro x, simp, sorry,},
    right_inv:= by {sorry,},


  }

/--/
noncomputable def  inf_quot_cast (H K L : subgroup G) :
  quotient_group.quotient (((H ⊓ K).subgroup_of L).subgroup_of (K.subgroup_of L)) ≃
  quotient_group.quotient (H.subgroup_of (K ⊓ L)) :={
    to_fun := λ x, maap K L (x.out'),
    inv_fun:= λ x, paam K L x.out',
    left_inv:= by {rw maap, rw paam, simp, sorry,},
    right_inv:= by {sorry,},


  }



lemma index_triple_int (H K L : subgroup G) :
  (subgroup.subgroup_of (H ⊓ K)  L).index =
  (subgroup.subgroup_of K  L).index *  (subgroup.subgroup_of H (K ⊓ L)).index :=

begin
have h1: (subgroup.subgroup_of (H ⊓ K)  L) ≤ (subgroup.subgroup_of K  L), by {sorry,},
have h2:= subgroup.index_eq_mul_of_le h1,
simp [h2],
have H:
  (((H ⊓ K).subgroup_of L).subgroup_of (K.subgroup_of L)).index = (H.subgroup_of (K ⊓ L)).index,
    by {
       apply congr_arg cardinal.to_nat,
       apply  cardinal.mk_congr,



       sorry,},
simp [H],
end
-/

lemma index_subgroup_le {H K : subgroup G} (h : H ≤ K)  : K.index =0 → H.index=0 :=
begin
intro h1,
have :=subgroup.index_eq_mul_of_le h,
rw h1 at this,
simp at this,
apply this,
end





lemma inf_ind_prod (H K L : subgroup G) :
   ((H ⊓ K).subgroup_of L).index =0  →
   (H.subgroup_of L).index=0 ∨ (K.subgroup_of (L ⊓ H)).index = 0 :=
 begin
have h1: (subgroup.subgroup_of (H ⊓ K)  L) ≤ (subgroup.subgroup_of H  L), by {apply subgroup_of_le, simp,},
have h2:= subgroup.index_eq_mul_of_le h1,
intro h,
rw h at h2,
simp at h2,
cases h2,
simp [h2],


sorry,
 end


noncomputable def  inf_quot_map (H K L : subgroup G) :
  quotient_group.quotient (H.subgroup_of (L ⊓ K)) →
  quotient_group.quotient ((H.subgroup_of K)) :=
λ x, quotient_group.mk (⟨x.out', by
  {let y:= x.out', have:=y.property, simp  at this, simp_rw ← y, exact this.2, }⟩ : K)

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
rw quotient.eq',
simp at hab,
convert hab,
end



lemma aux (H K L : subgroup G) :
  (H.subgroup_of (L ⊓ K)).index =0  →
   (H.subgroup_of K).index =0 :=
begin
simp_rw subgroup.index,
intro h,
have H1:=cardinal.to_nat_zero_of_injective' (inf_quot_map_injective H K L),
apply H1 h,
end


lemma trans (H K L : subgroup G) (hhk : commensurable H K ) (hkl : commensurable K L) :
  commensurable H L :=
begin
  simp_rw commensurable at *,
  split,
  by_contradiction,
  simp at *,
  have s1: (H ⊓ K).subgroup_of L ≤ H.subgroup_of L , by {apply subgroup_of_le, simp,},
  have H1:= index_subgroup_le s1,
  have H2:= H1 h,
  have H3:= inf_ind_prod K H L,
  have H4:= aux H K L,
  have r1: H ⊓ K = K ⊓ H, by {apply inf_comm},
  rw r1 at H2,
  have H5:= H3 H2,
  cases H5,
  rw H5 at hkl,
  simp at hkl,
  exact hkl,
  have H6:=H4 H5,
  rw H6 at hhk,
  simp at hhk,
  exact hhk,
  by_contradiction,
  simp at *,
   have s1: (L ⊓ K).subgroup_of H ≤ L.subgroup_of H , by {apply subgroup_of_le, simp,},
  have H1:= index_subgroup_le s1,
  have H2:= H1 h,
  have H3:= inf_ind_prod K L H,
  have H4:= aux L K H,
  have r1: L ⊓ K = K ⊓ L, by {apply inf_comm},
  rw r1 at H2,
  have H5:= H3 H2,
  cases H5,
  rw H5 at hhk,
  simp at hhk,
  exact hhk,
  have H6:=H4 H5,
  rw H6 at hkl,
  simp at hkl,
  exact hkl,
end

def commensurator (H : subgroup G) : subgroup G :={
carrier := {g : G | commensurable (conj_subgroup g H) H },
one_mem' := by {simp, rw cong_subgroup_id_eq_self  H, apply reflex, },
mul_mem' := by {sorry,},
inv_mem' := by {sorry,},

}


end commensurable
