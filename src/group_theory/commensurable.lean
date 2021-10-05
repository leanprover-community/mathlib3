import group_theory.index
import group_theory.quotient_group
import tactic.linarith
import group_theory.subgroup.pointwise

namespace commensurable

open_locale pointwise

variables {G : Type*} [group G]

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



@[simp]
lemma conf_cong_mem  (g : G)  (Γ : subgroup G) (h : G) :
 (h ∈ conj_subgroup g Γ) ↔ ∃ x : Γ, g * x * g⁻¹ = h  :=
begin
  rw conj_subgroup,
  split,
  intro h,
  cases h,
  use h_w,
  apply h_h.1,
  simp at *,
  apply h_h.2,
  intro h,
  cases h,
  rw ← h_h,
  sorry,
end

lemma cong_subgroup_id_eq_self (H : subgroup G) : conj_subgroup 1 H = H :=
begin
  ext1, simp at *,
  fsplit,
  work_on_goal 0 { intros h, cases h, rw ← h_h, simp, },
  intros h,
  fsplit,
  work_on_goal 0 { fsplit, work_on_goal 1 { assumption } }, refl,
end

lemma sub_to_inter (H K : subgroup G) ( x : (H.subgroup_of K)) : x.1.1 ∈ H ⊓ K :=
begin
simp,
cases x, assumption,
end

def maap (H K : subgroup G) : (H.subgroup_of K) → H ⊓ K :=
λ x, (⟨x.1.1, sub_to_inter H K x⟩ : H ⊓ K)

def paam (H K : subgroup G) : H ⊓ K → (H.subgroup_of K) :=
λ x, ( ⟨(⟨x.1, by {cases x, tidy,} ⟩ : K), by {tidy,}⟩ : (H.subgroup_of K))



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


lemma trans (H K L : subgroup G) (h1 : commensurable H K ) (h2 : commensurable K L) :
  commensurable H K :=
begin
sorry,
end

def commensurator (H : subgroup G) : subgroup G :={
carrier := {g : G | commensurable (conj_subgroup g H) H },
one_mem' := by {simp, rw cong_subgroup_id_eq_self  H, apply reflex, },
mul_mem' := by {sorry,},
inv_mem' := by {sorry,},

}


end commensurable
