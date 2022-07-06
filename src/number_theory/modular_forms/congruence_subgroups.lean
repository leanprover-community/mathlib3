/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import linear_algebra.special_linear_group
import data.zmod.basic
import group_theory.subgroup.pointwise
import group_theory.group_action.conj_act
/-!
# Congruence subgroups

This defines congruence subgroups of `SL(2,ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/

local notation `SL(` n `, ` R `)`:= matrix.special_linear_group (fin n) R

local attribute [-instance] matrix.special_linear_group.has_coe_to_fun

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

open matrix.special_linear_group matrix

lemma SL2_inv_expl (A : SL(2, ℤ)) : A⁻¹ = ⟨![![A.1 1 1, -A.1 0 1], ![-A.1 1 0 , A.1 0 0]],
  by { rw matrix.det_fin_two, simp, have := A.2, rw matrix.det_fin_two at this, rw mul_comm,
    convert this, }⟩ :=
begin
ext,
  rw coe_inv,
  have := matrix.adjugate_fin_two A.1,
  simp at this,
  rw this,
  refl,
end

@[simp] lemma mat_mul_expl {R : Type*} [comm_ring R] (A B : matrix (fin 2) (fin 2) R) :
  (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧
  (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
  (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧
  (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 :=
begin
  split, work_on_goal 2 {split}, work_on_goal 3 {split},
  all_goals {simp only [matrix.mul_eq_mul],
  rw matrix.mul_apply,
  rw finset.sum_fin_eq_sum_range,
  rw finset.sum_range_succ,
  rw finset.sum_range_succ,
  simp only [nat.succ_pos', lt_self_iff_false, dite_eq_ite, fin.mk_zero,
  forall_false_left, if_true, finset.sum_empty, not_le,
    finset.range_zero, nat.one_lt_bit0_iff, zero_add, add_right_inj, fin.mk_one, subtype.val_eq_coe,
    ite_eq_left_iff]},
end

lemma SL2_mat_mul_expl (A B : SL(2, ℤ)) :
  (A * B).1 0 0 = A.1 0 0 * B.1 0 0 + (A.1 0 1) * (B.1 1 0) ∧
  (A * B).1 0 1 = A.1 0 0 * B.1 0 1 + A.1 0 1 * B.1 1 1 ∧
  (A * B).1 1 0 = A.1 1 0 * B.1 0 0 + A.1 1 1 * B.1 1 0 ∧
  (A * B).1 1 1 = A.1 1 0 * B.1 0 1 + A.1 1 1 * B.1 1 1 :=
begin
  simp,
  convert (mat_mul_expl A.1 B.1),
end


def red_map (N : ℕ) : ℤ →+* (zmod N) := int.cast_ring_hom _

def SL_mod_map (N : ℕ) : SL(2, ℤ) →* SL(2, (zmod N)) := map (red_map N)


@[simp]
lemma sl_map_val (N : ℕ) (γ : SL(2, ℤ)) : ∀ i j, ↑ₘ(SL_mod_map N γ) i j = ((↑ₘγ i j) : zmod N) :=
begin
  intros i j,
  refl,
end

def Gamma_N (N : ℕ) : subgroup SL(2, ℤ) := (SL_mod_map N).ker

lemma Gamma_N_mem' (N : ℕ) (γ : SL(2, ℤ)) : γ ∈ (Gamma_N N) ↔ (SL_mod_map N γ) = 1 := iff.rfl

@[simp]
lemma Gamma_N_mem (N : ℕ) (γ : SL(2, ℤ)) : γ ∈ (Gamma_N N) ↔ ((↑ₘγ 0 0) : zmod N) = 1 ∧
  ((↑ₘγ 0 1) : zmod N) = 0 ∧ ((↑ₘγ 1 0) : zmod N) = 0 ∧ ((↑ₘγ 1 1) : zmod N) = 1 :=
begin
  rw Gamma_N_mem',
  split,
  { intro h,
    simp [←(sl_map_val N γ), h] },
  { intro h,
    ext,
    rw sl_map_val N γ,
    fin_cases i; fin_cases j,
    all_goals {simp_rw h, refl} }
end

lemma Gamma_N_normal (N : ℕ) : subgroup.normal (Gamma_N N) := (SL_mod_map N).normal_ker

def is_congruence_subgroup (Γ : subgroup SL(2, ℤ)) : Prop := ∃ (N : ℕ), (Gamma_N N) ≤ Γ

lemma is_congruence_subgroup_trans (H K : subgroup SL(2, ℤ)) (h: H ≤ K)
  (h2 : is_congruence_subgroup H) : is_congruence_subgroup K :=
begin
  obtain ⟨N , hN⟩ := h2,
  refine ⟨N, le_trans hN h⟩,
end

lemma Gamma_N_is_cong_sub (N : ℕ) : is_congruence_subgroup (Gamma_N N) :=
begin
  refine ⟨N, by {simp only [le_refl]}⟩,
end

def Gamma0_N (N : ℕ) : subgroup SL(2, ℤ) :=
{ carrier := { g : SL(2, ℤ) | (↑ₘg 1 0 : zmod N) = 0 },
  one_mem' := by { simp },
  mul_mem':= by {intros a b ha hb,
    simp only [ set.mem_set_of_eq],
    have h := ((SL2_mat_mul_expl a b).2.2.1),
    simp only [coe_coe, coe_matrix_coe, coe_mul, int.coe_cast_ring_hom, map_apply,
      set.mem_set_of_eq, subtype.val_eq_coe] at *,
    rw h,
    simp [ha, hb] },
  inv_mem':= by {intros a ha,
    simp only [ set.mem_set_of_eq, subtype.val_eq_coe],
    rw (SL2_inv_expl a),
    simp only [subtype.val_eq_coe, cons_val_zero, cons_val_one, head_cons, coe_coe, coe_matrix_coe,
      coe_mk, int.coe_cast_ring_hom, map_apply, int.cast_neg, neg_eq_zero, set.mem_set_of_eq] at *,
    exact ha } }

@[simp]
lemma Gamma0_N_mem (N : ℕ) (A: SL(2, ℤ)) : A ∈ (Gamma0_N N) ↔ ((↑ₘA) 1 0 : zmod N) = 0 :=iff.rfl

lemma Gamma0_det (N : ℕ) (A : Gamma0_N N) : (A.1.1.det : zmod N) = 1 :=
begin
  have ha:= A.1.property,
  rw ha,
  simp,
end

def Gamma_0_map (N : ℕ): (Gamma0_N N) →* (zmod N) :=
{ to_fun := λ g, (↑ₘg 1 1 : zmod N),
  map_one' := by { simp, },
  map_mul' := by {intros A B,
  have := (SL2_mat_mul_expl A B).2.2.2,
  simp at *,
  rw this,
  have ha:= A.property,
  simp at *,
  rw ha,
  simp,} }

def Gamma1_N' (N : ℕ) : subgroup (Gamma0_N N) := (Gamma_0_map N).ker

@[simp]
lemma Gamma1_N_mem' (N : ℕ) (γ :(Gamma0_N N)) : γ ∈ (Gamma1_N' N) ↔ ((Gamma_0_map N) γ) = 1 :=
iff.rfl

lemma Gamma1_to_Gamma0_mem (N : ℕ) (A : Gamma0_N N) : A ∈ (Gamma1_N' N) ↔
  (↑ₘA 0 0 : zmod N) = 1 ∧ (↑ₘA 1 1 : zmod N) = 1 ∧ (↑ₘA 1 0 : zmod N) = 0 :=
begin
  split,
  intro ha,
  have hA := A.property,
  rw Gamma0_N_mem at hA,
  have adet := Gamma0_det N A,
  rw matrix.det_fin_two at adet,
  simp only [Gamma_0_map, coe_coe, coe_matrix_coe, int.coe_cast_ring_hom, map_apply, Gamma1_N_mem',
    monoid_hom.coe_mk, subtype.val_eq_coe, int.cast_sub, int.cast_mul] at *,
  rw [hA, ha] at adet,
  simp only [mul_one, mul_zero, sub_zero] at adet,
  simp only [adet, hA, ha, eq_self_iff_true, and_self],
  intro ha,
  simp only [Gamma1_N_mem', Gamma_0_map, monoid_hom.coe_mk, coe_coe, coe_matrix_coe,
    int.coe_cast_ring_hom, map_apply],
  exact ha.2.1,
end

def Gamma1_map (N : ℕ) : (Gamma1_N' N) →* SL(2, ℤ) :=
((Gamma0_N N).subtype).comp (Gamma1_N' N).subtype

def Gamma1_N (N : ℕ) : subgroup SL(2, ℤ) := subgroup.map (Gamma1_map N) ⊤

@[simp]
lemma Gamma1_N_mem (N : ℕ) (A : SL(2, ℤ)) : A ∈ (Gamma1_N N) ↔
  (↑ₘA 0 0 : zmod N) = 1 ∧ (↑ₘA 1 1 : zmod N) = 1 ∧ (↑ₘA 1 0 : zmod N) = 0 :=
begin
  split,
  { intro ha,
    simp_rw [Gamma1_N, subgroup.mem_map, Gamma1_map] at ha,
    simp at ha,
    obtain ⟨⟨x, hx⟩, hxx⟩ := ha,
    rw Gamma1_to_Gamma0_mem at hx,
    rw ←hxx,
    convert hx },
  { intro ha,
    simp_rw [Gamma1_N, subgroup.mem_map],
    have hA : A ∈ (Gamma0_N N), by {simp [ha.right.right, Gamma0_N_mem, subtype.val_eq_coe],},
    have HA : (⟨A , hA⟩ : Gamma0_N N) ∈ Gamma1_N' N,
      by {simp only [Gamma1_to_Gamma0_mem, subgroup.coe_mk, coe_coe, coe_matrix_coe,
        int.coe_cast_ring_hom, map_apply],
      exact ha,},
    refine ⟨(⟨ (⟨A , hA⟩ : Gamma0_N N), HA ⟩ : (( Gamma1_N' N ) : subgroup (Gamma0_N N))), _⟩,
    rw Gamma1_map,
    simp }
end

lemma Gamma1_in_Gamma0 (N : ℕ) : (Gamma1_N N) ≤ (Gamma0_N N) :=
begin
  intros x HA,
  simp only [Gamma0_N_mem, Gamma1_N_mem, coe_coe, coe_matrix_coe, int.coe_cast_ring_hom,
    map_apply] at *,
  exact HA.2.2,
end

lemma Gamma1_N_is_congruence (N : ℕ) : is_congruence_subgroup (Gamma1_N N) :=
begin
  refine ⟨N, _⟩,
  intros A hA,
  simp only [Gamma1_N_mem, Gamma_N_mem] at *,
  simp only [hA, eq_self_iff_true, and_self],
end

lemma Gamma0_N_is_congruence (N : ℕ) : is_congruence_subgroup (Gamma0_N N) :=
begin
  apply is_congruence_subgroup_trans _ _ (Gamma1_in_Gamma0 N) (Gamma1_N_is_congruence N),
end

section conjugation

open_locale pointwise

lemma conj_act_normal {G : Type*} [group G] {H : subgroup G} (hH : H.normal ) (g : conj_act G) :
  g • H = H :=
begin
  ext,
  split,
  intro h,
  have := hH.conj_mem (g⁻¹ • x) _ (conj_act.of_conj_act g),
  rw subgroup.mem_pointwise_smul_iff_inv_smul_mem at h,
  dsimp at *,
  rw conj_act.smul_def at *,
  simp only [conj_act.of_conj_act_inv, conj_act.of_conj_act_to_conj_act, inv_inv] at *,
  convert this,
  simp_rw ←mul_assoc,
  simp only [mul_right_inv, one_mul, mul_inv_cancel_right],
  rw subgroup.mem_pointwise_smul_iff_inv_smul_mem at h,
  exact h,
  intro h,
  rw subgroup.mem_pointwise_smul_iff_inv_smul_mem,
  rw conj_act.smul_def at *,
  apply hH.conj_mem,
  exact h,
end

lemma Gamma_N_cong_eq_self (N : ℕ) (g : conj_act SL(2, ℤ)) : g • (Gamma_N N) = (Gamma_N N) :=
begin
apply conj_act_normal (Gamma_N_normal N),
end

lemma subgroup_conj_covariant (g : conj_act SL(2, ℤ)) (Γ_1 Γ_2 : subgroup SL(2, ℤ))
  (h : Γ_1 ≤ Γ_2) : ( g • Γ_1) ≤ (g • Γ_2) :=
begin
  simp [h],
end

lemma conj_cong_is_cong (g : conj_act SL(2, ℤ)) (Γ : subgroup SL(2, ℤ))
  (h : is_congruence_subgroup Γ) : is_congruence_subgroup (g • Γ) :=
begin
  simp_rw is_congruence_subgroup at *,
  obtain⟨ N, HN⟩:= h,
  use N,
  rw ←Gamma_N_cong_eq_self N g,
  apply subgroup_conj_covariant,
  exact HN,
end

end conjugation
