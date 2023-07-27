/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import data.zmod.basic
import group_theory.group_action.conj_act
import group_theory.subgroup.pointwise
import linear_algebra.matrix.special_linear_group
/-!
# Congruence subgroups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines congruence subgroups of `SL(2, ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/

local notation `SL(` n `, ` R `)`:= matrix.special_linear_group (fin n) R

local attribute [-instance] matrix.special_linear_group.has_coe_to_fun

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

open matrix.special_linear_group matrix

variable (N : ℕ)

local notation `SLMOD(`N`)`  := @matrix.special_linear_group.map (fin 2) _ _ _ _ _ _
  (int.cast_ring_hom (zmod N))

@[simp]
lemma SL_reduction_mod_hom_val (N : ℕ) (γ : SL(2, ℤ)) : ∀ (i j : fin 2),
  ((SLMOD(N) γ) : (matrix (fin 2) (fin 2) (zmod N))) i j =
  (((↑ₘγ i j) : ℤ) : zmod N) := λ i j, rfl

/--The full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to the identity
modulo `N`.-/
def Gamma (N : ℕ) : subgroup SL(2, ℤ) := (SLMOD(N)).ker

lemma Gamma_mem' (N : ℕ) (γ : SL(2, ℤ)) : γ ∈ Gamma N ↔ SLMOD(N) γ = 1 := iff.rfl

@[simp]
lemma Gamma_mem (N : ℕ) (γ : SL(2, ℤ)) : γ ∈ Gamma N ↔ (((↑ₘγ 0 0) : ℤ) : zmod N) = 1 ∧
  (((↑ₘγ 0 1) : ℤ) : zmod N) = 0 ∧ (((↑ₘγ 1 0) : ℤ) : zmod N) = 0 ∧
  (((↑ₘγ 1 1) : ℤ) : zmod N) = 1 :=
begin
  rw Gamma_mem',
  split,
  { intro h,
    simp [←(SL_reduction_mod_hom_val N γ), h] },
  { intro h,
    ext,
    rw SL_reduction_mod_hom_val N γ,
    fin_cases i; fin_cases j,
    all_goals {simp_rw h, refl} }
end

lemma Gamma_normal (N : ℕ) : subgroup.normal (Gamma N) := (SLMOD(N)).normal_ker

lemma Gamma_one_top : Gamma 1 = ⊤ :=
begin
  ext,
  simp,
end

lemma Gamma_zero_bot : Gamma 0 = ⊥ :=
begin
  ext,
  simp only [Gamma_mem, coe_coe, coe_matrix_coe, int.coe_cast_ring_hom, map_apply, int.cast_id,
    subgroup.mem_bot],
  split,
  { intro h,
    ext,
    fin_cases i; fin_cases j,
    any_goals {simp [h]} },
  { intro h,
    simp [h] }
end

/--The congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry reduces to zero
modulo `N`. -/
def Gamma0 (N : ℕ) : subgroup SL(2, ℤ) :=
{ carrier := { g : SL(2, ℤ) | ((↑ₘg 1 0 : ℤ) : zmod N) = 0 },
  one_mem' := by { simp },
  mul_mem':= by {intros a b ha hb,
    simp only [ set.mem_set_of_eq],
    have h := ((matrix.two_mul_expl a.1 b.1).2.2.1),
    simp only [coe_coe, coe_matrix_coe, coe_mul, int.coe_cast_ring_hom, map_apply,
      set.mem_set_of_eq, subtype.val_eq_coe, mul_eq_mul] at *,
    rw h,
    simp [ha, hb] },
  inv_mem':= by {intros a ha,
    simp only [ set.mem_set_of_eq, subtype.val_eq_coe],
    rw (SL2_inv_expl a),
    simp only [subtype.val_eq_coe, cons_val_zero, cons_val_one, head_cons, coe_coe, coe_matrix_coe,
      coe_mk, int.coe_cast_ring_hom, map_apply, int.cast_neg, neg_eq_zero, set.mem_set_of_eq] at *,
    exact ha } }

@[simp]
lemma Gamma0_mem (N : ℕ) (A: SL(2, ℤ)) : A ∈ Gamma0 N ↔ (((↑ₘA) 1 0 : ℤ) : zmod N) = 0 := iff.rfl

lemma Gamma0_det (N : ℕ) (A : Gamma0 N) : (A.1.1.det : zmod N) = 1 :=
by {simp [A.1.property]}

/--The group homomorphism from `Gamma0` to `zmod N` given by mapping a matrix to its lower
right-hand entry. -/
def Gamma_0_map (N : ℕ): Gamma0 N →* zmod N :=
{ to_fun := λ g, ((↑ₘg 1 1 : ℤ) : zmod N),
  map_one' := by { simp, },
  map_mul' := by {intros A B,
  have := (two_mul_expl A.1.1 B.1.1).2.2.2,
  simp only [coe_coe, subgroup.coe_mul, coe_matrix_coe, coe_mul, int.coe_cast_ring_hom, map_apply,
    subtype.val_eq_coe, mul_eq_mul] at *,
  rw this,
  have ha := A.property,
  simp only [int.cast_add, int.cast_mul, add_left_eq_self, subtype.val_eq_coe, Gamma0_mem, coe_coe,
    coe_matrix_coe, int.coe_cast_ring_hom, map_apply] at *,
  rw ha,
  simp,} }

/--The congruence subgroup `Gamma1` (as a subgroup of `Gamma0`) of matrices whose bottom
row is congruent to `(0,1)` modulo `N`.-/
def Gamma1' (N : ℕ) : subgroup (Gamma0 N) := (Gamma_0_map N).ker

@[simp]
lemma Gamma1_mem' (N : ℕ) (γ : Gamma0 N) : γ ∈ Gamma1' N ↔ (Gamma_0_map N) γ = 1 := iff.rfl

lemma Gamma1_to_Gamma0_mem (N : ℕ) (A : Gamma0 N) : A ∈ Gamma1' N ↔
  ((↑ₘA 0 0 : ℤ) : zmod N) = 1 ∧ ((↑ₘA 1 1 : ℤ) : zmod N) = 1 ∧ ((↑ₘA 1 0 : ℤ) : zmod N) = 0 :=
begin
  split,
  { intro ha,
    have hA := A.property,
    rw Gamma0_mem at hA,
    have adet := Gamma0_det N A,
    rw matrix.det_fin_two at adet,
    simp only [Gamma_0_map, coe_coe, coe_matrix_coe, int.coe_cast_ring_hom, map_apply, Gamma1_mem',
      monoid_hom.coe_mk, subtype.val_eq_coe, int.cast_sub, int.cast_mul] at *,
    rw [hA, ha] at adet,
    simp only [mul_one, mul_zero, sub_zero] at adet,
    simp only [adet, hA, ha, eq_self_iff_true, and_self]},
  { intro ha,
    simp only [Gamma1_mem', Gamma_0_map, monoid_hom.coe_mk, coe_coe, coe_matrix_coe,
      int.coe_cast_ring_hom, map_apply],
    exact ha.2.1,}
end

/--The congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices whose bottom
row is congruent to `(0,1)` modulo `N`. -/
def Gamma1 (N : ℕ) : subgroup SL(2, ℤ) := subgroup.map
(((Gamma0 N).subtype).comp (Gamma1' N).subtype) ⊤

@[simp]
lemma Gamma1_mem (N : ℕ) (A : SL(2, ℤ)) : A ∈ Gamma1 N ↔
  ((↑ₘA 0 0 : ℤ) : zmod N) = 1 ∧ ((↑ₘA 1 1 : ℤ) : zmod N) = 1 ∧ ((↑ₘA 1 0 : ℤ) : zmod N) = 0 :=
begin
  split,
  { intro ha,
    simp_rw [Gamma1, subgroup.mem_map] at ha,
    simp at ha,
    obtain ⟨⟨x, hx⟩, hxx⟩ := ha,
    rw Gamma1_to_Gamma0_mem at hx,
    rw ←hxx,
    convert hx },
  { intro ha,
    simp_rw [Gamma1, subgroup.mem_map],
    have hA : A ∈ (Gamma0 N), by {simp [ha.right.right, Gamma0_mem, subtype.val_eq_coe],},
    have HA : (⟨A , hA⟩ : Gamma0 N) ∈ Gamma1' N,
      by {simp only [Gamma1_to_Gamma0_mem, subgroup.coe_mk, coe_coe, coe_matrix_coe,
        int.coe_cast_ring_hom, map_apply],
      exact ha,},
    refine ⟨(⟨(⟨A , hA⟩ : Gamma0 N), HA ⟩ : (( Gamma1' N ) : subgroup (Gamma0 N))), _⟩,
    simp }
end

lemma Gamma1_in_Gamma0 (N : ℕ) : Gamma1 N ≤ Gamma0 N :=
begin
  intros x HA,
  simp only [Gamma0_mem, Gamma1_mem, coe_coe, coe_matrix_coe, int.coe_cast_ring_hom,
    map_apply] at *,
  exact HA.2.2,
end

section congruence_subgroup

/--A congruence subgroup is a subgroup of `SL(2, ℤ)` which contains some `Gamma N` for some
`(N : ℕ+)`. -/
def is_congruence_subgroup (Γ : subgroup SL(2, ℤ)) : Prop := ∃ (N : ℕ+), Gamma N ≤ Γ

lemma is_congruence_subgroup_trans (H K : subgroup SL(2, ℤ)) (h: H ≤ K)
  (h2 : is_congruence_subgroup H) : is_congruence_subgroup K :=
begin
  obtain ⟨N , hN⟩ := h2,
  refine ⟨N, le_trans hN h⟩,
end

lemma Gamma_is_cong_sub (N : ℕ+) : is_congruence_subgroup (Gamma N) :=
⟨N, by {simp only [le_refl]}⟩

lemma Gamma1_is_congruence (N : ℕ+) : is_congruence_subgroup (Gamma1 N) :=
begin
  refine ⟨N, _⟩,
  intros A hA,
  simp only [Gamma1_mem, Gamma_mem] at *,
  simp only [hA, eq_self_iff_true, and_self],
end

lemma Gamma0_is_congruence (N : ℕ+) : is_congruence_subgroup (Gamma0 N) :=
is_congruence_subgroup_trans _ _ (Gamma1_in_Gamma0 N) (Gamma1_is_congruence N)

end congruence_subgroup

section conjugation

open_locale pointwise

lemma Gamma_cong_eq_self (N : ℕ) (g : conj_act SL(2, ℤ)) : g • (Gamma N) = Gamma N :=
begin
  apply subgroup.normal.conj_act (Gamma_normal N),
end

lemma conj_cong_is_cong (g : conj_act SL(2, ℤ)) (Γ : subgroup SL(2, ℤ))
  (h : is_congruence_subgroup Γ) : is_congruence_subgroup (g • Γ) :=
begin
  obtain ⟨N, HN⟩ := h,
  refine ⟨N, _⟩,
  rw [←Gamma_cong_eq_self N g, subgroup.pointwise_smul_le_pointwise_smul_iff],
  exact HN,
end

end conjugation
