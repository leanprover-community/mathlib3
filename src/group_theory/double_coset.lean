/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import data.setoid.basic
import group_theory.subgroup.basic
import group_theory.coset
import group_theory.subgroup.pointwise
import data.set.basic
import tactic.group

/-!
# Double cosets

This file defines double cosets for two subgroups `H K` of a group `G` and the quotient of `G` by
the double coset relation, i.e. `H \ G / K`. We also prove that `G` can be writen as a disjoint
union of the double cosets and that if one of `H` or `K` is the trivial group (i.e. `⊥` ) then
this is the usual left or right quotient of a group by a subgroup.

## Main definitions

* `double_coset_rel`: The double coset relation defined by two subgroups `H K` of `G`.
* `double_coset.quotient`: The quotient of `G` by the double coset relation, i.e, ``H \ G / K`.
-/


variables {G : Type*} [group G] {α : Type*} [has_mul α] (J: subgroup G) (g : G)

namespace double_coset

open_locale pointwise

/--The double_coset as an element of `set α` corresponding to `s a t` -/
def doset (a : α) (s t : set α) : set α := s * {a} * t

@[simp]
lemma doset_mem {s t : set α} {a b : α} : b ∈ doset a s t ↔ ∃ (x ∈ s) (y ∈ t), b = x * a * y :=
⟨λ ⟨_, y, ⟨x, _, hx, rfl, rfl⟩, hy, h⟩, ⟨x, hx, y, hy, h.symm⟩,
  λ ⟨x, hx, y, hy, h⟩, ⟨x * a, y, ⟨x, a, hx, rfl, rfl⟩, hy, h.symm⟩⟩

def double_coset_rel (H K : set G) : G → G → Prop :=
λ x y, doset x H K = doset y H K

lemma rel_reflex {H K : set G} : reflexive (double_coset_rel H K) :=
λ x, rfl

lemma rel_symm {H K : set G} : symmetric (double_coset_rel H K) :=
λ x y, eq.symm

lemma rel_trans {H K : set G} : transitive (double_coset_rel H K) :=
λ x y z, eq.trans

lemma rel_is_equiv {H K : set G} : equivalence (double_coset_rel H K) :=
⟨rel_reflex, rel_symm, rel_trans⟩

/-- The setoid defined by the double_coset relation -/
def setoid (H K : set G) : setoid G :=
⟨double_coset_rel H K, rel_is_equiv⟩

/-- Quotient of `G` by the double coset relation, i.e. `H \ G / K` -/
def quotient (H K : set G) : Type* :=
quotient (setoid H K)

lemma doset_subgroups_mem_self (H K : subgroup G) (a : G) : a ∈ (doset a H K) :=
doset_mem.mpr ⟨1, H.one_mem, 1, K.one_mem, (one_mul a).symm.trans (mul_one (1 * a)).symm⟩

lemma sub_doset {H K : subgroup G} {a b : G} (hb : b ∈ doset a H K) :
  doset b H K = doset a H K :=
begin
  obtain ⟨_, k, ⟨h, a, hh, (rfl : _ = _), rfl⟩, hk, rfl⟩ := hb,
  rw [doset, doset, ←set.singleton_mul_singleton, ←set.singleton_mul_singleton, mul_assoc,
  mul_assoc, subgroup.singleton_mul_subgroup hk, ←mul_assoc, ←mul_assoc,
  subgroup.subgroup_mul_singleton hh],
end

lemma rel_iff {H K : subgroup G} {x y : G} :
  double_coset_rel ↑H ↑K x y ↔ ∃ (a ∈ H) (b ∈ K), y = a * x * b :=
iff.trans ⟨λ hxy, (congr_arg _ hxy).mpr (doset_subgroups_mem_self H K y),
  λ hxy, (sub_doset hxy).symm⟩ doset_mem

lemma left_bot_eq_left_group_rel (H : subgroup G) :
  (double_coset_rel ↑(⊥ : subgroup G) ↑H) = (quotient_group.left_rel H).rel :=
begin
 ext a b,
  rw rel_iff,
  split,
  { rintros ⟨a, (rfl : a = 1), b, hb, rfl⟩,
    change a⁻¹ * (1 * a * b) ∈ H,
    rwa [one_mul, inv_mul_cancel_left] },
  { rintro (h : a⁻¹ * b ∈ H),
    exact ⟨1, rfl, a⁻¹ * b, h, by rw [one_mul, mul_inv_cancel_left]⟩ },
end

lemma right_bot_eq_right_group_rel (H : subgroup G) :
  (double_coset_rel ↑H ↑(⊥ : subgroup G)) = (quotient_group.right_rel H).rel :=
begin
  ext a b,
  rw rel_iff,
  split,
  { rintros ⟨b, hb, a, (rfl : a = 1), rfl⟩,
    change b * a * 1 * a⁻¹ ∈ H,
    rwa [mul_one, mul_inv_cancel_right] },
  { rintro (h : b * a⁻¹ ∈ H),
    exact ⟨b * a⁻¹, h, 1, rfl, by rw [mul_one, inv_mul_cancel_right]⟩ },
end

lemma disjoint_sub (H K : subgroup G) (a b : G) (h : ¬ disjoint (doset a H K ) (doset b H K )) :
  b ∈ doset a H K :=
begin
  rw set.not_disjoint_iff at h,
  simp only [exists_prop, set_coe.exists, doset_mem, subgroup.mem_carrier, set_like.mem_coe,
  subgroup.coe_mk] at *,
  obtain  ⟨x, ⟨l, hl, r, hr, hrx⟩, y, hy, ⟨r', hr', rfl⟩⟩ := h,
  refine ⟨y⁻¹ * l, H.mul_mem (H.inv_mem hy) (hl), r * r'⁻¹, K.mul_mem hr (K.inv_mem hr'), _⟩,
  rwa [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, ←mul_assoc, ←mul_assoc, eq_mul_inv_iff_mul_eq],
end

lemma disjoint_doset (H K : subgroup G) (a b : G) (h: ¬ disjoint (doset a H K ) (doset b H K )) :
  doset a H K  = doset b H K :=
begin
  rw disjoint.comm at h,
  have ha : a ∈ (doset b H K), by {apply disjoint_sub _ _ _ _ h},
  apply sub_doset ha,
end

/--Create a doset out of an element of `H \ G / K`-/
def quot_to_doset (H K : subgroup G) (q : quotient ↑H ↑K ) : set G := (doset q.out' H K)

/--Map from `G` to `H \ G / K`-/
abbreviation mk (H K : subgroup G) (a : G) : quotient ↑H ↑K :=
quotient.mk' a

instance (H K : subgroup G) : inhabited (quotient ↑H ↑K) := ⟨(mk H K (1 : G) : quotient ↑H ↑K)⟩

lemma eq (H K : subgroup G) (a b : G): mk H K a = mk H K b ↔ ∃ (h ∈ H) (k ∈ K), b = h * a * k :=
by { rw quotient.eq', apply (rel_iff ), }

lemma out_eq' (H K : subgroup G) (q : quotient ↑H ↑K) : mk H K q.out' = q :=
quotient.out_eq' q

lemma mk_out'_eq_mul (H K : subgroup G) (g : G) :
  ∃ (h k : G), (h ∈ H) ∧ (k ∈ K) ∧ (mk H K g : quotient ↑H ↑K).out' = h * g * k :=
begin
  have := eq H K (mk H K g : quotient ↑H ↑K).out' g,
  rw out_eq' at this,
  simp only [exists_prop] at this,
  have h: mk H K g = mk H K g, by {refl,},
  have hh := this.1 h,
  obtain ⟨h,h_h,k,hk,T⟩ :=hh,
  refine ⟨h⁻¹ ,k⁻¹, (H.inv_mem h_h), K.inv_mem hk,_⟩,
  rw T,
  simp_rw ← mul_assoc,
  simp only [one_mul, mul_left_inv, mul_inv_cancel_right],
  exact congr_arg quotient.out' (congr_arg (mk H K) (eq.symm T)),
end

lemma doset_eq_quot_eq (H K : subgroup G) (a b : G) (h : doset a H K = doset b H K ) :
  mk H K a = mk H K b :=
begin
  rw eq,
  have : b ∈ doset a H K,
  { rw h,
    simp only [exists_prop, set_coe.exists, doset_mem, set_like.mem_coe, subgroup.coe_mk,
    prod.exists],
    use 1,
    simp only [H.one_mem, K.one_mem, one_mul, exists_eq_right, self_eq_mul_right, and_self]},
  rw doset_mem at this,
  simp only [exists_prop, set_coe.exists, set_like.mem_coe, subgroup.coe_mk, prod.exists] at *,
  apply this,
end

lemma disjoint_doset' (H K : subgroup G) (a b : quotient H.1 K) :
  a ≠ b → disjoint (doset a.out' H K) (doset b.out' H K) :=
begin
  simp only [ne.def],
  contrapose,
  simp only [not_not],
  intro h,
  have := disjoint_doset H K _ _ h,
  have h2 := doset_eq_quot_eq _ _ _ _ this,
  simp_rw [out_eq'] at h2,
  apply h2,
end

lemma top_eq_union_dosets (H K : subgroup G) : (⊤ : set G) = ⋃ q, quot_to_doset H K q :=
begin
  simp only [set.top_eq_univ],
  ext,
  simp only [set.mem_Union, true_iff, set.mem_univ],
  use mk H K x,
  rw quot_to_doset,
  simp only [exists_prop, doset_mem, subgroup.mem_carrier, set_like.mem_coe],
  have hy := mk_out'_eq_mul H K x,
  rcases hy with ⟨h, k, h3, h4, h5⟩,
  refine ⟨h⁻¹, H.inv_mem h3 ,k⁻¹, K.inv_mem h4,_⟩,
  simp only [h5, subgroup.coe_mk, ←mul_assoc, one_mul, mul_left_inv, mul_inv_cancel_right],
end

lemma doset_union_right_coset (H K : subgroup G) (a : G) :
  (doset a H K) = ⋃ (k : K), (right_coset H (a * k)) :=
begin
  ext,
  simp only [mem_right_coset_iff, exists_prop, mul_inv_rev, set.mem_Union, doset_mem,
    subgroup.mem_carrier, set_like.mem_coe],
  split,
  rintros ⟨x, hx, y, hy, hxy⟩,
  refine ⟨⟨y,hy⟩,_⟩,
  simp only [hxy, ←mul_assoc, hx, mul_inv_cancel_right, subgroup.coe_mk],
  intro h,
  cases h with y,
  refine ⟨x * (y⁻¹ * a⁻¹), h_h, y,y.2,_⟩,
  simp only [← mul_assoc, subgroup.coe_mk, inv_mul_cancel_right],
end

lemma doset_union_left_coset (H K : subgroup G) (a : G) :
  (doset a H K) = ⋃ (h : H), (left_coset (h * a) K) :=
begin
  ext,
  simp only [mem_left_coset_iff, exists_prop, mul_inv_rev, set.mem_Union, doset_mem,
  subgroup.mem_carrier, set_like.mem_coe],
  split,
  intro h,
  rcases h with ⟨l, hl, y, hy, hyr⟩,
  refine ⟨⟨l,hl⟩,_⟩,
  simp only [hyr, ←mul_assoc, hy, one_mul, mul_left_inv, subgroup.coe_mk, inv_mul_cancel_right],
  intro h,
  cases h with y,
  refine ⟨y, y.2, a⁻¹ * y⁻¹ * x, h_h, _⟩,
  simp only [←mul_assoc, one_mul, mul_right_inv, mul_inv_cancel_right],
end

lemma left_bot_eq_left_quot (H : subgroup G) :
  quotient (⊥ : subgroup G).1 H = (G ⧸ H) :=
begin
  simp_rw [quotient],
  apply congr_arg,
  have hab := left_bot_eq_left_group_rel H,
  ext,
  simp_rw ← hab,
  refl,
end

lemma right_bot_eq_right_quot (H : subgroup G) :
  quotient H.1 (⊥ : subgroup G) = _root_.quotient (quotient_group.right_rel H) :=
begin
  simp_rw [quotient],
  apply congr_arg,
  have hab := right_bot_eq_right_group_rel H,
  ext,
  simp_rw ← hab,
  refl,
end

end double_coset
