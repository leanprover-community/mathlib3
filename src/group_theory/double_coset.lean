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

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines double cosets for two subgroups `H K` of a group `G` and the quotient of `G` by
the double coset relation, i.e. `H \ G / K`. We also prove that `G` can be writen as a disjoint
union of the double cosets and that if one of `H` or `K` is the trivial group (i.e. `⊥` ) then
this is the usual left or right quotient of a group by a subgroup.

## Main definitions

* `rel`: The double coset relation defined by two subgroups `H K` of `G`.
* `double_coset.quotient`: The quotient of `G` by the double coset relation, i.e, ``H \ G / K`.
-/


variables {G : Type*} [group G] {α : Type*} [has_mul α] (J: subgroup G) (g : G)

namespace doset

open_locale pointwise

/--The double_coset as an element of `set α` corresponding to `s a t` -/
def _root_.doset (a : α) (s t : set α) : set α := s * {a} * t

lemma mem_doset {s t : set α} {a b : α} : b ∈ doset a s t ↔ ∃ (x ∈ s) (y ∈ t), b = x * a * y :=
⟨λ ⟨_, y, ⟨x, _, hx, rfl, rfl⟩, hy, h⟩, ⟨x, hx, y, hy, h.symm⟩,
  λ ⟨x, hx, y, hy, h⟩, ⟨x * a, y, ⟨x, a, hx, rfl, rfl⟩, hy, h.symm⟩⟩

lemma mem_doset_self (H K : subgroup G) (a : G) : a ∈ doset a H K :=
mem_doset.mpr ⟨1, H.one_mem, 1, K.one_mem, (one_mul a).symm.trans (mul_one (1 * a)).symm⟩

lemma doset_eq_of_mem {H K : subgroup G} {a b : G} (hb : b ∈ doset a H K) :
  doset b H K = doset a H K :=
begin
  obtain ⟨_, k, ⟨h, a, hh, (rfl : _ = _), rfl⟩, hk, rfl⟩ := hb,
  rw [doset, doset, ←set.singleton_mul_singleton, ←set.singleton_mul_singleton, mul_assoc,
    mul_assoc, subgroup.singleton_mul_subgroup hk, ←mul_assoc, ←mul_assoc,
    subgroup.subgroup_mul_singleton hh],
end

lemma mem_doset_of_not_disjoint {H K : subgroup G} {a b : G}
  (h : ¬ disjoint (doset a H K) (doset b H K)) : b ∈ doset a H K :=
begin
  rw set.not_disjoint_iff at h,
  simp only [mem_doset] at *,
  obtain ⟨x, ⟨l, hl, r, hr, hrx⟩, y, hy, ⟨r', hr', rfl⟩⟩ := h,
  refine ⟨y⁻¹ * l, H.mul_mem (H.inv_mem hy) (hl), r * r'⁻¹, K.mul_mem hr (K.inv_mem hr'), _⟩,
  rwa [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, ←mul_assoc, ←mul_assoc, eq_mul_inv_iff_mul_eq],
end

lemma eq_of_not_disjoint {H K : subgroup G} {a b : G} (h: ¬ disjoint (doset a H K) (doset b H K)) :
  doset a H K = doset b H K :=
begin
  rw disjoint.comm at h,
  have ha : a ∈ doset b H K := mem_doset_of_not_disjoint h,
  apply doset_eq_of_mem ha,
end

/-- The setoid defined by the double_coset relation -/
def setoid (H K : set G) : setoid G :=
setoid.ker (λ x, doset x H K)

/-- Quotient of `G` by the double coset relation, i.e. `H \ G / K` -/
def quotient (H K : set G) : Type* :=
quotient (setoid H K)

lemma rel_iff {H K : subgroup G} {x y : G} :
  (setoid ↑H ↑K).rel x y ↔ ∃ (a ∈ H) (b ∈ K), y = a * x * b :=
iff.trans ⟨λ hxy, (congr_arg _ hxy).mpr (mem_doset_self H K y),
  λ hxy, (doset_eq_of_mem hxy).symm⟩ mem_doset

lemma bot_rel_eq_left_rel (H : subgroup G) :
  (setoid ↑(⊥ : subgroup G) ↑H).rel = (quotient_group.left_rel H).rel :=
begin
  ext a b,
  rw [rel_iff, setoid.rel, quotient_group.left_rel_apply],
  split,
  { rintros ⟨a, (rfl : a = 1), b, hb, rfl⟩,
    change a⁻¹ * (1 * a * b) ∈ H,
    rwa [one_mul, inv_mul_cancel_left] },
  { rintro (h : a⁻¹ * b ∈ H),
    exact ⟨1, rfl, a⁻¹ * b, h, by rw [one_mul, mul_inv_cancel_left]⟩ },
end

lemma rel_bot_eq_right_group_rel (H : subgroup G) :
  (setoid ↑H ↑(⊥ : subgroup G)).rel = (quotient_group.right_rel H).rel :=
begin
  ext a b,
  rw [rel_iff, setoid.rel, quotient_group.right_rel_apply],
  split,
  { rintros ⟨b, hb, a, (rfl : a = 1), rfl⟩,
    change b * a * 1 * a⁻¹ ∈ H,
    rwa [mul_one, mul_inv_cancel_right] },
  { rintro (h : b * a⁻¹ ∈ H),
    exact ⟨b * a⁻¹, h, 1, rfl, by rw [mul_one, inv_mul_cancel_right]⟩ },
end

/--Create a doset out of an element of `H \ G / K`-/
def quot_to_doset (H K : subgroup G) (q : quotient ↑H ↑K) : set G := (doset q.out' H K)

/--Map from `G` to `H \ G / K`-/
abbreviation mk (H K : subgroup G) (a : G) : quotient ↑H ↑K :=
quotient.mk' a

instance (H K : subgroup G) : inhabited (quotient ↑H ↑K) := ⟨mk H K (1 : G)⟩

lemma eq (H K : subgroup G) (a b : G) : mk H K a = mk H K b ↔ ∃ (h ∈ H) (k ∈ K), b = h * a * k :=
by { rw quotient.eq', apply rel_iff, }

lemma out_eq' (H K : subgroup G) (q : quotient ↑H ↑K) : mk H K q.out' = q :=
quotient.out_eq' q

lemma mk_out'_eq_mul (H K : subgroup G) (g : G) :
  ∃ (h k : G), (h ∈ H) ∧ (k ∈ K) ∧ (mk H K g : quotient ↑H ↑K).out' = h * g * k :=
begin
have := eq H K (mk H K g : quotient ↑H ↑K).out' g,
  rw out_eq' at this,
  obtain ⟨h, h_h, k, hk, T⟩ := this.1 rfl,
  refine ⟨h⁻¹, k⁻¹, (H.inv_mem h_h), K.inv_mem hk, eq_mul_inv_of_mul_eq (eq_inv_mul_of_mul_eq _)⟩,
  rw [← mul_assoc, ← T]
end

lemma mk_eq_of_doset_eq {H K : subgroup G} {a b : G} (h : doset a H K = doset b H K) :
  mk H K a = mk H K b :=
begin
  rw eq,
  exact mem_doset.mp (h.symm ▸ mem_doset_self H K b)
end

lemma disjoint_out' {H K : subgroup G} {a b : quotient H.1 K} :
  a ≠ b → disjoint (doset a.out' H K) (doset b.out' H K) :=
begin
  contrapose!,
  intro h,
  simpa [out_eq'] using mk_eq_of_doset_eq (eq_of_not_disjoint  h),
end

lemma union_quot_to_doset (H K : subgroup G) : (⋃ q, quot_to_doset H K q) = set.univ :=
begin
  ext x,
  simp only [set.mem_Union, quot_to_doset, mem_doset, set_like.mem_coe, exists_prop,
    set.mem_univ, iff_true],
  use mk H K x,
  obtain ⟨h, k, h3, h4, h5⟩ := mk_out'_eq_mul H K x,
  refine ⟨h⁻¹, H.inv_mem h3, k⁻¹, K.inv_mem h4, _⟩,
  simp only [h5, subgroup.coe_mk, ←mul_assoc, one_mul, mul_left_inv, mul_inv_cancel_right],
end

lemma doset_union_right_coset (H K : subgroup G) (a : G) :
  (⋃ (k : K), right_coset ↑H (a * k)) = doset a H K :=
begin
  ext x,
  simp only [mem_right_coset_iff, exists_prop, mul_inv_rev, set.mem_Union, mem_doset,
  subgroup.mem_carrier, set_like.mem_coe],
  split,
  {rintro ⟨y, h_h⟩,
    refine ⟨x * (y⁻¹ * a⁻¹), h_h, y, y.2, _⟩,
    simp only [← mul_assoc, subgroup.coe_mk, inv_mul_cancel_right]},
  {rintros ⟨x, hx, y, hy, hxy⟩,
    refine ⟨⟨y,hy⟩,_⟩,
    simp only [hxy, ←mul_assoc, hx, mul_inv_cancel_right, subgroup.coe_mk]},
end

lemma doset_union_left_coset (H K : subgroup G) (a : G) :
  (⋃ (h : H), left_coset (h * a : G) K) = doset a H K :=
begin
  ext x,
  simp only [mem_left_coset_iff, mul_inv_rev, set.mem_Union, mem_doset],
  split,
  { rintro ⟨y, h_h⟩,
    refine ⟨y, y.2, a⁻¹ * y⁻¹ * x, h_h, _⟩,
    simp only [←mul_assoc, one_mul, mul_right_inv, mul_inv_cancel_right]},
  { rintros ⟨x, hx, y, hy, hxy⟩,
    refine ⟨⟨x, hx⟩, _⟩,
    simp only [hxy, ←mul_assoc, hy, one_mul, mul_left_inv, subgroup.coe_mk, inv_mul_cancel_right]},
  end

lemma left_bot_eq_left_quot (H : subgroup G) :
  quotient (⊥ : subgroup G).1 H = (G ⧸ H) :=
begin
  unfold quotient,
  congr,
  ext,
  simp_rw ← bot_rel_eq_left_rel H,
  refl,
end

lemma right_bot_eq_right_quot (H : subgroup G) :
  quotient H.1 (⊥ : subgroup G) = _root_.quotient (quotient_group.right_rel H) :=
begin
  unfold quotient,
  congr,
  ext,
  simp_rw ← rel_bot_eq_right_group_rel H,
  refl,
end

end doset
