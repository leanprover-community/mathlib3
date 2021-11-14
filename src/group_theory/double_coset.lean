/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import data.setoid.basic
import group_theory.subgroup.basic
import group_theory.coset
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

/--Relation defining a double coset-/
def double_coset_rel (H K : subgroup G) : G → G → Prop :=
λ x y, (∃ (a ∈ H) (b ∈ K), y = a * x * b)

lemma rel_iff (H K : subgroup G) (x y : G) :
  double_coset_rel H K x y ↔ (∃ (a ∈ H) (b ∈ K), y = a * x * b) := iff.rfl

lemma left_bot_eq_left_group_rel (H : subgroup G) :
  (double_coset_rel ⊥ H) = (quotient_group.left_rel H).rel :=
begin
  show (double_coset_rel ⊥ H) = (quotient_group.left_rel H).r,
  ext,
  simp only [exists_prop, one_mul, subgroup.mem_bot, exists_eq_left, rel_iff],
  split,
  rintro ⟨a, ha⟩,
  rw [quotient_group.left_rel, ha.2],
  simp only [ha.left, inv_mul_cancel_left],
  rw quotient_group.left_rel,
  dsimp only,
  intro h,
  use (⟨x⁻¹ * x_1, h⟩ : H),
  simp only [h, mul_inv_cancel_left, eq_self_iff_true, and_self, subgroup.coe_mk],
end


lemma right_bot_eq_right_group_rel (H : subgroup G) :
  (double_coset_rel H ⊥) = (quotient_group.right_rel H).rel :=
begin
  show (double_coset_rel H ⊥) = (quotient_group.right_rel H).r,
  ext,
  simp only [exists_prop, one_mul, subgroup.mem_bot, exists_eq_left, rel_iff],
  split,
  rintro ⟨a, ha⟩,
  rw [quotient_group.right_rel, ha.2],
  simp only [ha.left, mul_one, mul_inv_cancel_right],
  rw quotient_group.right_rel,
  dsimp only,
  intro h,
  use (⟨x_1 * x⁻¹, h⟩ : H),
  simp only [h, mul_one, eq_self_iff_true, and_self, subgroup.coe_mk, inv_mul_cancel_right],
end

lemma rel_reflex {H K : subgroup G} : reflexive (double_coset_rel H K) :=
begin
  rw double_coset_rel,
  simp only [exists_prop],
  intro x,
  use 1,
  simp only [H.one_mem, K.one_mem, one_mul, exists_eq_right, self_eq_mul_right, and_self],
end

lemma rel_symm {H K : subgroup G} : symmetric (double_coset_rel H K) :=
begin
  rw double_coset_rel,
  intros x y,
  simp only [and_imp, exists_prop, forall_exists_index],
  intros a ha b hb hx,
  use a⁻¹,
  have haa := subgroup.inv_mem H ha,
  simp only [haa, true_and],
  use b⁻¹,
  have hbb := subgroup.inv_mem K hb,
  simp only [hbb, true_and],
  rw hx,
  simp_rw ← mul_assoc,
  simp only [one_mul, mul_left_inv, mul_inv_cancel_right],
end

lemma rel_trans {H K : subgroup G} : transitive (double_coset_rel H K) :=
begin
  rw double_coset_rel,
  intros x y z,
  simp only [and_imp, exists_prop, forall_exists_index],
  intros a ha b hb hxy c hc d hd hyz,
  use c * a,
  have hac := H.mul_mem hc ha,
  simp only [hac, true_and],
  use b*d,
  have hdb := (K.mul_mem hb hd),
  simp only [hdb, true_and, hyz, hxy, ← mul_assoc],
end

lemma rel_is_equiv {H K : subgroup G} : equivalence (double_coset_rel H K) :=
⟨rel_reflex, rel_symm, rel_trans⟩

/--The setoid defined by the double_coset relation-/
def setoid (H K : subgroup G) : setoid G :=
⟨double_coset_rel H K, rel_is_equiv⟩

/--Quotient of `G` by the double coset relation, i.e. `H \ G / K`-/
def quotient (H K : subgroup G) : Type* := quotient (setoid H K)

/--The double_coset as an element of `set α` corresponding to `s a t` -/
def doset (s t : set α) (a : α) : set α := { b : α | ∃ x : (s × t), b = x.1 * a * x.2 }

@[simp]
lemma doset_mem (s t : set α) (a b : α) :
  b ∈ (doset s t a) ↔ ∃ x : (s × t), b = x.1 * a * x.2 :=iff.rfl

lemma sub_doset (H K : subgroup G) (a b : G) (hb : b ∈ doset H.1 K a) :
  (doset H.1 K b) ⊆ (doset H K a) :=
begin
  intro x,
  simp only [and_imp, exists_prop, forall_exists_index, set_coe.exists, subgroup.mem_carrier,
  set_like.mem_coe, doset_mem,
  subgroup.coe_mk] at *,
  intros g hg,
  cases hb,
  rw hb_h at hg,
  use ⟨g.1 * hb_w.1, hb_w.2 * g.2⟩,
  simp [hg],
  simp_rw ← mul_assoc,
end

lemma disjoint_sub (H K : subgroup G) (a b : G) (h : ¬ disjoint (doset H.1 K a ) (doset H K b)) :
  b ∈ doset H.1 K a :=
begin
  rw set.not_disjoint_iff at h,
  simp only [exists_prop, set_coe.exists, doset_mem, subgroup.mem_carrier, set_like.mem_coe,
    subgroup.coe_mk] at *,
  rcases h with ⟨x, ⟨hx, hxx⟩, hk, hhk⟩ ,
  use ( ⟨hk.1⁻¹ * hx.1, hx.2 * hk.2⁻¹⟩ : H × K),
  rw hxx at hhk,
  simp only [subgroup.coe_inv, subgroup.coe_mul, ← mul_assoc],
  rw ← mul_inv_eq_iff_eq_mul,
  simp only [inv_inv],
  rw [mul_assoc, mul_assoc ] at *,
  simp only [hhk,inv_mul_cancel_left],
end

lemma disjoint_doset (H K : subgroup G) (a b : G) (h: ¬ disjoint (doset H.1 K a) (doset H K b)) :
  doset H.1 K a = doset H K b :=
begin
  have hb : b ∈ (doset H.1 K a), by {apply disjoint_sub _ _ _ _ h},
  rw disjoint.comm at h,
  have ha : a ∈ (doset H.1 K b), by {apply disjoint_sub _ _ _ _ h},
  rw set.subset.antisymm_iff,
  split,
  apply sub_doset H K b a ha,
  apply sub_doset H K a b hb,
end

/--Create a doset out of an element of `H \ G / K`-/
def quot_to_doset (H K : subgroup G) (q : quotient H K ) : set G := (doset H.1 K q.out')

/--Map from `G` to `H \ G / K`-/
abbreviation mk (H K : subgroup G) (a : G) : quotient H K :=
quotient.mk' a

instance (H K : subgroup G) : inhabited (quotient H K) := ⟨(mk H K (1 : G) : quotient H K)⟩

lemma eq (H K : subgroup G) (a b : G): mk H K a = mk H K b ↔ ∃ (h ∈ H) (k ∈ K), b = h * a * k :=
by { rw quotient.eq', apply (rel_iff H K a b), }

lemma out_eq' (H K : subgroup G) (q : quotient H K) : mk H K q.out' = q :=
quotient.out_eq' q

lemma mk_out'_eq_mul (H K : subgroup G) (g : G) :
  ∃ (h k : G), (h ∈ H) ∧ (k ∈ K) ∧ (mk H K g : quotient H K).out' = h * g * k :=
begin
  have := eq H K (mk H K g : quotient H K).out' g,
  rw out_eq' at this,
  simp only [exists_prop] at this,
  have h: mk H K g = mk H K g, by {refl,},
  have hh := this.1 h,
  let l := classical.some_spec hh,
  let le := classical.some hh,
  have hr := l.2,
  let r := classical.some_spec hr,
  let re := classical.some hr,
  use le⁻¹,
  use re⁻¹,
  simp only [H.inv_mem l.left, K.inv_mem r.left, true_and],
  have fl := r.2,
  simp_rw ← le at fl,
  simp_rw ← re at fl,
  rw fl,
  simp_rw ← mul_assoc,
  simp only [one_mul, mul_left_inv, mul_inv_cancel_right],
  exact congr_arg quotient.out' (congr_arg (mk H K) (eq.symm fl)),
end

lemma doset_eq_quot_eq (H K : subgroup G) (a b : G) (h : doset H.1 K a = doset H K b ) :
  mk H K a = mk H K b :=
begin
  rw eq,
  have : b ∈ doset H.1 K a,
  { rw h,
    simp only [exists_prop, set_coe.exists, doset_mem, set_like.mem_coe, subgroup.coe_mk,
    prod.exists],
    use 1,
    simp only [H.one_mem, K.one_mem, one_mul, exists_eq_right, self_eq_mul_right, and_self]},
  simp only [doset, exists_prop, set_coe.exists, subgroup.mem_carrier, set_like.mem_coe,
  set.mem_set_of_eq, subgroup.coe_mk, prod.exists] at *,
  apply this,
end

lemma disjoint_doset' (H K : subgroup G) (a b : quotient H K) :
  a ≠ b → disjoint (doset H.1 K a.out') (doset H K b.out') :=
begin
  simp only [ne.def],
  contrapose,
  simp only [not_not],
  intro h,
  have := disjoint_doset H K _ _ h,
  have h2:= doset_eq_quot_eq _ _ _ _ this,
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
  use ⟨⟨h⁻¹, H.inv_mem h3⟩, ⟨ k⁻¹ , K.inv_mem h4⟩ ⟩,
  simp only [h5, subgroup.coe_mk],
  simp_rw ← mul_assoc,
  simp only [one_mul, mul_left_inv, mul_inv_cancel_right],
end

lemma doset_union_right_coset (H K : subgroup G) (a : G) :
  (doset H.1 K a) = ⋃ (k : K), (right_coset H (a * k)) :=
begin
  ext,
  simp only [mem_right_coset_iff, exists_prop, mul_inv_rev, set.mem_Union, doset_mem,
    subgroup.mem_carrier, set_like.mem_coe],
  split,
  rintros ⟨x, h_h⟩,
  use x.2,
  rw h_h,
  simp_rw ← mul_assoc,
  simp only [set_like.coe_mem, mul_inv_cancel_right],
  intro h,
  cases h with y,
  use ⟨⟨x * (y⁻¹ * a⁻¹), h_h⟩, y⟩,
  simp_rw ← mul_assoc,
  simp only [subgroup.coe_mk, inv_mul_cancel_right],
end

lemma doset_union_left_coset (H K : subgroup G) (a : G) :
  (doset H.1 K a) = ⋃ (h : H), (left_coset (h * a) K) :=
begin
  ext,
  simp only [mem_left_coset_iff, exists_prop, mul_inv_rev, set.mem_Union, doset_mem,
  subgroup.mem_carrier, set_like.mem_coe],
  split,
  intro h,
  cases h with x,
  use x.1,
  rw h_h,
  simp_rw ← mul_assoc,
  simp only [set_like.coe_mem, one_mul, mul_left_inv, inv_mul_cancel_right],
  intro h,
  cases h with y,
  use ⟨ y, ⟨a⁻¹ * y⁻¹ * x, h_h ⟩⟩,
  simp only [subgroup.coe_mk],
  simp_rw ← mul_assoc,
  simp only [one_mul, mul_right_inv, mul_inv_cancel_right],
end

lemma left_bot_eq_left_quot (H : subgroup G) :
  quotient (⊥ : subgroup G) H = quotient_group.quotient H :=
begin
  rw quotient_group.quotient,
  simp_rw [quotient],
  apply congr_arg,
  have hab := left_bot_eq_left_group_rel H,
  ext,
  simp_rw ← hab,
  refl,
end

lemma right_bot_eq_right_quot (H : subgroup G) :
  quotient H (⊥ : subgroup G) = _root_.quotient (quotient_group.right_rel H) :=
begin
  simp_rw [quotient],
  apply congr_arg,
  have hab := right_bot_eq_right_group_rel H,
  ext,
  simp_rw ← hab,
  refl,
end

end double_coset
