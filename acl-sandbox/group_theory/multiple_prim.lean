/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic.lift

import field_theory.galois

import group_theory.group_action.embedding

import .wielandt
import .ad_to_ulift

import .multiply_trans

-- import .ad_sub_mul_actions

-- import group_theory.specific_groups.alternating

-- import set_theory.cardinal


-- import group_theory.subgroup.pointwise
-- import group_theory.coset
-- import group_theory.quotient_group
-- import group_theory.abelianization
-- import group_theory.group_action.defs
-- import group_theory.group_action.basic
-- import group_theory.group_action.group
-- import group_theory.group_action.conj_act
-- import group_theory.group_action.sub_mul_action

-- import order.partition.finpartition
-- import data.finset.lattice

-- import data.setoid.partition
-- import data.set.basic
-- import data.fintype.basic
-- import order.rel_classes
-- import algebra.big_operators.order

open_locale big_operators pointwise cardinal

open_locale classical


section MultiplePrimitivity

namespace mul_action

variables (M α : Type*) [group M] [mul_action M α]

def is_multiply_preprimitive (n : ℕ) :=
  is_multiply_pretransitive M α n ∧
  (∀ (s : set α) (hs : #s = ↑(n - 1)),
    is_preprimitive (fixing_subgroup M s)
      (sub_mul_action_of_fixing_subgroup M α s))

lemma is_multiply_preprimitive_zero :
  is_multiply_preprimitive M α 0 :=
begin
    sorry
end

example : ∀ (n : ℕ), n = 0 ∨ n ≥ 1 :=
begin
  intro n,
  cases nat.lt_or_ge n 1 with h h,
  apply or.intro_left _ (nat.lt_one_iff.mp h),
  apply or.intro_right _ h,
end

lemma is_multiply_preprimitive_one_iff :
  is_multiply_preprimitive M α 1 ↔ is_preprimitive M α := sorry

lemma is_multiply_preprimitive_mk {n : ℕ} (h : is_pretransitive M α) :
  is_multiply_preprimitive M α n.succ ↔
  ∀ (a : α), is_multiply_preprimitive (stabilizer M a) (sub_mul_action_of_stabilizer M α a) n :=
begin
  split,
  { intros hn a,
    cases nat.lt_or_ge n 1 with h0 h1,
    { rw nat.lt_one_iff at h0, rw h0, apply is_multiply_preprimitive_zero, },
    split,
    exact (stabilizer.is_multiply_pretransitive M α h a).mp  hn.left,
    intros s hs,
    apply is_preprimitive.mk,
    { apply is_pretransitive.mk,
      intros x y,

      have ha : a ∉ coe '' s,
      { intro ha,
        rw set.mem_image at ha,
        obtain ⟨x, hx⟩ := ha,
        apply sub_mul_action_of_stabilizer_neq M α a x,
        exact hx.right },
      let t := insert a (coe '' s),
      have ht : #t = ↑(n.succ - 1),
      { rw [cardinal.mk_insert ha, cardinal.mk_image_eq subtype.coe_injective, hs],
        conv_rhs { rw  ← (nat.sub_add_cancel h1) },
        exact rfl },

      let z := (hn.right t ht).exists_smul_eq,
      let hxs := sub_mul_action_of_fixing_subgroup_not_mem x,
      have hxt : ↑x ∈ (sub_mul_action_of_fixing_subgroup M α t).carrier,
      { refine set.mem_compl _,
        simp only [coe_coe, set.mem_insert_iff, set.mem_image,
          set_like.coe_eq_coe, exists_eq_right],
        apply not_or,
        { intro h,

          sorry },
        exact sub_mul_action_of_fixing_subgroup_not_mem x },
    sorry },
    sorry },
  sorry
end


lemma is_multiply_preprimitive_of_higher {n : ℕ}
  {m : ℕ} (hmn : m ≤ n) (hα : ↑n ≤ #α)
  (hn : is_multiply_preprimitive M α n) :
  is_multiply_preprimitive M α m :=
begin
  apply and.intro (is_multiply_pretransitive_of_higher M α hn.left hmn hα),
  intros s hs,

--  is_preprimitive (mul_action.stabilizer M a) (sub_mul_action_of_stabilizer M α a)

  sorry
end

/-- The fixator of a subset of cardinal d in a k-primitive action
acts (k-d) primitively on the remaining -/
lemma remaining_primitivity (d : ℕ) (s : set α) (hs : ↑d = #s)
  (n : ℕ)
  (h : is_multiply_preprimitive M α n) :
  is_multiply_preprimitive (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M α s) (n-d) :=
sorry

theorem stabilizer.is_multiply_preprimitive'
  (hα' : is_preprimitive M α)
  {n : ℕ} (a : α) :
  -- (hα0 : ↑n ≤ #α) /- (hα : card_ge α n.succ) -/  :
  is_multiply_preprimitive M α n.succ ↔
  is_multiply_preprimitive (stabilizer M a) (sub_mul_action_of_stabilizer M α a) n :=
begin
  split,
  { intros h,
    split,
    rw ← stabilizer.is_multiply_pretransitive M α hα'.to_is_pretransitive,
    exact h.left,
    intros s hs,



   sorry, },
  sorry,

end

lemma is_multiply_preprimitive_of_higher'  {n : ℕ}
  (hn : is_multiply_preprimitive M α n) {m : ℕ} (hmn : m ≤ n)
  (hα : ↑n ≤ #α) :
  is_multiply_preprimitive M α m := sorry

lemma is_preprimitive_iff_is_one_preprimitive' :
  is_preprimitive M α ↔ is_multiply_preprimitive M α 1 :=

-- theorem is_multiply_preprimitive_of_fixator {n d : ℕ} {s : finset α} (hs : fintype.card s = d)
--  (hα : is_multiply_preprimitive M α n) : is_multiply_preprimitive  M (s : set α)) (n-d)

#exit

 /- -- Now useless
    { obtain ⟨l', hl', hl'n, hl'e⟩ := list.extend_nodup n.succ hn.left [a] (list.nodup_singleton a) _,
      rw list.length_singleton at hl'e,
      swap,
      { simp only [list.length_singleton], exact nat.succ_le_succ (zero_le n) },
      unfold card_ge,
      lift l'.drop 1 to list ↥(sub_mul_action_of_stabilizer M α a) with l hl_coe,
      swap,
      { intros x hx,
        change x ∈ (sub_mul_action_of_stabilizer M α a).carrier,
        rw sub_mul_action_of_stabilizer_def,
        simp only [set.mem_compl_eq, set.mem_singleton_iff],
        suffices : a ∉ list.drop 1 l',
        { intro h, apply this, rw ← h, exact hx, },
        rw ← list.singleton_disjoint,
        apply list.disjoint_of_nodup_append,
        rw [← hl'e,  list.take_append_drop],
        exact hl'n },
      use l,
      split,
      { rw [← list.length_map, hl_coe, list.length_drop, hl',
          ← nat.pred_eq_sub_one, nat.pred_succ] },
      { rw ← list.nodup_map_iff (subtype.coe_injective),
        rw hl_coe,
        rw ← list.take_append_drop 1 l' at hl'n,
        exact (list.nodup_append.mp hl'n).2.1 } },
-/



example {α : Type*} (s : finset α) (x : ↥s) : ↑x ∈ s :=
finset.coe_mem x

example {α : Type*} (l : list α) (x : ↥l.to_finset) : ↑x ∈ l :=
list.mem_to_finset.mp (finset.coe_mem x)



example {α : Type*} (n : ℕ) (l : list α) :
  (list.take n l).length = min n l.length :=
begin
refine list.length_take n l,
end


example {α : Type*} (s : set α) (x y : list ↥s) :
   x = y ↔ (list.map coe x : list α) = (list.map coe y) :=
begin
  split,
  intro h, rw h,
  intro h, exact  (list.map_injective_iff.mpr (subtype.coe_injective)) h,
end



example : ∀ {α β γ δ : Type*} (f : α ↪ β) (g : γ ↪ δ) (x : α ↪ γ) (y : β ↪ δ)
  (h : f.trans y = x.trans g),
  ∀ (a : α), g (x a) = y (f a) :=
begin
  intros α β γ δ f g x y h a,
  simp only [← trans_apply],
  rw h,
end



section test

open nat

variables (n : ℕ) (α : Type*) (s : set α) (x : fin n.succ ↪ ↥s)
#check function.embedding.trans x (function.embedding.subtype s)
#check (fin.cast_le (n.le_succ)).to_embedding.trans  x
#check (fin.cast_le (nat.lt_succ_self n)).to_embedding

example : n ≤ n.succ := nat.le_succ n
def subype_compl (a : α) : set α := {a}ᶜ

#check function.embedding.subtype s


#check set.image
#check set.image_injective

lemma argh1 : ∀ (n : ℕ) (α : Type*) (x : fin n ↪ α) (s : set α) (h : ∀ (i : fin n), x i ∈ s),
  ∃ (x' : fin n ↪ (subtype s)),
  x'.trans (subtype s) = x :=
begin
  intros n α x a h,
  use λ i, ⟨x i, h i⟩,
  intros i j hij,
  simpa only [embedding_like.apply_eq_iff_eq] using hij,
  ext i,
  dsimp only [embedding_like.apply_eq_iff_eq], refl,
end


  /-
  function.embedding.trans (fin.cast_le (nat.lt_succ_self n)).to_embedding  x
  = function.embedding.trans x' (subtype (({a} : set α)ᶜ)) :=
  sorry
-/


lemma argh : ∀ (n : ℕ) (α : Type*) (x : fin n.succ ↪ α) (a : α)
  (h : ∀ i, x i ≠ a),
  ∃ (x' : fin n ↪ ↥({a} : set α)ᶜ),
  (fin.cast_le (nat.le_succ n)).to_embedding.trans  x
  = x'.trans (function.embedding.subtype ({a} : set α)ᶜ) :=

  sorry





end test



example : ∀ (α : Type*), (card_ge α 2) ↔ nontrivial α :=
begin
  intro α,
  split,
  { rintro ⟨x, hxl, hxn⟩,
    apply nontrivial.mk,
    let a := list.nth_le x 0 _ , let b := list.nth_le x 1 _,
    use a, use b, intro hab,
    rw list.nodup_iff_nth_le_inj at hxn,
    have : ¬(0 = 1), exact zero_ne_one, apply this,
    apply hxn 0 1 _ _ _,
    any_goals { rw hxl, norm_num },
    exact hab },
  { rintro ⟨a, b, hab⟩,
    unfold card_ge, use ([a, b]),
    simp [hab] }
end



example (α β : Type*) (s : set β) (f : α ↪ ↥s) : α ↪ β := f.trans (subtype _)
