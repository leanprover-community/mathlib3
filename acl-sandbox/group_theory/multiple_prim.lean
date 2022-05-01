/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic.lift

-- import field_theory.galois

import group_theory.group_action.embedding


import .multiply_trans
-- import .mul_action_bihom
-- import .wielandt
-- import .ad_to_ulift
-- import .ad_sub_mul_actions

open_locale big_operators pointwise cardinal

open_locale classical

namespace mul_action

section mul_action_bihom

/- On veut étudier la situation suivante :

M and N are monoids,
there are actions of M on α and of N on β,
and I wish to consider pairs (φ : M →*N , f : α → β)
such that φ(m) • f(a) = f(m • a) for all m, a.

-/


variables (M α : Type*) [group M] [mul_action M α]
variables (N β : Type*) [group N] [mul_action N β]

variables {M α N β}
lemma preimage_is_block (f : mul_action_bihom M α N β)
  {B : set β} (hB : is_block N β B) :
  is_block M α (f.to_fun ⁻¹' B) :=
begin
  rw is_block.mk at hB ⊢,
  intro m,
  simp only [mul_of_preimage_eq],
  cases hB (f.to_monoid_hom m) with h h,
  { apply or.intro_left, rw h },
  { apply or.intro_right,
    apply set.disjoint_preimage h }
end

lemma is_preprimitive_of_bihom (f : mul_action_bihom M α N β) (hf : function.surjective f.to_fun):
  is_preprimitive M α → is_preprimitive N β :=
begin
  intro h, let h.htb := h.has_trivial_blocks,
  split,
  apply is_pretransitive_of_bihom f hf,
  exact h.to_is_pretransitive,
  intros B hB,
  rw ← (set.image_preimage_eq B hf),
  cases h.htb (preimage_is_block f hB) with hB' hB',
  { apply or.intro_left,
    simp only [set.subsingleton_coe] at hB' ⊢,
    apply set.subsingleton.image hB' },
  { apply or.intro_right, rw hB',
    simp only [set.top_eq_univ],
    rw set.image_univ, rw set.range_iff_surjective,
    assumption }
end

end mul_action_bihom

section MultiplePrimitivity

variables (M α : Type*) [group M] [mul_action M α]

def is_multiply_preprimitive (n : ℕ) :=
  is_multiply_pretransitive M α n ∧
  (∀ (s : set α) (hs : #s < ↑n),
    is_preprimitive (fixing_subgroup M s)
      (sub_mul_action_of_fixing_subgroup M s))

lemma is_multiply_preprimitive_zero :
  is_multiply_preprimitive M α 0 :=
begin
  split,
  apply is_zero_pretransitive,
  { intros s, apply not.elim, rw not_lt, apply zero_le }
end

example : ∀ (n : ℕ), n = 0 ∨ n ≥ 1 :=
begin
  intro n,
  cases nat.lt_or_ge n 1 with h h,
  apply or.intro_left _ (nat.lt_one_iff.mp h),
  apply or.intro_right _ h,
end

lemma is_multiply_preprimitive_one_iff :
  is_multiply_preprimitive M α 1 ↔ is_preprimitive M α :=
begin
  let j := sub_mul_action_of_fixing_subgroup_inclusion' M (∅ : set α),
  have hj : ∀ (a : α), a ∈ sub_mul_action_of_fixing_subgroup M (∅ : set α),
  { intro a, change a ∈ (sub_mul_action_of_fixing_subgroup M ∅).carrier,
      rw sub_mul_action_of_fixing_subgroup_def,
      simp only [set.compl_empty] },
  have hj' : ∀ (m : M), m ∈ fixing_subgroup M (∅ : set α),
  { intro m, rw mem_fixing_subgroup_iff, intros y hy,
      exfalso, simpa only using hy, },
  have hj'' : function.bijective  j.to_fun,
  { split,
    { intros a b h,
      rw ← set_like.coe_eq_coe,
      have ha : ↑a = j.to_fun a, refl,
      have hb : ↑b = j.to_fun b, refl,
      rw [ha, hb, h] },
    { intro a, use a,
      change a ∈ (sub_mul_action_of_fixing_subgroup M ∅).carrier,
      rw sub_mul_action_of_fixing_subgroup_def,
      simp only [set.compl_empty], refl } },
  let j' : mul_action_bihom M α (fixing_subgroup M ∅) (sub_mul_action_of_fixing_subgroup M ∅) :=
  { to_fun := λ a, ⟨a, hj a⟩ ,
    to_monoid_hom := {
      to_fun := λ m, ⟨m, hj' m⟩,
      map_one' := rfl,
      map_mul' := λ m n, by simp only [submonoid.mk_mul_mk, subtype.mk_eq_mk] },
    map_smul' := λ m a, begin  simp, refl, end,
    },
  split,
  { rintro ⟨h1, h1'⟩,
    refine is_preprimitive_of_bihom j _ _,
    apply function.bijective.surjective hj'',
    refine h1' _ _,
    simp },
  { intro h,
    split,
    rw ← is_pretransitive_iff_is_one_pretransitive,
    exact h.to_is_pretransitive,
    intros s hs,
    simp only [nat.cast_one] at hs,

    have : s = ∅,
    { rw [← cardinal.mk_emptyc_iff, ← nonpos_iff_eq_zero,
          ← cardinal.lt_succ, cardinal.succ_zero],
      exact hs },
    rw this,
    refine is_preprimitive_of_bihom j' _ h,
    { intro a, use ↑a , simp only [set_like.eta] } }
end

example : ∀ (c : cardinal) (n : ℕ) (h : c < n), c + 1 ≤ n :=
begin
  intros c n h,
  suffices : c < ω,
  { rw cardinal.lt_omega at this,
    obtain ⟨m, rfl⟩ := this,
    rw cardinal.nat_cast_lt  at h,
    refine le_trans (cardinal.add_one_le_succ _) _,
    rw ← cardinal.nat_succ,
    rw cardinal.nat_cast_le,
    exact nat.succ_le_iff.mpr h },
  refine lt_trans h (cardinal.nat_lt_omega n),
end

lemma test (n : ℕ) (h : 1 ≤ n) : 2 ≤ n.succ :=
begin
  exact nat.succ_le_succ h,
end


lemma is_multiply_preprimitive_mk {n : ℕ} (h : is_pretransitive M α) (hα : (n.succ : cardinal) ≤ #α):
  is_multiply_preprimitive M α n.succ ↔
  ∀ (a : α), is_multiply_preprimitive (stabilizer M a) (sub_mul_action_of_stabilizer M α a) n :=
begin
  split,
  { intros hn a,
    cases nat.lt_or_ge n 1 with h0 h1,
    { rw nat.lt_one_iff at h0, rw h0, apply is_multiply_preprimitive_zero, },

    split,
    -- n-pretransitve
    exact (stabilizer.is_multiply_pretransitive M α h a).mp  hn.left,
    -- multiple preprimitivity property
    intros s hs,

    let t : set α := set.insert a (coe '' s),

    have hst : (subgroup.map (subgroup.subtype _) (fixing_subgroup ↥(stabilizer M a) s) : subgroup M)
      = fixing_subgroup M t,
    { ext m,
      split,
      { rintro ⟨n, hn, rfl⟩,
        simp only [subgroup.coe_subtype, set_like.mem_coe, mem_fixing_subgroup_iff] at hn ⊢,
        intros y hy,
        cases set.mem_insert_iff.mp hy with hy hy,
          -- y = a
          rw hy, simpa using n.prop,
          -- y ∈ s
          simp only [set.mem_image] at hy,
          obtain ⟨y, hy1, rfl⟩ := hy,
          conv_rhs { rw ← hn y hy1 },
          refl },
      { intro hm,
        use m,
        { rw mem_stabilizer_iff,
          rw mem_fixing_subgroup_iff at hm,
          apply hm a (set.mem_insert a _) },
        { split,
          simp only [set_like.mem_coe , mem_fixing_subgroup_iff],
          intros y hy,
          rw mem_fixing_subgroup_iff at hm,
          suffices : ↑y ∈ t,
          { rw ← set_like.coe_eq_coe,
            conv_rhs { rw ← hm ↑y this},
            refl },
          apply set.mem_insert_of_mem,
          use ⟨y, hy, rfl⟩,
          refl } } },


    have hs' : s = coe ⁻¹' (coe '' s : set α) :=
    begin
      rw set.preimage_image_eq, exact subtype.coe_injective
    end,
    let j := sub_mul_action_of_fixing_subgroup_eq_bihom (stabilizer M a) hs'.symm,
    apply is_preprimitive_of_bihom j,
    { intro x, use x,
      { rw ← hs', exact x.prop },
      rw ← set_like.coe_eq_coe,
      simp_rw ← sub_mul_action_of_fixing_subgroup_eq_bihom_def (stabilizer M a) hs' x,
      refl },

    let j' := sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a (coe '' s : set α),
    apply is_preprimitive_of_bihom j',
    { intro x, use x,
      { simp,
        change _ ∈ (sub_mul_action_of_fixing_subgroup M _).carrier,
        rw sub_mul_action_of_fixing_subgroup_def,
        simp,
        sorry, },
      simp,
      rw ← set_like.coe_eq_coe,
      simp_rw ← sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_def M a (coe ⁻¹' (coe '' s)) x,


      sorry },

    apply hn.right,
    { sorry },
  },
  sorry,
end

/-
    have j' : mul_action_bihom
      ↥(fixing_subgroup M (set.insert a (coe '' s : set α)))
      (sub_mul_action_of_fixing_subgroup M (insert a (coe '' s : set α)))
      ↥(fixing_subgroup ↥(stabilizer M a) s)
      (sub_mul_action_of_fixing_subgroup ↥(stabilizer M a) s),
    sorry,

    apply is_preprimitive.mk,
    { apply is_pretransitive.mk,

      have extend_aux : ∀ (x : sub_mul_action_of_fixing_subgroup (stabilizer M a) s),
         ∃ (x' : fin 2 ↪ α), x' 0 = x ∧ x' 1 = a,
      { intro x, let x' : fin 1 ↪ α := {
        to_fun := λ i, x,
        inj' := begin
          apply function.injective_of_subsingleton _,
          exact unique.subsingleton,
        end, },
        obtain ⟨y',hy', hy''⟩ := may_extend_with x' a _,
        use y',
        apply and.intro _ hy'',
        { suffices : x' 0 = x,
          { rw ← this, rw ← hy', refl },
          refl },
        { intro h,
          simp only [coe_coe, set.range_const, set.mem_singleton_iff] at h,
          apply sub_mul_action_of_stabilizer_neq M α a x,
          exact h.symm } },

      intros x y,
      obtain ⟨x', hx'0, hx'1⟩ := extend_aux x,
      obtain ⟨y', hy'0, hy'1⟩ := extend_aux y,
      have hn' : is_multiply_pretransitive M α 2 :=
        is_multiply_pretransitive_of_higher M α hn.left
          (nat.succ_le_succ h1) hα,
      let hn'_eq := hn'.exists_smul_eq,
      obtain ⟨g, hgxy⟩ := hn'_eq x' y',
      have hg : g ∈ stabilizer M a,
      { sorry },
      use ⟨g, hg⟩,


      have ha : a ∉ coe '' s,
      { intro ha,
        rw set.mem_image at ha,
        obtain ⟨x, hx⟩ := ha,
        apply sub_mul_action_of_stabilizer_neq M α a x,
        exact hx.right },
      let t := insert a (coe '' s),
      have ht : #t ≤ n,
      { -- simp only [cardinal.nat_succ, cardinal.lt_succ],
        rw cardinal.mk_insert ha,
        rw cardinal.mk_image_eq_of_inj_on,
        { have : #s < ω := lt_trans hs (cardinal.nat_lt_omega n),
          rw cardinal.lt_omega at this,
          obtain ⟨m, hm⟩ := this,
          rw [hm, cardinal.nat_cast_lt]  at hs,
          refine le_trans (cardinal.add_one_le_succ _) _,
          rw [hm, ← cardinal.nat_succ, cardinal.nat_cast_le, nat.succ_le_iff],
          exact hs },
          apply set.inj_on_of_injective,
          exact subtype.coe_injective },

      sorry, },

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
-/

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
