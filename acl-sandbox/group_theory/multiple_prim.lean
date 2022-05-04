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

namespace cardinal

section cardinal

lemma lt_add_one_of_lt_omega (c : cardinal) (h : c < ω) : c < c + 1 :=
begin
  obtain ⟨n, rfl⟩ := cardinal.lt_omega.mp h,
  rw [← nat.cast_one, ← nat.cast_add, cardinal.nat_cast_lt],
  apply lt_add_one,
end

lemma add_one_le (c : cardinal) (n : ℕ) (h : c < n) : c + 1 ≤ n :=
begin
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

lemma add_cancel {c : cardinal} {m n : ℕ} (h : c + m = n + m) : c = n :=
begin
  suffices : c + m < ω,
  { rw cardinal.add_lt_omega_iff at this,
    obtain ⟨m, rfl⟩ := cardinal.lt_omega.mp this.left,
    simp only [← nat.cast_add, cardinal.nat_cast_inj] at h,
    apply congr_arg,
    apply nat.add_right_cancel h },
  rw [h, cardinal.add_lt_omega_iff],
  exact ⟨cardinal.nat_lt_omega n, cardinal.nat_lt_omega m⟩,
end

lemma lt_of_add_right_iff {c : cardinal} {m n : ℕ} :
 c + m < n + m ↔ c < n :=
begin
  split,
  { intro h,
    suffices : c + m < ω,
    { rw cardinal.add_lt_omega_iff at this,
      obtain ⟨m, rfl⟩ := cardinal.lt_omega.mp this.left,
      rw cardinal.nat_cast_lt,
      simpa only [← nat.cast_add, cardinal.nat_cast_lt,
        add_lt_add_iff_right] using h },
    apply lt_trans h,
    rw ← nat.cast_add, apply cardinal.nat_lt_omega },
  { intro h,
    obtain ⟨k, rfl⟩ := cardinal.lt_omega.mp (lt_trans h (cardinal.nat_lt_omega n)),
    simp only [← nat.cast_add, cardinal.nat_cast_lt],
    rw cardinal.nat_cast_lt at h,
    exact add_lt_add_right h m },
end

lemma cardinal_nat_add_one {m : ℕ} : (m : cardinal) + 1 = (m.succ) :=
begin
  rw [← nat.cast_one, ←  nat.cast_add],
end

end cardinal

end cardinal

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

/-- An action is n-fold preprimitive if it is n-fold pretransitive
and if the action of fixator of any (n-1) element subset on the remaining set
is not only pretransitive but also preprimitive. (Wielandt, §10)
-/
def is_multiply_preprimitive (n : ℕ) :=
  is_multiply_pretransitive M α n ∧
  (∀ (s : set α) (hs : #s + 1 = ↑n),
    is_preprimitive (fixing_subgroup M s)
      (sub_mul_action_of_fixing_subgroup M s))

/-- Any action is 0-fold preprimitive -/
lemma is_multiply_preprimitive_zero :
  is_multiply_preprimitive M α 0 :=
begin
  split,
  apply is_zero_pretransitive,
  { intros s, apply not.elim,
    simp only [nat.cast_zero, add_eq_zero_iff, one_ne_zero, and_false, not_false_iff],  }
end

/-- 1-fold preprimitivity is preprimitivity -/
lemma is_multiply_preprimitive_one_iff :
  is_multiply_preprimitive M α 1 ↔ is_preprimitive M α :=
begin
  split,
  { rintro ⟨h1, h1'⟩,
    apply is_preprimitive_of_bihom (sub_mul_action_of_fixing_subgroup_empty_bihom M α),
    apply function.bijective.surjective,
    apply sub_mul_action_of_fixing_subgroup_empty_bihom_bijective,
    apply h1',
    simp },
  { intro h,
    split,
    rw ← is_pretransitive_iff_is_one_pretransitive,
    exact h.to_is_pretransitive,
    intros s hs,
    suffices : s = ∅,
    rw this,
    refine is_preprimitive_of_bihom (sub_mul_action_of_fixing_subgroup_empty_bihom' M α) _ h,
    apply function.bijective.surjective,
    apply sub_mul_action_of_fixing_subgroup_empty_bihom'_bijective,

    rw [← nat.cast_one] at hs,
    rw [← cardinal.mk_emptyc_iff, ← nat.cast_zero],
    apply cardinal.add_cancel, rw hs,
    simp },
end

/-- A pretransitive  action is n.succ-fold preprimitive  iff
  the action of stabilizers is n-fold preprimitive -/
theorem is_multiply_preprimitive_of_stabilizer {n : ℕ} (hn : n ≥ 1) (h : is_pretransitive M α) : -- (hα : (n.succ : cardinal) ≤ #α):
  is_multiply_preprimitive M α n.succ ↔
  ∀ (a : α), is_multiply_preprimitive (stabilizer M a) (sub_mul_action_of_stabilizer M α a) n :=
begin
  split,
  { intros hn a,
    cases nat.lt_or_ge n 1 with h0 h1,
    { rw nat.lt_one_iff at h0, rw h0, apply is_multiply_preprimitive_zero, },

    split,
    -- n-pretransitive
    exact (stabilizer.is_multiply_pretransitive M α h).mp hn.left a,

    -- multiple preprimitivity property
    intros s hs,

--    let j := sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s,

    apply is_preprimitive_of_bihom _,
    exact (sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_bijective M a s).right,
    apply hn.right,

    suffices : # (set.insert a (coe '' s)) = # s + 1,
    rw [this, hs, ← nat.cast_one, ←  nat.cast_add],

    suffices : a ∉ coe '' s,
    let z : # ↥(set.insert a (coe '' s)) = _ := cardinal.mk_insert this,
    rw z,
    rw cardinal.mk_image_eq  subtype.coe_injective,

    rintro ⟨x, hx, hx'⟩,
    apply x.prop, simp only [set.mem_singleton_iff],
    exact hx' },
  { intro hn_0,
    split,
    { rw (stabilizer.is_multiply_pretransitive M α h),
      intro a, exact (hn_0 a).left },
    { intros s hs,
      rw [← nat.cast_one, nat.cast_add n 1] at hs,
      let hs := cardinal.add_cancel hs,
      have : ∃ (a : α), a ∈ s,
        { rw [← set.nonempty_def, ← set.ne_empty_iff_nonempty ],
          intro h, rw ← cardinal.mk_emptyc_iff at h,
          rw [h, ← nat.cast_zero, cardinal.nat_cast_inj] at hs,
          rw ← hs at hn,  simpa using hn },
      obtain ⟨a, ha⟩ := this,
      let t : set (sub_mul_action_of_stabilizer M α a) := coe ⁻¹' s,
      have hst : s = set.insert a (coe '' t),
      { ext,
        split,
        { intro hxs,
          cases classical.em (x = a) with hxa hxa,
          rw hxa, apply set.mem_insert,
          apply set.mem_insert_of_mem,  use x,
          refine and.intro _ rfl,
          simp only [set.mem_preimage, sub_mul_action.coe_mk], exact hxs },
        { intro hxat,
          cases set.mem_insert_iff.mp hxat with hxa hxt,
          rw hxa, exact ha,
          obtain ⟨y, hy, rfl⟩ := hxt,
          simpa only using hy } },
/-
      have hat : s \ {a} ⊆ (sub_mul_action_of_stabilizer M α a).carrier,
      begin
        rintros x ⟨hxs, hx⟩,
        simpa using hx,
      end,
      let t : set ↥(sub_mul_action_of_stabilizer M α a) := ⟨s \ {a}, hat⟩,

      have hast : s = set.insert a (s \ {a}),
      { apply subset_antisymm,
        apply set.subset_insert_diff_singleton,
        change insert _ _ ⊆ s, rw set.insert_subset,
        apply and.intro ha,
        exact set.diff_subset s {a} },
        -/

      rw hst,
--      let j := sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom' M a t,
      apply is_preprimitive_of_bihom _,
      exact (sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom'_bijective M a t).right,

      apply (hn_0 a).right t,
      rw hst at hs,

      have ha : a ∉ (coe '' t : set α),
      { rintro ⟨x, hx⟩,
        apply x.prop, rw hx.right, simp only [set.mem_singleton] },
      rw ← hs,
      let z : # ↥(set.insert a (coe '' t)) = _ := cardinal.mk_insert ha,
      rw z,
      rw cardinal.mk_image_eq  subtype.coe_injective }  },
end


-- PROBABLEMENT FAUX !
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

/-- The fixator of a subset of cardinal d in an n-primitive action
acts (n-d) primitively on the remaining (d ≤ n)-/
lemma remaining_primitivity {n : ℕ} (h : is_multiply_preprimitive M α n)
  {d : ℕ} (hdn : d ≤ n) {s : set α} (hs : #s = d) :
  is_multiply_preprimitive (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s) (n-d) :=
begin
  split,
  { apply remaining_transitivity M α d s hs, exact h.left, },
  { intros t ht,
    let t' : set α := coe '' t,
    have htt' : t = coe ⁻¹' t',
    { apply symm, apply set.preimage_image_eq, exact subtype.coe_injective, },
    rw htt',
    apply is_preprimitive_of_bihom (sub_mul_action_of_fixing_subgroup_union_bihom M s _)
      (function.bijective.surjective
        (sub_mul_action_of_fixing_subgroup_union_bihom_surjective M s t')),
    apply h.right,
    rw cardinal.mk_union_of_disjoint,
    rw [cardinal.mk_image_eq (subtype.coe_injective), add_assoc, ht, hs,
      ← nat.cast_add, cardinal.nat_cast_inj, nat.add_sub_of_le hdn],
    intro a, rintro ⟨has, ⟨b, hbt, rfl⟩⟩,
    exfalso, exact b.prop has }
end

/-- n.succ-fold pretransitivity implies n-fold preprimitivity -/
theorem is_multiply_preprimitive_of_multiply_pretransitive_succ {n : ℕ} (hn : 1 ≤ n) (hα : ↑n.succ ≤ #α)
  (h : is_multiply_pretransitive M α n.succ) : is_multiply_preprimitive M α n :=
begin
  split,
  apply is_multiply_pretransitive_of_higher M α h,
  exact nat.le_succ n,
  exact hα,

  obtain ⟨m, hm⟩ := nat.exists_eq_add_of_le hn,
  rw hm,
  intros s hs,
  apply is_preprimitive_of_two_pretransitive,
  suffices : 2 = n.succ - m,
  rw this,
  apply remaining_transitivity,
  { apply cardinal.add_cancel, rw ← nat.cast_one at hs,
    rw [hs, ← nat.cast_add, cardinal.nat_cast_inj],
    apply add_comm },
  exact h,
  simp only [hm, nat.succ_eq_one_add, ← add_assoc],
  norm_num,
end


end MultiplePrimitivity

#exit

section MultiplePrimitivity'

variables (M α : Type*) [group M] [mul_action M α]

def is_multiply_preprimitive' (n : ℕ) :=
  is_multiply_pretransitive M α n ∧
  (∀ (s : set α) (hs : #s < ↑n),
    is_preprimitive (fixing_subgroup M s)
      (sub_mul_action_of_fixing_subgroup M s))

lemma is_multiply_preprimitive'_of_higher {n : ℕ}
  {m : ℕ} (hmn : m ≤ n) (hα : ↑n ≤ #α)
  (hn : is_multiply_preprimitive' M α n) :
  is_multiply_preprimitive' M α m :=
begin
  apply and.intro (is_multiply_pretransitive_of_higher M α hn.left hmn hα),
  intros s hs,
  apply hn.right s,
  apply lt_of_lt_of_le hs,
  simp only [cardinal.nat_cast_le],
  exact hmn
end

lemma is_multiply_preprimitive'_zero :
  is_multiply_preprimitive' M α 0 :=
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

lemma is_multiply_preprimitive'_one_iff :
  is_multiply_preprimitive' M α 1 ↔ is_preprimitive M α :=
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

example (s : set α) (hs : is_empty ↥s) : s = ∅ :=
begin
  rw is_empty_iff at hs,
  rw ← set.not_nonempty_iff_eq_empty,
  rintro ⟨a, h⟩, apply hs, exact ⟨a,h⟩,
end

lemma is_multiply_preprimitive'_mk {n : ℕ} (hn : n ≥ 1) (h : is_pretransitive M α) : -- (hα : (n.succ : cardinal) ≤ #α):
  is_multiply_preprimitive' M α n.succ ↔
  ∀ (a : α), is_multiply_preprimitive' (stabilizer M a) (sub_mul_action_of_stabilizer M α a) n :=
begin
  split,
  { intros hn a,
    cases nat.lt_or_ge n 1 with h0 h1,
    { rw nat.lt_one_iff at h0, rw h0, apply is_multiply_preprimitive'_zero, },

    split,
    -- n-pretransitive
    exact (stabilizer.is_multiply_pretransitive M α h).mp hn.left a,

    -- multiple preprimitivity property
    intros s hs,

    let j := sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s,

    apply is_preprimitive_of_bihom j,
    exact (sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_bijective M a s).right,
    apply hn.right,

    suffices : # (set.insert a (coe '' s)) = # s + 1,
    { rw [this, nat.cast_add n 1, ← nat.cast_one],
      rw cardinal.lt_of_add_right_iff,
      exact hs },

    suffices : a ∉ coe '' s,
    let z : # ↥(set.insert a (coe '' s)) = _ := cardinal.mk_insert this,
    rw z,
    rw cardinal.mk_image_eq  subtype.coe_injective,

    rintro ⟨x, hx, hx'⟩,
    apply x.prop, simp only [set.mem_singleton_iff],
    exact hx' },
  { intro hn_0,
    split,
    { rw (stabilizer.is_multiply_pretransitive M α h),
      intro a, exact (hn_0 a).left },
    { intros s hs,
      rw [nat.cast_add n 1] at hs,
--      rw ← cardinal_lt_of_add_right_iff at hs,

      cases (is_empty_or_nonempty s) with hs_e hs_ne,
      -- s = ∅
      suffices : is_preprimitive M α,

      have hs_e' : #s = 0,
      { rw is_empty_iff at hs_e,
        rw cardinal.mk_emptyc_iff,
        rw ← set.not_nonempty_iff_eq_empty,
        rintro ⟨a, h⟩, apply hs_e, exact ⟨a,h⟩ },

      rw ← is_multiply_preprimitive'_one_iff at this,
      apply this.right s,
      rw [hs_e', ← nat.cast_zero, cardinal.nat_cast_lt],
      exact one_pos,

      -- PROBABLEMENT INCORRECT

      sorry,


      -- s.nonempty
/-      have : ∃ (a : α), a ∈ s,
        { rw [← set.nonempty_def, ← set.ne_empty_iff_nonempty ],
          intro h, rw ← cardinal.mk_emptyc_iff at h,
          rw [h, ← nat.cast_zero, cardinal.nat_cast_inj] at hs,
          rw ← hs at hn,  simpa using hn }, -/

      obtain ⟨⟨a, ha⟩,_⟩ := @set.exists_mem_of_nonempty s hs_ne,
      let t : set (sub_mul_action_of_stabilizer M α a) := coe ⁻¹' s,
      have hst : s = set.insert a (coe '' t),
      { ext,
        split,
        { intro hxs,
          cases classical.em (x = a) with hxa hxa,
          rw hxa, apply set.mem_insert,
          apply set.mem_insert_of_mem,  use x,
          refine and.intro _ rfl,
          simp only [set.mem_preimage, sub_mul_action.coe_mk], exact hxs },
        { intro hxat,
          cases set.mem_insert_iff.mp hxat with hxa hxt,
          rw hxa, exact ha,
          obtain ⟨y, hy, rfl⟩ := hxt,
          simpa only using hy } },
/-
      have hat : s \ {a} ⊆ (sub_mul_action_of_stabilizer M α a).carrier,
      begin
        rintros x ⟨hxs, hx⟩,
        simpa using hx,
      end,
      let t : set ↥(sub_mul_action_of_stabilizer M α a) := ⟨s \ {a}, hat⟩,

      have hast : s = set.insert a (s \ {a}),
      { apply subset_antisymm,
        apply set.subset_insert_diff_singleton,
        change insert _ _ ⊆ s, rw set.insert_subset,
        apply and.intro ha,
        exact set.diff_subset s {a} },
        -/

      rw hst,
      let j := sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom' M a t,
      apply is_preprimitive_of_bihom j,
      exact (sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom'_bijective M a t).right,

      apply (hn_0 a).right t,
      rw hst at hs,

      have ha : a ∉ (coe '' t : set α),
      { rintro ⟨x, hx⟩,
        apply x.prop, rw hx.right, simp only [set.mem_singleton] },

      let z : # ↥(set.insert a (coe '' t)) = _ := cardinal.mk_insert ha,
      rw [z, ← nat.cast_one, cardinal.mk_image_eq  subtype.coe_injective] at hs,
      exact cardinal.lt_of_add_right_iff.mp hs } },
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
