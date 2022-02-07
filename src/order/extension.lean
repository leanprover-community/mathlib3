/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.set.lattice
import order.zorn
import tactic.by_contra
import algebra.group_power.basic
import algebra.smul_with_zero
import algebra.module

/-!
# Extend a partial order to a linear order

This file constructs a linear order which is an extension of the given partial order, using Zorn's
lemma.
-/

universes u
open set classical
open_locale classical

/--
Any partial order can be extended to a linear order.
-/
theorem extend_partial_order {α : Type u} (r : α → α → Prop) [is_partial_order α r] :
  ∃ (s : α → α → Prop) (_ : is_linear_order α s), r ≤ s :=
begin
  let S := {s | is_partial_order α s},
  have hS : ∀ c, c ⊆ S → zorn.chain (≤) c → ∀ y ∈ c, (∃ ub ∈ S, ∀ z ∈ c, z ≤ ub),
  { rintro c hc₁ hc₂ s hs,
    haveI := (hc₁ hs).1,
    refine ⟨Sup c, _, λ z hz, le_Sup hz⟩,
    refine { refl := _, trans := _, antisymm := _ }; simp_rw binary_relation_Sup_iff,
    { intro x,
      exact ⟨s, hs, refl x⟩ },
    { rintro x y z ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩,
      haveI : is_partial_order _ _ := hc₁ h₁s₁,
      haveI : is_partial_order _ _ := hc₁ h₁s₂,
      cases hc₂.total_of_refl h₁s₁ h₁s₂,
      { exact ⟨s₂, h₁s₂, trans (h _ _ h₂s₁) h₂s₂⟩ },
      { exact ⟨s₁, h₁s₁, trans h₂s₁ (h _ _ h₂s₂)⟩ } },
    { rintro x y ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩,
      haveI : is_partial_order _ _ := hc₁ h₁s₁,
      haveI : is_partial_order _ _ := hc₁ h₁s₂,
      cases hc₂.total_of_refl h₁s₁ h₁s₂,
      { exact antisymm (h _ _ h₂s₁) h₂s₂ },
      { apply antisymm h₂s₁ (h _ _ h₂s₂) } } },
  obtain ⟨s, hs₁ : is_partial_order _ _, rs, hs₂⟩ := zorn.zorn_nonempty_partial_order₀ S hS r ‹_›,
  resetI,
  refine ⟨s, { total := _ }, rs⟩,
  intros x y,
  by_contra' h,
  let s' := λ x' y', s x' y' ∨ s x' x ∧ s y y',
  rw ←hs₂ s' _ (λ _ _, or.inl) at h,
  { apply h.1 (or.inr ⟨refl _, refl _⟩) },
  { refine
      { refl := λ x, or.inl (refl _),
        trans := _,
        antisymm := _ },
    { rintro a b c (ab | ⟨ax : s a x, yb : s y b⟩) (bc | ⟨bx : s b x, yc : s y c⟩),
      { exact or.inl (trans ab bc), },
      { exact or.inr ⟨trans ab bx, yc⟩ },
      { exact or.inr ⟨ax, trans yb bc⟩ },
      { exact or.inr ⟨ax, yc⟩ } },
    { rintro a b (ab | ⟨ax : s a x, yb : s y b⟩) (ba | ⟨bx : s b x, ya : s y a⟩),
      { exact antisymm ab ba },
      { exact (h.2 (trans ya (trans ab bx))).elim },
      { exact (h.2 (trans yb (trans ba ax))).elim },
      { exact (h.2 (trans yb bx)).elim } } },
end

/-- A type alias for `α`, intended to extend a partial order on `α` to a linear order. -/
def linear_extension (α : Type u) : Type u := α

noncomputable instance {α : Type u} [partial_order α] : linear_order (linear_extension α) :=
{ le := (extend_partial_order ((≤) : α → α → Prop)).some,
  le_refl := (extend_partial_order ((≤) : α → α → Prop)).some_spec.some.1.1.1.1,
  le_trans := (extend_partial_order ((≤) : α → α → Prop)).some_spec.some.1.1.2.1,
  le_antisymm := (extend_partial_order ((≤) : α → α → Prop)).some_spec.some.1.2.1,
  le_total := (extend_partial_order ((≤) : α → α → Prop)).some_spec.some.2.1,
  decidable_le := classical.dec_rel _ }

/-- The embedding of `α` into `linear_extension α` as a relation homomorphism. -/
def to_linear_extension {α : Type u} [partial_order α] :
  ((≤) : α → α → Prop) →r ((≤) : linear_extension α → linear_extension α → Prop) :=
{ to_fun := λ x, x,
  map_rel' := λ a b, (extend_partial_order ((≤) : α → α → Prop)).some_spec.some_spec _ _ }

instance {α : Type u} [inhabited α] : inhabited (linear_extension α) :=
⟨(default : α)⟩

/-
E.g.
fin 2 → ℕ


(a,b) ≤ (c,d) ↔ a ≤ c ∧ b ≤ d

(1,0) (0,1)
-/

/- s is finer than r, more things are related -/
def is_finer {α : Type u} (r s : ordered_add_comm_group α) : Prop :=
  @has_le.le α (@preorder.to_has_le α
    (@partial_order.to_preorder α
      (@ordered_add_comm_group.to_partial_order α r))) ≤
  @has_le.le α (@preorder.to_has_le α
    (@partial_order.to_preorder α
      (@ordered_add_comm_group.to_partial_order α s)))

/--
Any ordered group can be extended to a linear ordered group.
-/
theorem extend_ordered_group {α : Type u} [o : ordered_add_comm_group α]
  (h_norm : ∀ (x : α), (∃ (n : ℕ) (hn : n ≠ 0), 0 ≤ n • x) → 0 ≤ x) : -- fuchs calls this normal
  ∃ l : linear_ordered_add_comm_group α, is_finer o
    (@linear_ordered_add_comm_group.to_ordered_add_comm_group α l) :=
begin
  let S := {s | is_partial_order α s ∧
                (∀ a b : α, s a b → ∀ c : α, s (c + a) (c + b)) ∧
                ∀ x, (∃ (n : ℕ) (hn : n ≠ 0), s 0 (n • x)) → s 0 x },
  have hS : ∀ c, c ⊆ S → zorn.chain (≤) c → ∀ y ∈ c, (∃ ub ∈ S, ∀ z ∈ c, z ≤ ub),
  { rintro c hc₁ hc₂ s hs,
    haveI := (hc₁ hs).1.1,
    refine ⟨Sup c, _, λ z hz, le_Sup hz⟩,
    refine ⟨{ refl := _, trans := _, antisymm := _ }, _, _⟩,
    any_goals{ simp_rw binary_relation_Sup_iff},
    { intro x,
      exact ⟨s, hs, refl x⟩ },
    { rintro x y z ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩,
      haveI : is_partial_order _ _ := (hc₁ h₁s₁).1,
      haveI : is_partial_order _ _ := (hc₁ h₁s₂).1,
      cases hc₂.total_of_refl h₁s₁ h₁s₂,
      { exact ⟨s₂, h₁s₂, trans (h _ _ h₂s₁) h₂s₂⟩ },
      { exact ⟨s₁, h₁s₁, trans h₂s₁ (h _ _ h₂s₂)⟩ } },
    { rintro x y ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩,
      haveI : is_partial_order _ _ := (hc₁ h₁s₁).1,
      haveI : is_partial_order _ _ := (hc₁ h₁s₂).1,
      cases hc₂.total_of_refl h₁s₁ h₁s₂,
      { exact antisymm (h _ _ h₂s₁) h₂s₂ },
      { apply antisymm h₂s₁ (h _ _ h₂s₂) } },
    { rintro x y ⟨s₁, h₁s₁, h₂s₁⟩ z, -- TODO is this junk removable?
      use [s₁, h₁s₁, (hc₁ h₁s₁).2.1 _ _ h₂s₁ z], },
    { rintro x ⟨n, hn, r, hr₁, hr₂⟩,
      use [r, hr₁, (hc₁ hr₁).2.2 _ ⟨n, hn, hr₂⟩], }, },
  obtain ⟨s, ⟨hs₁, hs₁a, hs₁b⟩, rs, hs₂⟩ := zorn.zorn_nonempty_partial_order₀ S hS (≤)
    ⟨is_partial_order.mk, o.add_le_add_left, h_norm⟩,
  resetI,
  haveI inst_refl : is_refl α s := by apply_instance, -- probably dont need to be haveI's
  haveI inst_trans : is_trans α s := by apply_instance,
  haveI inst_antisymm : is_antisymm α s := by apply_instance,
  let t : linear_ordered_add_comm_group α :=
    { le := s,
      le_refl := inst_refl.refl,
      le_trans := inst_trans.trans,
      le_antisymm := inst_antisymm.antisymm,
      le_total := _,
      decidable_le := by apply_instance,
      add_le_add_left := hs₁a,
      ..(@ordered_add_comm_group.to_add_comm_group α o)},
  refine ⟨t, rs⟩,
  intros x y,
  change s x y ∨ s y x,
  by_contra h,
  let s' := λ x' y', ∃ p q (hpq : p ≠ 0 ∨ q ≠ 0), s (q • (y - x)) (p • (y' - x')), -- s x' y' ∨ s x' x ∧ s y y',
  have hp : ∀ (x') (y') {p q} (hpq : p ≠ 0 ∨ q ≠ 0) (hs' : s (q • (y - x)) (p • (y' - x'))), p ≠ 0,
  { rintro x' y' p q hpq hs',
    cases hpq, assumption,
    intro hp,
    rw not_or_distrib at h,
    apply h.2,
    simp only [hp, zero_smul] at hs',
    have : s 0 (q • (x - y)),
    { have : s (q • (x - y) + q • (y - x)) (q • (x - y) + 0),
      exact hs₁a _ _ hs' _,
      simpa [← smul_add], },
    have : s (y + 0) (y + (x - y)) := hs₁a _ _ (hs₁b _ ⟨_, hpq, this⟩) y,
    simpa, },
  rw ← hs₂ s' _ _ at h,
  { exact h (or.inl ⟨1, 1, by simp, refl _⟩) }, -- case α ????    v) in Nakada
  { have key : ∀ (a b c : α) (pab qab : ℕ) (habn : pab ≠ 0 ∨ qab ≠ 0)
      (hab : s (qab • (y - x)) (pab • (b - a))) (pbc qbc : ℕ) (hbcn : pbc ≠ 0 ∨ qbc ≠ 0)
      (hbc : s (qbc • (y - x)) (pbc • (c - b))),
      (pab * pbc ≠ 0 ∨ qab * pbc + qbc * pab ≠ 0) ∧
      s ((qab * pbc + qbc * pab) • (y - x)) ((pab * pbc) • (c - a)),
    { intros a b c pab qab habn hab pbc qbc hbcn hbc,
      have habp : pab ≠ 0 := hp _ _ habn hab,
      have hbcp : pbc ≠ 0 := hp _ _ hbcn hbc,
      split,
      { left,
        intro hprod,
        rw [nat.mul_eq_zero] at hprod,
        tauto, },
      rw [← sub_add_sub_cancel' b a c],
      rw smul_add,
      rw add_smul,
      have : ∀ (l k : α) (n : ℕ), s k l → s (n • k) (n • l),
      { intros l k n hlk,
        induction n,
        { simp,
          exact refl _, },
        { simp [nat.succ_eq_add_one, add_smul],
          apply trans (_ : s (n_n • k + k) (n_n • l + k)),
          apply hs₁a,
          assumption,
          rw [add_comm _ k, add_comm _ k],
          apply hs₁a,
          assumption, }, },
      apply trans (_ : s ((qab * pbc) • (y - x) + (qbc * pab) • (y - x))
                         ((qab * pbc) • (y - x) + (pab * pbc) • (c - b))),
      { rw [add_comm _ ((pab * pbc) • (c - b))],
        rw [add_comm _ ((pab * pbc) • (c - b))],
        apply hs₁a,
        convert this _ _ pbc hab using 1,
        { rw [mul_smul, smul_comm], },
        { rw [mul_smul, smul_comm], }, },
      { apply hs₁a,
        convert this _ _ pab hbc using 1,
        { rw [mul_smul, smul_comm], },
        { rw [mul_smul, smul_comm], }, }, },
    have trans : ∀ (a b c : α), s' a b → s' b c → s' a c,
    { rintro a b c ⟨pab, qab, habn, hab⟩ ⟨pbc, qbc, hbcn, hbc⟩,
      use [pab * pbc, qab * pbc + qbc * pab],
      exact key a b c pab qab habn hab pbc qbc hbcn hbc, },
    repeat {split},
    refine
      { refl := _,
        trans := _,
        antisymm := _ },
    { intro x,
      use [1,0],
      simp only [ne.def, nat.one_ne_zero, not_false_iff, eq_self_iff_true, not_true,
        or_false, zero_smul, sub_self, smul_zero', true_and],
      exact refl _, },
    { exact trans },
    { rintros a b ⟨pab, qab, habn, hab⟩ ⟨pba, qba, hban, hba⟩, -- antisymm
      have hpabn := hp _ _ habn hab,
      have hqabn := hp _ _ hban hba,
      obtain ⟨keyl, keyr⟩ := key a b a pab qab habn hab pba qba hban hba,
      simp only [sub_self, smul_zero] at keyr,
      have : s 0 ((qab * pba + qba * pab) • (x - y)),
      { simpa [← smul_add] using hs₁a _ _ keyr ((qab * pba + qba * pab) • (x - y)), },
      by_cases hqs : qab = 0 ∧ qba = 0,
      { simp only [hqs, zero_smul] at hab hba,
        apply antisymm (_ : s a b),
        { have := hs₁b _ ⟨_, _, hba⟩,
          simpa using hs₁a _ _ this b,
          tauto, },
        { have := hs₁b _ ⟨_, _, hab⟩,
          simpa using hs₁a _ _ this a,
          tauto, }, },
      exfalso,
      have : s 0 (x - y) := hs₁b _ ⟨_, _, this⟩,
      have := hs₁a _ _ this y,
      simp only [add_zero, add_sub_cancel'_right] at this,
      tauto,
      intro hz,
      simp only [add_eq_zero_iff, nat.mul_eq_zero] at hz,
      tauto, },
    { rintros a b ⟨pab, qab, habn, hab⟩ c, -- homog
      use [pab, qab, habn],
      simpa, },
    { rintros a ⟨n, hnn, ⟨pn, qn, han, ha⟩⟩, -- normal
      use [pn * n, qn],
      split,
      { left,
        simp only [hnn, ne.def, nat.mul_eq_zero, or_false],
        exact hp _ _ han ha, },
      simpa [mul_smul] using ha, }, },
  { intros a b h, --finer
    use [1, 0],
    simp only [ne.def, nat.one_ne_zero, not_false_iff, eq_self_iff_true, not_true,
      or_false, zero_smul, one_nsmul, true_and],
    convert hs₁a _ _ h (-a),
    simp only [add_left_neg],
    exact sub_eq_neg_add b a, },
end


-- def linear_extension (α : Type u) : Type u := α

-- noncomputable instance {α : Type u} [partial_order α] : linear_order (linear_extension α) :=
-- { le := (extend_partial_order ((≤) : α → α → Prop)).some,
--   le_refl := (extend_partial_order ((≤) : α → α → Prop)).some_spec.some.1.1.1.1,
--   le_trans := (extend_partial_order ((≤) : α → α → Prop)).some_spec.some.1.1.2.1,
--   le_antisymm := (extend_partial_order ((≤) : α → α → Prop)).some_spec.some.1.2.1,
--   le_total := (extend_partial_order ((≤) : α → α → Prop)).some_spec.some.2.1,
--   decidable_le := classical.dec_rel _ }

-- /-- The embedding of `α` into `linear_extension α` as a relation homomorphism. -/
-- def to_linear_extension {α : Type u} [partial_order α] :
--   ((≤) : α → α → Prop) →r ((≤) : linear_extension α → linear_extension α → Prop) :=
-- { to_fun := λ x, x,
--   map_rel' := λ a b, (extend_partial_order ((≤) : α → α → Prop)).some_spec.some_spec _ _ }

-- instance {α : Type u} [inhabited α] : inhabited (linear_extension α) :=
-- ⟨(default : α)⟩
--
