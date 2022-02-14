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
import tactic.group

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
@[to_additive]
def ordered_cancel_comm_monoid.is_finer {α : Type u} (r s : ordered_cancel_comm_monoid α) : Prop :=
  @has_le.le α (@preorder.to_has_le α
    (@partial_order.to_preorder α
      (@ordered_cancel_comm_monoid.to_partial_order α r))) ≤
  @has_le.le α (@preorder.to_has_le α
    (@partial_order.to_preorder α
      (@ordered_cancel_comm_monoid.to_partial_order α s)))

/--
Any ordered group can be extended to a linear ordered group.
-/
@[to_additive]
theorem extend_ordered_group {α : Type u} [o : ordered_cancel_comm_monoid α]
  (h_norm : ∀ (x y : α), (∃ (n : ℕ) (hn : n ≠ 0), y ^ n ≤ x ^ n) → y ≤ x) : -- fuchs calls this normal
  ∃ l : linear_ordered_cancel_comm_monoid α, ordered_cancel_comm_monoid.is_finer o
    (@linear_ordered_cancel_comm_monoid.to_ordered_cancel_comm_monoid α l) :=
begin
  let S := { s | is_partial_order α s ∧
                (∀ a b c : α, s a b ↔ s (c * a) (c * b)) ∧
                ∀ x y, (∃ (n : ℕ) (hn : n ≠ 0), s (y ^ n) (x ^ n)) → s y x },
  have hS : ∀ C, C ⊆ S → zorn.chain (≤) C → ∀ y ∈ C, ∃ ub ∈ S, ∀ z ∈ C, z ≤ ub,
  { rintro C hC₁ hC₂ s hs,
    haveI := (hC₁ hs).1.1,
    refine ⟨Sup C, _, λ z hz, le_Sup hz⟩,
    refine ⟨{ refl := _, trans := _, antisymm := _ }, _, _⟩,
    any_goals{ simp_rw binary_relation_Sup_iff},
    { intro x,
      exact ⟨s, hs, refl x⟩ },
    { rintro x y z ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩,
      haveI : is_partial_order _ _ := (hC₁ h₁s₁).1,
      haveI : is_partial_order _ _ := (hC₁ h₁s₂).1,
      cases hC₂.total_of_refl h₁s₁ h₁s₂,
      { exact ⟨s₂, h₁s₂, trans (h _ _ h₂s₁) h₂s₂⟩ },
      { exact ⟨s₁, h₁s₁, trans h₂s₁ (h _ _ h₂s₂)⟩ } },
    { rintro x y ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩,
      haveI : is_partial_order _ _ := (hC₁ h₁s₁).1,
      haveI : is_partial_order _ _ := (hC₁ h₁s₂).1,
      cases hC₂.total_of_refl h₁s₁ h₁s₂,
      { exact antisymm (h _ _ h₂s₁) h₂s₂ },
      { apply antisymm h₂s₁ (h _ _ h₂s₂) } },
    { intros x y z,
      split;
      rintros ⟨s₁, h₁s₁, h₂s₁⟩; -- TODO is this junk removable?
      use [s₁, h₁s₁],
      rwa ← (hC₁ h₁s₁).2.1,
      rwa (hC₁ h₁s₁).2.1, },
    { rintro x y ⟨n, hn, r, hr₁, hr₂⟩,
      use [r, hr₁, (hC₁ hr₁).2.2 _ _ ⟨n, hn, hr₂⟩], }, },
  obtain ⟨s, ⟨hs₁, hs₁a, hs₁b⟩, rs, hs₂⟩ := zorn.zorn_nonempty_partial_order₀ S hS (≤)
    ⟨is_partial_order.mk, λ a b c, by rw mul_le_mul_iff_left, h_norm⟩,
  resetI,
  have inst_refl : is_refl α s := by apply_instance, -- probably dont need to be haveI's
  have inst_trans : is_trans α s := by apply_instance,
  have inst_antisymm : is_antisymm α s := by apply_instance,
  let t : linear_ordered_cancel_comm_monoid α :=
    { le := s,
      le_refl := inst_refl.refl,
      le_trans := inst_trans.trans,
      le_antisymm := inst_antisymm.antisymm,
      le_total := _,
      decidable_le := by apply_instance,
      mul_le_mul_left := λ a b hab c, (hs₁a a _ _).mp hab,
      le_of_mul_le_mul_left := λ a b c, (hs₁a b c a).mpr,
      ..(@ordered_cancel_comm_monoid.to_cancel_comm_monoid α o)},
  refine ⟨t, rs⟩,
  intros x y,
  change s x y ∨ s y x,
  by_contra h,
  let s' := λ x' y', ∃ p q (hpq : p ≠ 0 ∨ q ≠ 0), s (y ^ q * x' ^ p) (y' ^ p * x ^ q),
  have hfine : s ≤ s',
  { intros a b h, --finer
    use [1, 0],
    simpa, },
  have hp : ∀ x' y' {p q} (hpq : p ≠ 0 ∨ q ≠ 0) (hs' : s (y ^ q * x' ^ p) (y' ^ p * x ^ q)), p ≠ 0,
  { rintro x' y' p q (hpq | hpq) hs',
    { assumption, },
    intro hp,
    apply h,
    right,
    simp only [hp, mul_one, pow_zero, one_mul] at hs',
    simpa using hs₁b _ _ ⟨q, hpq, hs'⟩, },
  rw ← hs₂ s' _ hfine at h,
  { exact h (or.inl ⟨1, 1, by simp, refl _⟩) }, -- case α ????    v) in Nakada
  { have key : ∀ (a b c : α) (pab qab : ℕ) (habn : pab ≠ 0 ∨ qab ≠ 0)
      (hab : s (y ^ qab * a ^ pab) (b ^ pab * x ^ qab)) (pbc qbc : ℕ) (hbcn : pbc ≠ 0 ∨ qbc ≠ 0)
      (hbc : s (y ^ qbc * b ^ pbc) (c ^ pbc * x ^ qbc)),
      (pab * pbc ≠ 0 ∨ qab * pbc + qbc * pab ≠ 0) ∧
      s (y ^ (qab * pbc + qbc * pab) * a ^ (pab * pbc))
        (c ^ (pab * pbc) * x ^ (qab * pbc + qbc * pab)),
    { intros a b c pab qab habn hab pbc qbc hbcn hbc,
      have habp : pab ≠ 0 := hp _ _ habn hab,
      have hbcp : pbc ≠ 0 := hp _ _ hbcn hbc,
      split,
      { left,
        intro hprod,
        rw [nat.mul_eq_zero] at hprod,
        tauto, },
      rw [pow_add],
      have : ∀ (l k : α) (n : ℕ), s k l → s (k ^ n) (l ^ n),
      { intros l k n hlk,
        induction n,
        { rw [pow_zero, pow_zero],
          exact refl _, },
        { simp only [nat.succ_eq_add_one, pow_add, pow_one],
          apply trans (_ : s (k ^ n_n * k) (l ^ n_n * k)),
          rwa ← hs₁a,
          rwa [mul_comm _ k, mul_comm _ k, ← hs₁a], }, },
      apply trans _ (_ : s (y ^ (qbc * pab) * b ^ (pab * pbc) * x ^ (qab * pbc))
                         (c ^ (pab * pbc) * x ^ (qab * pbc + qbc * pab))),
      { rw [mul_comm (y ^ (qab * pbc)) (y ^ (qbc * pab)), mul_assoc, mul_assoc, ← hs₁a],
        convert this _ _ pbc hab using 1,
        { simp [mul_pow, pow_mul], },
        { simp [mul_pow, pow_mul, mul_comm], }, },
      { rw [add_comm, pow_add, ← mul_assoc,
          mul_comm _ (x ^ (qab * _)), mul_comm _ (x ^ (qab * _)), ← hs₁a],
        convert this _ _ pab hbc using 1,
        { simp [mul_pow, pow_mul' b, pow_mul y], },
        { simp [mul_pow, pow_mul' c, pow_mul x], }, }, },
    have trans : ∀ (a b c : α), s' a b → s' b c → s' a c,
    { rintro a b c ⟨pab, qab, habn, hab⟩ ⟨pbc, qbc, hbcn, hbc⟩,
      use [pab * pbc, qab * pbc + qbc * pab],
      exact key a b c pab qab habn hab pbc qbc hbcn hbc, },
    repeat {split},
    refine
      { refl := λ x, hfine x x (refl x),
        trans := trans,
        antisymm := _ },
    { rintros a b ⟨pab, qab, habn, hab⟩ ⟨pba, qba, hban, hba⟩, -- antisymm
      have hpabn := hp _ _ habn hab,
      have hqabn := hp _ _ hban hba,
      obtain ⟨keyl, keyr⟩ := key a b a pab qab habn hab pba qba hban hba,
      have : s (y ^ (qab * pba + qba * pab)) (x ^ (qab * pba + qba * pab)),
      -- this requires cancellation (strongness)
      { rwa [mul_comm, ← hs₁a] at keyr, },
      by_cases hqs : qab = 0 ∧ qba = 0,
      { simp only [hqs, pow_zero, one_mul, mul_one] at hab hba,
        apply antisymm (_ : s a b),
        { refine hs₁b _ _ ⟨_, _, hba⟩,
          tauto, },
        { refine hs₁b _ _ ⟨_, _, hab⟩,
          tauto, }, },
      exfalso,
      have : s y x := hs₁b _ _ ⟨_, _, this⟩,
      tauto,
      intro hz,
      simp only [add_eq_zero_iff, nat.mul_eq_zero] at hz,
      tauto, },
    { rintros a b c, -- homog
      refine exists₂_congr _,
      simp only [exists_prop, and.congr_right_iff],
      intros pab qab habn,
      rw [mul_pow, mul_pow, ← mul_assoc, mul_comm _ (c ^ _), mul_assoc, mul_assoc, ← hs₁a], },
    { rintros a b ⟨n, hnn, ⟨pn, qn, han, ha⟩⟩, -- normal
      use [pn * n, qn],
      split,
      { left,
        simp only [hnn, ne.def, nat.mul_eq_zero, or_false],
        exact hp _ _ han ha, },
      simpa [pow_mul'] using ha, }, },
end

-- TODO this lemma missing for groups?
-- have : (a / b) ^ n = a ^ n / b ^ n,

def linear_group_extension (α : Type u) : Type u := α

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
