/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import probability.probability_mass_function.basic

/-!
# Monad Operations for Probability Mass Functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file constructs two operations on `pmf` that give it a monad structure.
`pure a` is the distribution where a single value `a` has probability `1`.
`bind pa pb : pmf β` is the distribution given by sampling `a : α` from `pa : pmf α`,
and then sampling from `pb a : pmf β` to get a final result `b : β`.

`bind_on_support` generalizes `bind` to allow binding to a partial function,
so that the second argument only needs to be defined on the support of the first argument.

-/

noncomputable theory
variables {α β γ : Type*}
open_locale classical big_operators nnreal ennreal
open measure_theory

namespace pmf

section pure

/-- The pure `pmf` is the `pmf` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
def pure (a : α) : pmf α := ⟨λ a', if a' = a then 1 else 0, has_sum_ite_eq _ _⟩

variables (a a' : α)

@[simp] lemma pure_apply : pure a a' = (if a' = a then 1 else 0) := rfl

@[simp] lemma support_pure : (pure a).support = {a} := set.ext (λ a', by simp [mem_support_iff])

lemma mem_support_pure_iff: a' ∈ (pure a).support ↔ a' = a := by simp

@[simp] lemma pure_apply_self : pure a a = 1 := if_pos rfl

lemma pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 := if_neg h

instance [inhabited α] : inhabited (pmf α) := ⟨pure default⟩

section measure

variable (s : set α)

@[simp] lemma to_outer_measure_pure_apply : (pure a).to_outer_measure s = if a ∈ s then 1 else 0 :=
begin
  refine (to_outer_measure_apply (pure a) s).trans _,
  split_ifs with ha ha,
  { refine ((tsum_congr (λ b, _)).trans (tsum_ite_eq a 1)),
    exact ite_eq_left_iff.2 (λ hb, symm (ite_eq_right_iff.2 (λ h, (hb $ h.symm ▸ ha).elim))) },
  { refine ((tsum_congr (λ b, _)).trans (tsum_zero)),
    exact ite_eq_right_iff.2 (λ hb, ite_eq_right_iff.2 (λ h, (ha $ h ▸ hb).elim)) }
end

variable [measurable_space α]

/-- The measure of a set under `pure a` is `1` for sets containing `a` and `0` otherwise -/
@[simp] lemma to_measure_pure_apply (hs : measurable_set s) :
  (pure a).to_measure s = if a ∈ s then 1 else 0 :=
(to_measure_apply_eq_to_outer_measure_apply (pure a) s hs).trans (to_outer_measure_pure_apply a s)

lemma to_measure_pure : (pure a).to_measure = measure.dirac a :=
measure.ext (λ s hs, by simpa only [to_measure_pure_apply a s hs, measure.dirac_apply' a hs])

@[simp] lemma to_pmf_dirac [countable α] [h : measurable_singleton_class α] :
  (measure.dirac a).to_pmf = pure a :=
by rw [to_pmf_eq_iff_to_measure_eq, to_measure_pure]

end measure

end pure

section bind

/-- The monadic bind operation for `pmf`. -/
def bind (p : pmf α) (f : α → pmf β) : pmf β :=
⟨λ b, ∑' a, p a * f a b, ennreal.summable.has_sum_iff.2 (ennreal.tsum_comm.trans $
  by simp only [ennreal.tsum_mul_left, tsum_coe, mul_one])⟩

variables (p : pmf α) (f : α → pmf β) (g : β → pmf γ)

@[simp] lemma bind_apply (b : β) : p.bind f b = ∑'a, p a * f a b := rfl

@[simp] lemma support_bind : (p.bind f).support = ⋃ a ∈ p.support, (f a).support :=
set.ext (λ b, by simp [mem_support_iff, ennreal.tsum_eq_zero, not_or_distrib])

lemma mem_support_bind_iff (b : β) : b ∈ (p.bind f).support ↔ ∃ a ∈ p.support, b ∈ (f a).support :=
by simp only [support_bind, set.mem_Union, set.mem_set_of_eq]

@[simp] lemma pure_bind (a : α) (f : α → pmf β) : (pure a).bind f = f a :=
have ∀ b a', ite (a' = a) 1 0 * f a' b = ite (a' = a) (f a b) 0, from
  assume b a', by split_ifs; simp; subst h; simp,
by ext b; simp [this]

@[simp] lemma bind_pure : p.bind pure = p :=
pmf.ext (λ x, (bind_apply _ _ _).trans (trans (tsum_eq_single x $
  (λ y hy, by rw [pure_apply_of_ne _ _ hy.symm, mul_zero])) $ by rw [pure_apply_self, mul_one]))

@[simp] lemma bind_const (p : pmf α) (q : pmf β) : p.bind (λ _, q) = q :=
pmf.ext (λ x, by rw [bind_apply, ennreal.tsum_mul_right, tsum_coe, one_mul])

@[simp] lemma bind_bind : (p.bind f).bind g = p.bind (λ a, (f a).bind g) :=
pmf.ext (λ b, by simpa only [ennreal.coe_eq_coe.symm, bind_apply, ennreal.tsum_mul_left.symm,
    ennreal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ennreal.tsum_comm)

lemma bind_comm (p : pmf α) (q : pmf β) (f : α → β → pmf γ) :
  p.bind (λ a, q.bind (f a)) = q.bind (λ b, p.bind (λ a, f a b)) :=
pmf.ext (λ b, by simpa only [ennreal.coe_eq_coe.symm, bind_apply, ennreal.tsum_mul_left.symm,
  ennreal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ennreal.tsum_comm)

section measure

variable (s : set β)

@[simp] lemma to_outer_measure_bind_apply :
  (p.bind f).to_outer_measure s = ∑' a, p a * (f a).to_outer_measure s :=
calc (p.bind f).to_outer_measure s
  = ∑' b, if b ∈ s then ∑' a, p a * f a b else 0 :
    by simp [to_outer_measure_apply, set.indicator_apply]
  ... = ∑' b a, p a * (if b ∈ s then f a b else 0) :
    tsum_congr (λ b, by split_ifs; simp)
  ... = ∑' a b, p a * (if b ∈ s then f a b else 0) :
    tsum_comm' ennreal.summable (λ _, ennreal.summable) (λ _, ennreal.summable)
  ... = ∑' a, p a * ∑' b, (if b ∈ s then f a b else 0) :
    tsum_congr (λ a, ennreal.tsum_mul_left)
  ... = ∑' a, p a * ∑' b, if b ∈ s then f a b else 0 :
    tsum_congr (λ a, congr_arg (λ x, (p a) * x) $ tsum_congr (λ b, by split_ifs; refl))
  ... = ∑' a, p a * (f a).to_outer_measure s :
    tsum_congr (λ a, by simp only [to_outer_measure_apply, set.indicator_apply])

/-- The measure of a set under `p.bind f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a` -/
@[simp] lemma to_measure_bind_apply [measurable_space β] (hs : measurable_set s) :
  (p.bind f).to_measure s = ∑' a, p a * (f a).to_measure s :=
(to_measure_apply_eq_to_outer_measure_apply (p.bind f) s hs).trans
  ((to_outer_measure_bind_apply p f s).trans (tsum_congr (λ a, congr_arg (λ x, p a * x)
  (to_measure_apply_eq_to_outer_measure_apply (f a) s hs).symm)))

end measure

end bind

instance : monad pmf :=
{ pure := λ A a, pure a,
  bind := λ A B pa pb, pa.bind pb }

section bind_on_support

/-- Generalized version of `bind` allowing `f` to only be defined on the support of `p`.
  `p.bind f` is equivalent to `p.bind_on_support (λ a _, f a)`, see `bind_on_support_eq_bind` -/
def bind_on_support (p : pmf α) (f : Π a ∈ p.support, pmf β) : pmf β :=
⟨λ b, ∑' a, p a * if h : p a = 0 then 0 else f a h b,
ennreal.summable.has_sum_iff.2 begin
  refine (ennreal.tsum_comm.trans (trans (tsum_congr $ λ a, _) p.tsum_coe)),
  simp_rw [ennreal.tsum_mul_left],
  split_ifs with h,
  { simp only [h, zero_mul] },
  { rw [(f a h).tsum_coe, mul_one] }
end⟩

variables {p : pmf α} (f : Π a ∈ p.support, pmf β)

@[simp] lemma bind_on_support_apply (b : β) :
  p.bind_on_support f b = ∑' a, p a * if h : p a = 0 then 0 else f a h b := rfl

@[simp] lemma support_bind_on_support :
  (p.bind_on_support f).support = ⋃ (a : α) (h : a ∈ p.support), (f a h).support :=
begin
  refine set.ext (λ b, _),
  simp only [ennreal.tsum_eq_zero, not_or_distrib, mem_support_iff,
    bind_on_support_apply, ne.def, not_forall, mul_eq_zero, set.mem_Union],
  exact ⟨λ hb, let ⟨a, ⟨ha, ha'⟩⟩ := hb in ⟨a, ha, by simpa [ha] using ha'⟩,
    λ hb, let ⟨a, ha, ha'⟩ := hb in ⟨a, ⟨ha, by simpa [(mem_support_iff _ a).1 ha] using ha'⟩⟩⟩
end

lemma mem_support_bind_on_support_iff (b : β) :
  b ∈ (p.bind_on_support f).support ↔ ∃ (a : α) (h : a ∈ p.support), b ∈ (f a h).support :=
by simp only [support_bind_on_support, set.mem_set_of_eq, set.mem_Union]

/-- `bind_on_support` reduces to `bind` if `f` doesn't depend on the additional hypothesis -/
@[simp] lemma bind_on_support_eq_bind (p : pmf α) (f : α → pmf β) :
  p.bind_on_support (λ a _, f a) = p.bind f :=
begin
  ext b x,
  have : ∀ a, ite (p a = 0) 0 (p a * f a b) = p a * f a b,
  from λ a, ite_eq_right_iff.2 (λ h, h.symm ▸ symm (zero_mul $ f a b)),
  simp only [bind_on_support_apply (λ a _, f a), p.bind_apply f,
    dite_eq_ite, mul_ite, mul_zero, this],
end

lemma bind_on_support_eq_zero_iff (b : β) :
  p.bind_on_support f b = 0 ↔ ∀ a (ha : p a ≠ 0), f a ha b = 0 :=
begin
  simp only [bind_on_support_apply, ennreal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left],
  exact ⟨λ h a ha, trans (dif_neg ha).symm (h a ha), λ h a ha, trans (dif_neg ha) (h a ha)⟩,
end

@[simp] lemma pure_bind_on_support (a : α) (f : Π (a' : α) (ha : a' ∈ (pure a).support), pmf β) :
  (pure a).bind_on_support f = f a ((mem_support_pure_iff a a).mpr rfl) :=
begin
  refine pmf.ext (λ b, _),
  simp only [bind_on_support_apply, pure_apply],
  refine trans (tsum_congr (λ a', _)) (tsum_ite_eq a _),
  by_cases h : (a' = a); simp [h],
end

lemma bind_on_support_pure (p : pmf α) :
  p.bind_on_support (λ a _, pure a) = p :=
by simp only [pmf.bind_pure, pmf.bind_on_support_eq_bind]

@[simp] lemma bind_on_support_bind_on_support (p : pmf α)
  (f : ∀ a ∈ p.support, pmf β)
  (g : ∀ (b ∈ (p.bind_on_support f).support), pmf γ) :
  (p.bind_on_support f).bind_on_support g =
    p.bind_on_support (λ a ha, (f a ha).bind_on_support
      (λ b hb, g b ((mem_support_bind_on_support_iff f b).mpr ⟨a, ha, hb⟩))) :=
begin
  refine pmf.ext (λ a, _),
  simp only [ennreal.coe_eq_coe.symm, bind_on_support_apply, ← tsum_dite_right,
    ennreal.tsum_mul_left.symm, ennreal.tsum_mul_right.symm],
  simp only [ennreal.tsum_eq_zero, ennreal.coe_eq_coe, ennreal.coe_eq_zero, ennreal.coe_zero,
    dite_eq_left_iff, mul_eq_zero],
  refine ennreal.tsum_comm.trans (tsum_congr (λ a', tsum_congr (λ b, _))),
  split_ifs,
  any_goals { ring1 },
  { have := h_1 a', simp [h] at this, contradiction },
  { simp [h_2], },
end

lemma bind_on_support_comm (p : pmf α) (q : pmf β)
  (f : ∀ (a ∈ p.support) (b ∈ q.support), pmf γ) :
  p.bind_on_support (λ a ha, q.bind_on_support (f a ha)) =
    q.bind_on_support (λ b hb, p.bind_on_support (λ a ha, f a ha b hb)) :=
begin
  apply pmf.ext, rintro c,
  simp only [ennreal.coe_eq_coe.symm, bind_on_support_apply, ← tsum_dite_right,
    ennreal.tsum_mul_left.symm, ennreal.tsum_mul_right.symm],
  refine trans (ennreal.tsum_comm) (tsum_congr (λ b, tsum_congr (λ a, _))),
  split_ifs with h1 h2 h2; ring,
end

section measure

variable (s : set β)

@[simp] lemma to_outer_measure_bind_on_support_apply : (p.bind_on_support f).to_outer_measure s
  = ∑' a, p a * if h : p a = 0 then 0 else (f a h).to_outer_measure s :=
begin
  simp only [to_outer_measure_apply, set.indicator_apply, bind_on_support_apply],
  calc ∑' b, ite (b ∈ s) (∑' a, p a * dite (p a = 0) (λ h, 0) (λ h, f a h b)) 0
    = ∑' b a, ite (b ∈ s) (p a * dite (p a = 0) (λ h, 0) (λ h, f a h b)) 0 :
      tsum_congr (λ b, by split_ifs with hbs; simp only [eq_self_iff_true, tsum_zero])
    ... = ∑' a b, ite (b ∈ s) (p a * dite (p a = 0) (λ h, 0) (λ h, f a h b)) 0 : ennreal.tsum_comm
    ... = ∑' a, p a * ∑' b, ite (b ∈ s) (dite (p a = 0) (λ h, 0) (λ h, f a h b)) 0 :
      tsum_congr (λ a, by simp only [← ennreal.tsum_mul_left, mul_ite, mul_zero])
    ... = ∑' a, p a * dite (p a = 0) (λ h, 0) (λ h, ∑' b, ite (b ∈ s) (f a h b) 0) :
      tsum_congr (λ a, by split_ifs with ha; simp only [if_t_t, tsum_zero, eq_self_iff_true])
end

/-- The measure of a set under `p.bind_on_support f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a _`.
  The additional if statement is needed since `f` is only a partial function -/
@[simp] lemma to_measure_bind_on_support_apply [measurable_space β] (hs : measurable_set s) :
  (p.bind_on_support f).to_measure s
    = ∑' a, p a * if h : p a = 0 then 0 else (f a h).to_measure s :=
by simp only [to_measure_apply_eq_to_outer_measure_apply _ _ hs,
  to_outer_measure_bind_on_support_apply]

end measure

end bind_on_support

end pmf
