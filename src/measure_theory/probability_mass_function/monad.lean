/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import measure_theory.probability_mass_function.basic

/-!
# Monadic structure on probability mass functions

This file features the monadic structure of `pmf`.
The pure `pmf` is the `pmf` where all the mass lies in one point.

The `bind : ∀ (pa : pmf α) (pb : α → pmf β), pmf β` operation is the distribution
given by sampling `a : α` from `pa` and then sampling a value `b : β` from `pb a`.
The explicit probability of choosing `b : β` is the sum over `a : α` of `pa a * pb a b`.

Explicit measures of sets under these constructions are given by
`to_measure_pure_apply` and `to_measure_bind_apply`
-/

namespace pmf

noncomputable theory
variables {α : Type*} {β : Type*} {γ : Type*}
open_locale classical big_operators nnreal ennreal

section pure

/-- The pure `pmf` is the `pmf` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
def pure (a : α) : pmf α := ⟨λ a', if a' = a then 1 else 0, has_sum_ite_eq _ _⟩

variables (a a' : α)

@[simp] lemma pure_apply : pure a a' = (if a' = a then 1 else 0) := rfl

@[simp] lemma support_pure : (pure a).support = {a} := set.ext (λ a', by simp [mem_support_iff])

lemma mem_support_pure_iff: a' ∈ (pure a).support ↔ a' = a := by simp

instance [inhabited α] : inhabited (pmf α) := ⟨pure (default α)⟩

section measure

lemma to_outer_measure_pure_apply (a : α) (s : set α) :
  (pure a).to_outer_measure s = if a ∈ s then 1 else 0 :=
begin
  refine (to_outer_measure_apply' (pure a) s).trans _,
  split_ifs with ha ha,
  { refine ennreal.coe_eq_one.2 ((tsum_congr (λ b, _)).trans (tsum_ite_eq a 1)),
    exact ite_eq_left_iff.2 (λ hb, symm (ite_eq_right_iff.2 (λ h, (hb $ h.symm ▸ ha).elim))) },
  { refine ennreal.coe_eq_zero.2 ((tsum_congr (λ b, _)).trans (tsum_zero)),
    exact ite_eq_right_iff.2 (λ hb, ite_eq_right_iff.2 (λ h, (ha $ h ▸ hb).elim)) }
end

/-- The measure of a set under `pure a` is `1` for sets containing `a` and `0` otherwise -/
lemma to_measure_pure_apply [measurable_space α] (a : α) (s : set α) (hs : measurable_set s) :
  (pure a).to_measure s = if a ∈ s then 1 else 0 :=
(to_measure_apply_eq_to_outer_measure_apply (pure a) s hs).trans (to_outer_measure_pure_apply a s)

end measure

end pure

section bind

protected lemma bind.summable (p : pmf α) (f : α → pmf β) (b : β) :
  summable (λ a : α, p a * f a b) :=
begin
  refine nnreal.summable_of_le (assume a, _) p.summable_coe,
  suffices : p a * f a b ≤ p a * 1, { simpa },
  exact mul_le_mul_of_nonneg_left ((f a).coe_le_one _) (p a).2
end

/-- The monadic bind operation for `pmf`. -/
def bind (p : pmf α) (f : α → pmf β) : pmf β :=
⟨λ b, ∑'a, p a * f a b,
  begin
    apply ennreal.has_sum_coe.1,
    simp only [ennreal.coe_tsum (bind.summable p f _)],
    rw [ennreal.summable.has_sum_iff, ennreal.tsum_comm],
    simp [ennreal.tsum_mul_left, (ennreal.coe_tsum (f _).summable_coe).symm,
      (ennreal.coe_tsum p.summable_coe).symm]
  end⟩

variables (p : pmf α) (f : α → pmf β)

@[simp] lemma bind_apply (b : β) : p.bind f b = ∑'a, p a * f a b := rfl

@[simp] lemma support_bind : (p.bind f).support = {b | ∃ a ∈ p.support, b ∈ (f a).support} :=
set.ext (λ b, by simp [mem_support_iff, tsum_eq_zero_iff (bind.summable p f b), not_or_distrib])

lemma mem_support_bind_iff (b : β) : b ∈ (p.bind f).support ↔ ∃ a ∈ p.support, b ∈ (f a).support :=
by simp

lemma coe_bind_apply (p : pmf α) (f : α → pmf β) (b : β) :
  (p.bind f b : ℝ≥0∞) = ∑'a, p a * f a b :=
eq.trans (ennreal.coe_tsum $ bind.summable p f b) $ by simp

@[simp] lemma pure_bind (a : α) (f : α → pmf β) : (pure a).bind f = f a :=
have ∀ b a', ite (a' = a) 1 0 * f a' b = ite (a' = a) (f a b) 0, from
  assume b a', by split_ifs; simp; subst h; simp,
by ext b; simp [this]

@[simp] lemma bind_pure (p : pmf α) : p.bind pure = p :=
have ∀ a a', (p a * ite (a' = a) 1 0) = ite (a = a') (p a') 0, from
  assume a a', begin split_ifs; try { subst a }; try { subst a' }; simp * at * end,
by ext b; simp [this]

@[simp] lemma bind_bind (p : pmf α) (f : α → pmf β) (g : β → pmf γ) :
  (p.bind f).bind g = p.bind (λ a, (f a).bind g) :=
begin
  ext1 b,
  simp only [ennreal.coe_eq_coe.symm, coe_bind_apply, ennreal.tsum_mul_left.symm,
             ennreal.tsum_mul_right.symm],
  rw [ennreal.tsum_comm],
  simp [mul_assoc, mul_left_comm, mul_comm]
end

lemma bind_comm (p : pmf α) (q : pmf β) (f : α → β → pmf γ) :
  p.bind (λ a, q.bind (f a)) = q.bind (λ b, p.bind (λ a, f a b)) :=
begin
  ext1 b,
  simp only [ennreal.coe_eq_coe.symm, coe_bind_apply, ennreal.tsum_mul_left.symm,
             ennreal.tsum_mul_right.symm],
  rw [ennreal.tsum_comm],
  simp [mul_assoc, mul_left_comm, mul_comm]
end

section measure

lemma to_outer_measure_bind_apply (pa : pmf α) (pb : α → pmf β) (s : set β) :
  (pa.bind pb).to_outer_measure s = ∑' (a : α), pa a * (pb a).to_outer_measure s :=
calc (pa.bind pb).to_outer_measure s
      = ∑' (b : β), if b ∈ s then ↑(∑' (a : α), pa a * pb a b) else 0
    : by simp [to_outer_measure_apply, set.indicator_apply]
  ... = ∑' (b : β), ↑(∑' (a : α), pa a * (if b ∈ s then pb a b else 0))
    : tsum_congr (λ b, by split_ifs; simp)
  ... = ∑' (b : β) (a : α), ↑(pa a * (if b ∈ s then pb a b else 0))
    : tsum_congr (λ b, ennreal.coe_tsum $
        nnreal.summable_of_le (by split_ifs; simp) (bind.summable pa pb b))
  ... = ∑' (a : α) (b : β), ↑(pa a) * ↑(if b ∈ s then pb a b else 0)
    : ennreal.tsum_comm.trans (tsum_congr $ λ a, tsum_congr $ λ b, ennreal.coe_mul)
  ... = ∑' (a : α), ↑(pa a) * ∑' (b : β), ↑(if b ∈ s then pb a b else 0)
    : tsum_congr (λ a, ennreal.tsum_mul_left)
  ... = ∑' (a : α), ↑(pa a) * ∑' (b : β), if b ∈ s then ↑(pb a b) else (0 : ℝ≥0∞)
    : tsum_congr (λ a, congr_arg (λ x, ↑(pa a) * x) $ tsum_congr (λ b, by split_ifs; refl))
  ... = ∑' (a : α), ↑(pa a) * (pb a).to_outer_measure s
    : tsum_congr (λ a, by rw [to_outer_measure_apply, set.indicator])

/-- The measure of a set under `pa.bind pb` is the sum over `a : α`
  of the probability of `a` under `pa` times the measure of the set under `pb a` -/
lemma to_measure_bind_apply [measurable_space β] (pa : pmf α) (pb : α → pmf β) (s : set β) (hs : measurable_set s) :
  (pa.bind pb).to_measure s = ∑' (a : α), pa a * (pb a).to_measure s :=
(to_measure_apply_eq_to_outer_measure_apply (pa.bind pb) s hs).trans
  ((to_outer_measure_bind_apply pa pb s).trans (tsum_congr (λ a, congr_arg (λ x, pa a * x)
  (to_measure_apply_eq_to_outer_measure_apply (pb a) s hs).symm)))

end measure

end bind

instance : monad pmf :=
{ pure := λ α a, pure a,
  bind := λ α β pa pb, pa.bind pb }

end pmf
