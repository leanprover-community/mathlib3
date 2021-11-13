/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import measure_theory.probability_mass_function.basic

/-!
# Specific Constructions of Probability Mass Functions

This file gives a number of different `pmf` constructions for common probability distributions.

`map` and `seq` allow pushing a `pmf α` along a function `f : α → β` (or distribution of
functions `f : pmf (α → β)`) to get a `pmf β`

`of_finset` and `of_fintype` simplify the construction of a `pmf α` from a function `f : α → ℝ≥0`,
by allowing the "sum equals 1" constraint to be in terms of `finset.sum` instead of `tsum`.
`of_multiset`, `uniform_of_finset`, and `uniform_of_fintype` construct probability mass functions
from the corresponding object, with proportional weighting for each element of the object.

`normalize` constructs a `pmf α` by normalizing a function `f : α → ℝ≥0` by its sum,
and `filter` uses this to filter the support of a `pmf` and re-normalize the new distribution.

`bind_on_support` generalizes `bind` to allow binding to a partial function,
so that the second argument only needs to be defined on the support of the first argument.

`bernoulli` represents the bernoulli distribution on `bool`

-/

namespace pmf

noncomputable theory
variables {α : Type*} {β : Type*} {γ : Type*}
open_locale classical big_operators nnreal ennreal

section map

/-- The functorial action of a function on a `pmf`. -/
def map (f : α → β) (p : pmf α) : pmf β := bind p (pure ∘ f)

lemma bind_pure_comp (f : α → β) (p : pmf α) : bind p (pure ∘ f) = map f p := rfl

lemma map_id (p : pmf α) : map id p = p := by simp [map]

lemma map_comp (p : pmf α) (f : α → β) (g : β → γ) : (p.map f).map g = p.map (g ∘ f) :=
by simp [map]

lemma pure_map (a : α) (f : α → β) : (pure a).map f = pure (f a) :=
by simp [map]

end map

section seq

/-- The monadic sequencing operation for `pmf`. -/
def seq (f : pmf (α → β)) (p : pmf α) : pmf β := f.bind (λ m, p.bind $ λ a, pure (m a))

end seq

section of_finite

/-- Given a finset `s` and a function `f : α → ℝ≥0` with sum `1` on `s`,
  such that `f x = 0` for `x ∉ s`, we get a `pmf` -/
def of_finset (f : α → ℝ≥0) (s : finset α) (h : ∑ x in s, f x = 1)
  (h' : ∀ x ∉ s, f x = 0) : pmf α :=
⟨f, h ▸ has_sum_sum_of_ne_finset_zero h'⟩

@[simp]
lemma of_finset_apply {f : α → ℝ≥0} {s : finset α} (h : ∑ x in s, f x = 1)
  (h' : ∀ x ∉ s, f x = 0) (a : α) : of_finset f s h h' a = f a :=
rfl

lemma of_finset_apply_of_not_mem {f : α → ℝ≥0} {s : finset α} (h : ∑ x in s, f x = 1)
  (h' : ∀ x ∉ s, f x = 0) {a : α} (ha : a ∉ s) : of_finset f s h h' a = 0 :=
h' a ha

/-- Given a finite type `α` and a function `f : α → ℝ≥0` with sum 1, we get a `pmf`. -/
def of_fintype [fintype α] (f : α → ℝ≥0) (h : ∑ x, f x = 1) : pmf α :=
of_finset f finset.univ h (λ x hx, absurd (finset.mem_univ x) hx)

@[simp]
lemma of_fintype_apply [fintype α] {f : α → ℝ≥0} (h : ∑ x, f x = 1)
  (a : α) : of_fintype f h a = f a :=
rfl

/-- Given a non-empty multiset `s` we construct the `pmf` which sends `a` to the fraction of
  elements in `s` that are `a`. -/
def of_multiset (s : multiset α) (hs : s ≠ 0) : pmf α :=
⟨λ a, s.count a / s.card,
  have ∑ a in s.to_finset, (s.count a : ℝ) / s.card = 1,
    by simp [div_eq_inv_mul, finset.mul_sum.symm, (nat.cast_sum _ _).symm, hs],
  have ∑ a in s.to_finset, (s.count a : ℝ≥0) / s.card = 1,
    by rw [← nnreal.eq_iff, nnreal.coe_one, ← this, nnreal.coe_sum]; simp,
  begin
    rw ← this,
    apply has_sum_sum_of_ne_finset_zero,
    simp {contextual := tt},
  end⟩

@[simp]
lemma of_multiset_apply {s : multiset α} (hs : s ≠ 0) (a : α) :
  of_multiset s hs a = s.count a / s.card :=
rfl

lemma of_multiset_apply_of_not_mem {s : multiset α} (hs : s ≠ 0)
  {a : α} (ha : a ∉ s) : of_multiset s hs a = 0 :=
div_eq_zero_iff.2 (or.inl $ nat.cast_eq_zero.2 $ multiset.count_eq_zero_of_not_mem ha)

end of_finite

section uniform

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def uniform_of_finset (s : finset α) (hs : s.nonempty) : pmf α :=
of_finset (λ a, if a ∈ s then (s.card : ℝ≥0)⁻¹ else 0) s (Exists.rec_on hs (λ x hx,
  calc ∑ (a : α) in s, ite (a ∈ s) (s.card : ℝ≥0)⁻¹ 0
    = ∑ (a : α) in s, (s.card : ℝ≥0)⁻¹ : finset.sum_congr rfl (λ x hx, by simp [hx])
    ... = s.card • (s.card : ℝ≥0)⁻¹ : finset.sum_const _
    ... = (s.card : ℝ≥0) * (s.card : ℝ≥0)⁻¹ : by rw nsmul_eq_mul
    ... = 1 : div_self (nat.cast_ne_zero.2 $ finset.card_ne_zero_of_mem hx)
  )) (λ x hx, by simp only [hx, if_false])

@[simp]
lemma uniform_of_finset_apply {s : finset α} (hs : s.nonempty) (a : α) :
  uniform_of_finset s hs a = if a ∈ s then (s.card : ℝ≥0)⁻¹ else 0 :=
rfl

lemma uniform_of_finset_apply_of_mem {s : finset α} (hs : s.nonempty) {a : α} (ha : a ∈ s) :
  uniform_of_finset s hs a = (s.card)⁻¹ :=
by simp [ha]

lemma uniform_of_finset_apply_of_not_mem {s : finset α} (hs : s.nonempty) {a : α} (ha : a ∉ s) :
  uniform_of_finset s hs a = 0 :=
by simp [ha]

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def uniform_of_fintype (α : Type*) [fintype α] [nonempty α] : pmf α :=
  uniform_of_finset (finset.univ) (finset.univ_nonempty)

@[simp]
lemma uniform_of_fintype_apply [fintype α] [nonempty α] (a : α) :
  uniform_of_fintype α a = (fintype.card α)⁻¹ :=
by simpa only [uniform_of_fintype, finset.mem_univ, if_true, uniform_of_finset_apply]

end uniform

section normalize

/-- Given a `f` with non-zero sum, we get a `pmf` by normalizing `f` by it's `tsum` -/
def normalize (f : α → ℝ≥0) (hf0 : tsum f ≠ 0) : pmf α :=
⟨λ a, f a * (∑' x, f x)⁻¹,
  (mul_inv_cancel hf0) ▸ has_sum.mul_right (∑' x, f x)⁻¹
    (not_not.mp (mt tsum_eq_zero_of_not_summable hf0 : ¬¬summable f)).has_sum⟩

lemma normalize_apply {f : α → ℝ≥0} (hf0 : tsum f ≠ 0) (a : α) :
  (normalize f hf0) a = f a * (∑' x, f x)⁻¹ := rfl

end normalize

section filter

/-- Create new `pmf` by filtering on a set with non-zero measure and normalizing -/
def filter (p : pmf α) (s : set α) (h : ∃ a ∈ s, p a ≠ 0) : pmf α :=
pmf.normalize (s.indicator p) $ nnreal.tsum_indicator_ne_zero p.2.summable h

lemma filter_apply (p : pmf α) {s : set α} (h : ∃ a ∈ s, p a ≠ 0) {a : α} :
  (p.filter s h) a = (s.indicator p a) * (∑' x, (s.indicator p) x)⁻¹ :=
by rw [filter, normalize_apply]

lemma filter_apply_eq_zero_of_not_mem (p : pmf α) {s : set α} (h : ∃ a ∈ s, p a ≠ 0)
  {a : α} (ha : a ∉ s) : (p.filter s h) a = 0 :=
by rw [filter_apply, set.indicator_apply_eq_zero.mpr (λ ha', absurd ha' ha), zero_mul]

lemma filter_apply_eq_zero_iff (p : pmf α) {s : set α} (h : ∃ a ∈ s, p a ≠ 0) (a : α) :
  (p.filter s h) a = 0 ↔ a ∉ (p.support ∩ s) :=
begin
  rw [set.mem_inter_iff, p.mem_support_iff, not_and_distrib, not_not],
  split; intro ha,
  { rw [filter_apply, mul_eq_zero] at ha,
    refine ha.by_cases
      (λ ha, (em (a ∈ s)).by_cases (λ h, or.inl ((set.indicator_apply_eq_zero.mp ha) h)) or.inr)
      (λ ha, absurd (inv_eq_zero.1 ha) (nnreal.tsum_indicator_ne_zero p.2.summable h)) },
  { rw [filter_apply, set.indicator_apply_eq_zero.2 (λ h, ha.by_cases id (absurd h)), zero_mul] }
end

lemma filter_apply_ne_zero_iff (p : pmf α) {s : set α} (h : ∃ a ∈ s, p a ≠ 0) (a : α) :
  (p.filter s h) a ≠ 0 ↔ a ∈ (p.support ∩ s) :=
by rw [← not_iff, filter_apply_eq_zero_iff, not_iff, not_not]

end filter

section bernoulli

/-- A `pmf` which assigns probability `p` to `tt` and `1 - p` to `ff`. -/
def bernoulli (p : ℝ≥0) (h : p ≤ 1) : pmf bool :=
of_fintype (λ b, cond b p (1 - p)) (nnreal.eq $ by simp [h])

@[simp]
lemma bernuolli_apply {p : ℝ≥0} (h : p ≤ 1) (b : bool) :
  bernoulli p h b = cond b p (1 - p) :=
rfl

end bernoulli

section bind_on_support

protected lemma bind_on_support.summable (p : pmf α) (f : ∀ a ∈ p.support, pmf β) (b : β) :
  summable (λ a : α, p a * if h : p a = 0 then 0 else f a h b) :=
begin
  refine nnreal.summable_of_le (assume a, _) p.summable_coe,
  split_ifs,
  { refine (mul_zero (p a)).symm ▸ le_of_eq h.symm },
  { suffices : p a * f a h b ≤ p a * 1, { simpa },
    exact mul_le_mul_of_nonneg_left ((f a h).coe_le_one _) (p a).2 }
end

/-- Generalized version of `bind` allowing `f` to only be defined on the support of `p`.
  `p.bind f` is equivalent to `p.bind_on_support (λ a _, f a)`, see `bind_on_support_eq_bind` -/
def bind_on_support (p : pmf α) (f : ∀ a ∈ p.support, pmf β) : pmf β :=
⟨λ b, ∑' a, p a * if h : p a = 0 then 0 else f a h b,
ennreal.has_sum_coe.1 begin
  simp only [ennreal.coe_tsum (bind_on_support.summable p f _)],
  rw [ennreal.summable.has_sum_iff, ennreal.tsum_comm],
  simp only [ennreal.coe_mul, ennreal.coe_one, ennreal.tsum_mul_left],
  have : ∑' (a : α), (p a : ennreal) = 1 :=
    by simp only [←ennreal.coe_tsum p.summable_coe, ennreal.coe_one, tsum_coe],
  refine trans (tsum_congr (λ a, _)) this,
  split_ifs with h,
  { simp [h] },
  { simp [← ennreal.coe_tsum (f a h).summable_coe, (f a h).tsum_coe] }
end⟩

@[simp] lemma bind_on_support_apply (p : pmf α) (f : ∀ a ∈ p.support, pmf β) (b : β) :
  p.bind_on_support f b = ∑' a, p a * if h : p a = 0 then 0 else f a h b := rfl

/-- `bind_on_support` reduces to `bind` if `f` doesn't depend on the additional hypothesis -/
@[simp] lemma bind_on_support_eq_bind (p : pmf α) (f : α → pmf β) :
  p.bind_on_support (λ a _, f a) = p.bind f :=
begin
  ext b,
  simp only [p.bind_on_support_apply (λ a _, f a), p.bind_apply f,
    dite_eq_ite, nnreal.coe_eq, mul_ite, mul_zero],
  refine congr_arg _ (funext (λ a, _)),
  split_ifs with h; simp [h],
end

lemma coe_bind_on_support_apply (p : pmf α) (f : ∀ a ∈ p.support, pmf β) (b : β) :
  (p.bind_on_support f b : ℝ≥0∞) = ∑' a, p a * if h : p a = 0 then 0 else f a h b :=
by simp only [bind_on_support_apply, ennreal.coe_tsum (bind_on_support.summable p f b),
    dite_cast, ennreal.coe_mul, ennreal.coe_zero]

@[simp] lemma mem_support_bind_on_support_iff (p : pmf α) (f : ∀ a ∈ p.support, pmf β) (b : β) :
  b ∈ (p.bind_on_support f).support ↔ ∃ a (ha : p a ≠ 0), b ∈ (f a ha).support :=
begin
  simp only [mem_support_iff, bind_on_support_apply,
    tsum_ne_zero_iff (bind_on_support.summable p f b), mul_ne_zero_iff],
  split; { rintro ⟨a, ha, haf⟩, refine ⟨a, ha, ne_of_eq_of_ne _ haf⟩, simp [ha], },
end

lemma bind_on_support_eq_zero_iff (p : pmf α) (f : ∀ a ∈ p.support, pmf β) (b : β) :
  p.bind_on_support f b = 0 ↔ ∀ a (ha : p a ≠ 0), f a ha b = 0 :=
begin
  simp only [bind_on_support_apply, tsum_eq_zero_iff (bind_on_support.summable p f b),
    mul_eq_zero, or_iff_not_imp_left],
  exact ⟨λ h a ha, trans (dif_neg ha).symm (h a ha), λ h a ha, trans (dif_neg ha) (h a ha)⟩,
end

@[simp] lemma pure_bind_on_support (a : α) (f : ∀ (a' : α) (ha : a' ∈ (pure a).support), pmf β) :
  (pure a).bind_on_support f = f a ((mem_support_pure_iff a a).mpr rfl) :=
begin
  refine pmf.ext (λ b, _),
  simp only [nnreal.coe_eq, bind_on_support_apply, pure_apply],
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
      (λ b hb, g b ((p.mem_support_bind_on_support_iff f b).mpr ⟨a, ha, hb⟩))) :=
begin
  refine pmf.ext (λ a, _),
  simp only [ennreal.coe_eq_coe.symm, coe_bind_on_support_apply, ← tsum_dite_right,
    ennreal.tsum_mul_left.symm, ennreal.tsum_mul_right.symm],
  refine trans (ennreal.tsum_comm) (tsum_congr (λ a', _)),
  split_ifs with h,
  { simp only [h, ennreal.coe_zero, zero_mul, tsum_zero] },
  { simp only [← ennreal.tsum_mul_left, ← mul_assoc],
    refine tsum_congr (λ b, _),
    split_ifs with h1 h2 h2,
    any_goals { ring1 },
    { rw bind_on_support_eq_zero_iff at h1,
      simp only [h1 a' h, ennreal.coe_zero, zero_mul, mul_zero] },
    { simp only [h2, ennreal.coe_zero, mul_zero, zero_mul] } }
end

lemma bind_on_support_comm (p : pmf α) (q : pmf β)
  (f : ∀ (a ∈ p.support) (b ∈ q.support), pmf γ) :
  p.bind_on_support (λ a ha, q.bind_on_support (f a ha)) =
    q.bind_on_support (λ b hb, p.bind_on_support (λ a ha, f a ha b hb)) :=
begin
  apply pmf.ext, rintro c,
  simp only [ennreal.coe_eq_coe.symm, coe_bind_on_support_apply, ← tsum_dite_right,
    ennreal.tsum_mul_left.symm, ennreal.tsum_mul_right.symm],
  refine trans (ennreal.tsum_comm) (tsum_congr (λ b, tsum_congr (λ a, _))),
  split_ifs with h1 h2 h2; ring,
end

end bind_on_support

end pmf
