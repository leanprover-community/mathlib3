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

variables (f : α → β) (p : pmf α) (b : β)

@[simp] lemma map_apply : (map f p) b = ∑' a, if b = f a then p a else 0 := by simp [map]

@[simp] lemma support_map : (map f p).support = f '' p.support :=
set.ext (λ b, by simp [map, @eq_comm β b])

lemma mem_support_map_iff : b ∈ (map f p).support ↔ ∃ a ∈ p.support, f a = b := by simp

lemma bind_pure_comp : bind p (pure ∘ f) = map f p := rfl

lemma map_id : map id p = p := by simp [map]

lemma map_comp (g : β → γ) : (p.map f).map g = p.map (g ∘ f) :=
by simp [map]

lemma pure_map (a : α) : (pure a).map f = pure (f a) :=
by simp [map]

end map

section seq

/-- The monadic sequencing operation for `pmf`. -/
def seq (q : pmf (α → β)) (p : pmf α) : pmf β := q.bind (λ m, p.bind $ λ a, pure (m a))

variables (q : pmf (α → β)) (p : pmf α) (b : β)

@[simp] lemma seq_apply : (seq q p) b = ∑' (f : α → β) (a : α), if b = f a then q f * p a else 0 :=
begin
  simp only [seq, mul_boole, bind_apply, pure_apply],
  refine tsum_congr (λ f, (nnreal.tsum_mul_left (q f) _).symm.trans (tsum_congr (λ a, _))),
  simpa only [mul_zero] using mul_ite (b = f a) (q f) (p a) 0
end

@[simp] lemma support_seq : (seq q p).support = ⋃ f ∈ q.support, f '' p.support :=
set.ext (λ b, by simp [-mem_support_iff, seq, @eq_comm β b])

lemma mem_support_seq_iff : b ∈ (seq q p).support ↔ ∃ (f ∈ q.support), b ∈ f '' p.support :=
by simp

end seq

section of_finset

/-- Given a finset `s` and a function `f : α → ℝ≥0` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `pmf` -/
def of_finset (f : α → ℝ≥0) (s : finset α) (h : ∑ a in s, f a = 1)
  (h' : ∀ a ∉ s, f a = 0) : pmf α :=
⟨f, h ▸ has_sum_sum_of_ne_finset_zero h'⟩

variables {f : α → ℝ≥0} {s : finset α} (h : ∑ a in s, f a = 1) (h' : ∀ a ∉ s, f a = 0)

@[simp] lemma of_finset_apply (a : α) : of_finset f s h h' a = f a := rfl

@[simp] lemma support_of_finset : (of_finset f s h h').support = s ∩ (function.support f) :=
set.ext (λ a, by simpa [mem_support_iff] using mt (h' a))

lemma mem_support_of_finset_iff (a : α) : a ∈ (of_finset f s h h').support ↔ a ∈ s ∧ f a ≠ 0 :=
by simp

lemma of_finset_apply_of_not_mem {a : α} (ha : a ∉ s) : of_finset f s h h' a = 0 :=
h' a ha

end of_finset

section of_fintype

/-- Given a finite type `α` and a function `f : α → ℝ≥0` with sum 1, we get a `pmf`. -/
def of_fintype [fintype α] (f : α → ℝ≥0) (h : ∑ a, f a = 1) : pmf α :=
of_finset f finset.univ h (λ a ha, absurd (finset.mem_univ a) ha)

variables [fintype α] {f : α → ℝ≥0} (h : ∑ a, f a = 1)

@[simp] lemma of_fintype_apply (a : α) : of_fintype f h a = f a := rfl

@[simp] lemma support_of_fintype : (of_fintype f h).support = function.support f := rfl

lemma mem_support_of_fintype_iff (a : α) : a ∈ (of_fintype f h).support ↔ f a ≠ 0 := iff.rfl

end of_fintype

section of_multiset

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

variables {s : multiset α} (hs : s ≠ 0)

@[simp] lemma of_multiset_apply (a : α) : of_multiset s hs a = s.count a / s.card := rfl

@[simp] lemma support_of_multiset : (of_multiset s hs).support = s.to_finset :=
set.ext (by simp [mem_support_iff, hs])

lemma mem_support_of_multiset_iff (a : α) : a ∈ (of_multiset s hs).support ↔ a ∈ s.to_finset :=
by simp

lemma of_multiset_apply_of_not_mem {a : α} (ha : a ∉ s) : of_multiset s hs a = 0 :=
div_eq_zero_iff.2 (or.inl $ nat.cast_eq_zero.2 $ multiset.count_eq_zero_of_not_mem ha)

end of_multiset

section uniform

section uniform_of_finset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def uniform_of_finset (s : finset α) (hs : s.nonempty) : pmf α :=
of_finset (λ a, if a ∈ s then (s.card : ℝ≥0)⁻¹ else 0) s (Exists.rec_on hs (λ x hx,
  calc ∑ (a : α) in s, ite (a ∈ s) (s.card : ℝ≥0)⁻¹ 0
    = ∑ (a : α) in s, (s.card : ℝ≥0)⁻¹ : finset.sum_congr rfl (λ x hx, by simp [hx])
    ... = s.card • (s.card : ℝ≥0)⁻¹ : finset.sum_const _
    ... = (s.card : ℝ≥0) * (s.card : ℝ≥0)⁻¹ : by rw nsmul_eq_mul
    ... = 1 : div_self (nat.cast_ne_zero.2 $ finset.card_ne_zero_of_mem hx)
  )) (λ x hx, by simp only [hx, if_false])

variables {s : finset α} (hs : s.nonempty) {a : α}

@[simp] lemma uniform_of_finset_apply (a : α) :
  uniform_of_finset s hs a = if a ∈ s then (s.card : ℝ≥0)⁻¹ else 0 := rfl

lemma uniform_of_finset_apply_of_mem (ha : a ∈ s) : uniform_of_finset s hs a = (s.card)⁻¹ :=
by simp [ha]

lemma uniform_of_finset_apply_of_not_mem (ha : a ∉ s) : uniform_of_finset s hs a = 0 :=
by simp [ha]

@[simp] lemma support_uniform_of_finset : (uniform_of_finset s hs).support = s :=
set.ext (let ⟨a, ha⟩ := hs in by simp [mem_support_iff, finset.ne_empty_of_mem ha])

lemma mem_support_uniform_of_finset_iff (a : α) : a ∈ (uniform_of_finset s hs).support ↔ a ∈ s :=
by simp

end uniform_of_finset

section uniform_of_fintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def uniform_of_fintype (α : Type*) [fintype α] [nonempty α] : pmf α :=
  uniform_of_finset (finset.univ) (finset.univ_nonempty)

variables [fintype α] [nonempty α]

@[simp] lemma uniform_of_fintype_apply (a : α) : uniform_of_fintype α a = (fintype.card α)⁻¹ :=
by simpa only [uniform_of_fintype, finset.mem_univ, if_true, uniform_of_finset_apply]

variable (α)

@[simp] lemma support_uniform_of_fintype : (uniform_of_fintype α).support = ⊤ :=
set.ext (λ x, by simpa [mem_support_iff] using fintype.card_ne_zero)

variable {α}

lemma mem_support_uniform_of_fintype_iff (a : α) : a ∈ (uniform_of_fintype α).support := by simp

end uniform_of_fintype

end uniform

section normalize

/-- Given a `f` with non-zero sum, we get a `pmf` by normalizing `f` by it's `tsum` -/
def normalize (f : α → ℝ≥0) (hf0 : tsum f ≠ 0) : pmf α :=
⟨λ a, f a * (∑' x, f x)⁻¹,
  (mul_inv_cancel hf0) ▸ has_sum.mul_right (∑' x, f x)⁻¹
    (not_not.mp (mt tsum_eq_zero_of_not_summable hf0 : ¬¬summable f)).has_sum⟩

variables {f : α → ℝ≥0} (hf0 : tsum f ≠ 0)

@[simp] lemma normalize_apply (a : α) : (normalize f hf0) a = f a * (∑' x, f x)⁻¹ := rfl

@[simp] lemma support_normalize : (normalize f hf0).support = function.support f :=
set.ext (by simp [mem_support_iff, hf0])

lemma mem_support_normalize_iff (a : α) : a ∈ (normalize f hf0).support ↔ f a ≠ 0 := by simp

end normalize

section filter

/-- Create new `pmf` by filtering on a set with non-zero measure and normalizing -/
def filter (p : pmf α) (s : set α) (h : ∃ a ∈ s, a ∈ p.support) : pmf α :=
pmf.normalize (s.indicator p) $ nnreal.tsum_indicator_ne_zero p.2.summable h

variables {p : pmf α} {s : set α} (h : ∃ a ∈ s, a ∈ p.support)

@[simp]
lemma filter_apply (a : α) : (p.filter s h) a = (s.indicator p a) * (∑' a', (s.indicator p) a')⁻¹ :=
by rw [filter, normalize_apply]

lemma filter_apply_eq_zero_of_not_mem {a : α} (ha : a ∉ s) : (p.filter s h) a = 0 :=
by rw [filter_apply, set.indicator_apply_eq_zero.mpr (λ ha', absurd ha' ha), zero_mul]

@[simp] lemma support_filter : (p.filter s h).support = s ∩ p.support:=
begin
  refine set.ext (λ a, _),
  rw [mem_support_iff, filter_apply, mul_ne_zero_iff, set.indicator_eq_zero_iff],
  exact ⟨λ ha, ha.1, λ ha, ⟨ha, inv_ne_zero (nnreal.tsum_indicator_ne_zero p.2.summable h)⟩⟩
end

lemma mem_support_filter_iff (a : α) : a ∈ (p.filter s h).support ↔ a ∈ s ∧ a ∈ p.support :=
by simp

lemma filter_apply_eq_zero_iff (a : α) : (p.filter s h) a = 0 ↔ a ∉ s ∨ a ∉ p.support :=
by erw [apply_eq_zero_iff, support_filter, set.mem_inter_iff, not_and_distrib]

lemma filter_apply_ne_zero_iff (a : α) : (p.filter s h) a ≠ 0 ↔ a ∈ s ∧ a ∈ p.support :=
by rw [ne.def, filter_apply_eq_zero_iff, not_or_distrib, not_not, not_not]

end filter

section bernoulli

/-- A `pmf` which assigns probability `p` to `tt` and `1 - p` to `ff`. -/
def bernoulli (p : ℝ≥0) (h : p ≤ 1) : pmf bool :=
of_fintype (λ b, cond b p (1 - p)) (nnreal.eq $ by simp [h])

variables {p : ℝ≥0} (h : p ≤ 1) (b : bool)

@[simp] lemma bernoulli_apply : bernoulli p h b = cond b p (1 - p) := rfl

@[simp] lemma support_bernoulli : (bernoulli p h).support = {b | cond b (p ≠ 0) (p ≠ 1)} :=
begin
  refine set.ext (λ b, _),
  induction b,
  { simp_rw [mem_support_iff, bernoulli_apply, bool.cond_ff, ne.def, tsub_eq_zero_iff_le, not_le],
    exact ⟨ne_of_lt, lt_of_le_of_ne h⟩ },
  { simp only [mem_support_iff, bernoulli_apply, bool.cond_tt, set.mem_set_of_eq], }
end

lemma mem_support_bernoulli_iff : b ∈ (bernoulli p h).support ↔ cond b (p ≠ 0) (p ≠ 1) := by simp

end bernoulli

section bind_on_support

protected lemma bind_on_support.summable (p : pmf α) (f : Π a ∈ p.support, pmf β) (b : β) :
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
def bind_on_support (p : pmf α) (f : Π a ∈ p.support, pmf β) : pmf β :=
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

variables {p : pmf α} (f : Π a ∈ p.support, pmf β)

@[simp] lemma bind_on_support_apply (b : β) :
  p.bind_on_support f b = ∑' a, p a * if h : p a = 0 then 0 else f a h b :=
rfl

@[simp] lemma support_bind_on_support :
  (p.bind_on_support f).support = {b | ∃ (a : α) (h : a ∈ p.support), b ∈ (f a h).support} :=
begin
  refine set.ext (λ b, _),
  simp only [tsum_eq_zero_iff (bind_on_support.summable p f b), not_or_distrib, mem_support_iff,
    bind_on_support_apply, ne.def, not_forall, mul_eq_zero],
  exact ⟨λ hb, let ⟨a, ⟨ha, ha'⟩⟩ := hb in ⟨a, ha, by simpa [ha] using ha'⟩,
    λ hb, let ⟨a, ha, ha'⟩ := hb in ⟨a, ⟨ha, by simpa [(mem_support_iff _ a).1 ha] using ha'⟩⟩⟩
end

lemma mem_support_bind_on_support_iff (b : β) :
  b ∈ (p.bind_on_support f).support ↔ ∃ (a : α) (h : a ∈ p.support), b ∈ (f a h).support :=
by simp

/-- `bind_on_support` reduces to `bind` if `f` doesn't depend on the additional hypothesis -/
@[simp] lemma bind_on_support_eq_bind (p : pmf α) (f : α → pmf β) :
  p.bind_on_support (λ a _, f a) = p.bind f :=
begin
  ext b,
  simp only [bind_on_support_apply (λ a _, f a), p.bind_apply f,
    dite_eq_ite, nnreal.coe_eq, mul_ite, mul_zero],
  refine congr_arg _ (funext (λ a, _)),
  split_ifs with h; simp [h],
end

lemma coe_bind_on_support_apply (b : β) :
  (p.bind_on_support f b : ℝ≥0∞) = ∑' a, p a * if h : p a = 0 then 0 else f a h b :=
by simp only [bind_on_support_apply, ennreal.coe_tsum (bind_on_support.summable p f b),
    dite_cast, ennreal.coe_mul, ennreal.coe_zero]

lemma bind_on_support_eq_zero_iff (b : β) :
  p.bind_on_support f b = 0 ↔ ∀ a (ha : p a ≠ 0), f a ha b = 0 :=
begin
  simp only [bind_on_support_apply, tsum_eq_zero_iff (bind_on_support.summable p f b),
    mul_eq_zero, or_iff_not_imp_left],
  exact ⟨λ h a ha, trans (dif_neg ha).symm (h a ha), λ h a ha, trans (dif_neg ha) (h a ha)⟩,
end

@[simp] lemma pure_bind_on_support (a : α) (f : Π (a' : α) (ha : a' ∈ (pure a).support), pmf β) :
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
      (λ b hb, g b ((mem_support_bind_on_support_iff f b).mpr ⟨a, ha, hb⟩))) :=
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
