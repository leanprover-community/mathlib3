/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import measure_theory.probability_mass_function.monad

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

`bernoulli` represents the bernoulli distribution on `bool`

-/

namespace pmf

noncomputable theory
variables {α β γ : Type*}
open_locale classical big_operators nnreal ennreal

section map

/-- The functorial action of a function on a `pmf`. -/
def map (f : α → β) (p : pmf α) : pmf β := bind p (pure ∘ f)

variables (f : α → β) (p : pmf α) (b : β)

lemma monad_map_eq_map {α β : Type*} (f : α → β) (p : pmf α) : f <$> p = p.map f := rfl

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

section measure

variable (s : set β)

@[simp] lemma to_outer_measure_map_apply :
  (p.map f).to_outer_measure s = p.to_outer_measure (f ⁻¹' s) :=
by simp [map, set.indicator, to_outer_measure_apply p (f ⁻¹' s)]

@[simp] lemma to_measure_map_apply [measurable_space α] [measurable_space β] (hf : measurable f)
  (hs : measurable_set s) : (p.map f).to_measure s = p.to_measure (f ⁻¹' s) :=
begin
  rw [to_measure_apply_eq_to_outer_measure_apply _ s hs,
    to_measure_apply_eq_to_outer_measure_apply _ (f ⁻¹' s) (measurable_set_preimage hf hs)],
  exact to_outer_measure_map_apply f p s,
end

end measure

end map

section seq

/-- The monadic sequencing operation for `pmf`. -/
def seq (q : pmf (α → β)) (p : pmf α) : pmf β := q.bind (λ m, p.bind $ λ a, pure (m a))

variables (q : pmf (α → β)) (p : pmf α) (b : β)

lemma monad_seq_eq_seq {α β : Type*} (q : pmf (α → β)) (p : pmf α) : q <*> p = q.seq p := rfl

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

instance : is_lawful_functor pmf :=
{ map_const_eq := λ α β, rfl,
  id_map := λ α, bind_pure,
  comp_map := λ α β γ g h x, (map_comp _ _ _).symm }

instance : is_lawful_monad pmf :=
{ bind_pure_comp_eq_map := λ α β f x, rfl,
  bind_map_eq_seq := λ α β f x, rfl,
  pure_bind := λ α β, pure_bind,
  bind_assoc := λ α β γ, bind_bind }

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

section measure

variable (t : set α)

@[simp] lemma to_outer_measure_of_finset_apply :
  (of_finset f s h h').to_outer_measure t = ↑(∑' x, t.indicator f x) :=
to_outer_measure_apply' (of_finset f s h h') t

@[simp] lemma to_measure_of_finset_apply [measurable_space α] (ht : measurable_set t) :
  (of_finset f s h h').to_measure t = ↑(∑' x, t.indicator f x) :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_of_finset_apply h h' t)

end measure

end of_finset

section of_fintype

/-- Given a finite type `α` and a function `f : α → ℝ≥0` with sum 1, we get a `pmf`. -/
def of_fintype [fintype α] (f : α → ℝ≥0) (h : ∑ a, f a = 1) : pmf α :=
of_finset f finset.univ h (λ a ha, absurd (finset.mem_univ a) ha)

variables [fintype α] {f : α → ℝ≥0} (h : ∑ a, f a = 1)

@[simp] lemma of_fintype_apply (a : α) : of_fintype f h a = f a := rfl

@[simp] lemma support_of_fintype : (of_fintype f h).support = function.support f := rfl

lemma mem_support_of_fintype_iff (a : α) : a ∈ (of_fintype f h).support ↔ f a ≠ 0 := iff.rfl

section measure

variable (s : set α)

@[simp] lemma to_outer_measure_of_fintype_apply :
  (of_fintype f h).to_outer_measure s = ↑(∑' x, s.indicator f x) :=
to_outer_measure_apply' (of_fintype f h) s

@[simp] lemma to_measure_of_fintype_apply [measurable_space α] (hs : measurable_set s) :
  (of_fintype f h).to_measure s = ↑(∑' x, s.indicator f x) :=
(to_measure_apply_eq_to_outer_measure_apply _ s hs).trans
  (to_outer_measure_of_fintype_apply h s)

end measure

end of_fintype

section of_multiset

/-- Given a non-empty multiset `s` we construct the `pmf` which sends `a` to the fraction of
  elements in `s` that are `a`. -/
def of_multiset (s : multiset α) (hs : s ≠ 0) : pmf α :=
⟨λ a, s.count a / s.card,
  have ∑ a in s.to_finset, (s.count a : ℝ) / s.card = 1,
  { simp only [div_eq_inv_mul, ← finset.mul_sum, ← nat.cast_sum, multiset.to_finset_sum_count_eq],
    rw [inv_mul_cancel], simp [hs] },
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

section measure

variable (t : set α)

@[simp] lemma to_outer_measure_of_multiset_apply :
  (of_multiset s hs).to_outer_measure t = (∑' x, (s.filter (∈ t)).count x) / s.card :=
begin
  rw [div_eq_mul_inv, ← ennreal.tsum_mul_right, to_outer_measure_apply],
  refine tsum_congr (λ x, _),
  by_cases hx : x ∈ t,
  { have : (multiset.card s : ℝ≥0) ≠ 0 := by simp [hs],
    simp [set.indicator, hx, div_eq_mul_inv, ennreal.coe_inv this] },
  { simp [hx] }
end

@[simp] lemma to_measure_of_multiset_apply [measurable_space α] (ht : measurable_set t) :
  (of_multiset s hs).to_measure t = (∑' x, (s.filter (∈ t)).count x) / s.card :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_of_multiset_apply hs t)

end measure

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

section measure

variable (t : set α)

@[simp] lemma to_outer_measure_uniform_of_finset_apply :
  (uniform_of_finset s hs).to_outer_measure t = (s.filter (∈ t)).card / s.card :=
calc (uniform_of_finset s hs).to_outer_measure t
  = ↑(∑' x, if x ∈ t then (uniform_of_finset s hs x) else 0) :
    to_outer_measure_apply' (uniform_of_finset s hs) t
  ... = ↑(∑' x, if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0)⁻¹ else 0) :
    begin
      refine (ennreal.coe_eq_coe.2 $ tsum_congr (λ x, _)),
      by_cases hxt : x ∈ t,
      { by_cases hxs : x ∈ s; simp [hxt, hxs] },
      { simp [hxt] }
    end
  ... = ↑(∑ x in (s.filter (∈ t)), if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0)⁻¹ else 0) :
    begin
      refine ennreal.coe_eq_coe.2 (tsum_eq_sum (λ x hx, _)),
      have : ¬ (x ∈ s ∧ x ∈ t) := λ h, hx (finset.mem_filter.2 h),
      simp [this]
    end
  ... = ↑(∑ x in (s.filter (∈ t)), (s.card : ℝ≥0)⁻¹) :
    ennreal.coe_eq_coe.2 (finset.sum_congr rfl $
      λ x hx, let this : x ∈ s ∧ x ∈ t := by simpa using hx in by simp [this])
  ... = (s.filter (∈ t)).card / s.card :
    let this : (s.card : ℝ≥0) ≠ 0 := nat.cast_ne_zero.2
      (hs.rec_on $ λ _, finset.card_ne_zero_of_mem) in
    by simp [div_eq_mul_inv, ennreal.coe_inv this]

@[simp] lemma to_measure_uniform_of_finset_apply [measurable_space α] (ht : measurable_set t) :
  (uniform_of_finset s hs).to_measure t = (s.filter (∈ t)).card / s.card :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_uniform_of_finset_apply hs t)

end measure

end uniform_of_finset

section uniform_of_fintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def uniform_of_fintype (α : Type*) [fintype α] [nonempty α] : pmf α :=
  uniform_of_finset (finset.univ) (finset.univ_nonempty)

variables [fintype α] [nonempty α]

@[simp] lemma uniform_of_fintype_apply (a : α) : uniform_of_fintype α a = (fintype.card α)⁻¹ :=
by simpa only [uniform_of_fintype, finset.mem_univ, if_true, uniform_of_finset_apply]

@[simp] lemma support_uniform_of_fintype (α : Type*) [fintype α] [nonempty α] :
  (uniform_of_fintype α).support = ⊤ :=
set.ext (λ x, by simpa [mem_support_iff] using fintype.card_ne_zero)

lemma mem_support_uniform_of_fintype (a : α) : a ∈ (uniform_of_fintype α).support := by simp

section measure

variable (s : set α)

lemma to_outer_measure_uniform_of_fintype_apply :
  (uniform_of_fintype α).to_outer_measure s = fintype.card s / fintype.card α :=
by simpa [uniform_of_fintype]

lemma to_measure_uniform_of_fintype_apply [measurable_space α] (hs : measurable_set s) :
  (uniform_of_fintype α).to_measure s = fintype.card s / fintype.card α :=
by simpa [uniform_of_fintype, hs]

end measure

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

lemma mem_support_filter_iff {a : α} : a ∈ (p.filter s h).support ↔ a ∈ s ∧ a ∈ p.support :=
(mem_support_normalize_iff _ _).trans set.indicator_apply_ne_zero

@[simp] lemma support_filter : (p.filter s h).support = s ∩ p.support:=
set.ext $ λ x, (mem_support_filter_iff _)

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

end pmf
