/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import topology.instances.ennreal
import measure_theory.measure.measure_space

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0` such that the values have (infinite) sum `1`.

This file features the monadic structure of `pmf`,
other constructions of `pmf`s are found in `probability_mass_function/constructions.lean`

Given `p : pmf α`, `pmf.to_outer_measure` constructs an `outer_measure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `measure` on `α`, see `pmf.to_measure`.
`pmf.to_measure.is_probability_measure` shows this associated measure is a probability measure.

## Tags

probability mass function, discrete probability measure
-/
noncomputable theory
variables {α : Type*} {β : Type*} {γ : Type*}
open_locale classical big_operators nnreal ennreal

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0` such that
  the values have (infinite) sum `1`. -/
def {u} pmf (α : Type u) : Type u := { f : α → ℝ≥0 // has_sum f 1 }

namespace pmf

instance : has_coe_to_fun (pmf α) (λ p, α → ℝ≥0) := ⟨λ p a, p.1 a⟩

@[ext] protected lemma ext : ∀ {p q : pmf α}, (∀ a, p a = q a) → p = q
| ⟨f, hf⟩ ⟨g, hg⟩ eq :=  subtype.eq $ funext eq

lemma has_sum_coe_one (p : pmf α) : has_sum p 1 := p.2

lemma summable_coe (p : pmf α) : summable p := (p.has_sum_coe_one).summable

@[simp] lemma tsum_coe (p : pmf α) : ∑' a, p a = 1 := p.has_sum_coe_one.tsum_eq

/-- The support of a `pmf` is the set where it is nonzero. -/
def support (p : pmf α) : set α := function.support p

@[simp] lemma mem_support_iff (p : pmf α) (a : α) :
  a ∈ p.support ↔ p a ≠ 0 := iff.rfl

lemma apply_eq_zero_iff (p : pmf α) (a : α) :
  p a = 0 ↔ a ∉ p.support :=
by rw [mem_support_iff, not_not]

lemma coe_le_one (p : pmf α) (a : α) : p a ≤ 1 :=
has_sum_le (by { intro b, split_ifs; simp only [h, zero_le'] })
  (has_sum_ite_eq a (p a)) (has_sum_coe_one p)

section pure

/-- The pure `pmf` is the `pmf` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
def pure (a : α) : pmf α := ⟨λ a', if a' = a then 1 else 0, has_sum_ite_eq _ _⟩

@[simp] lemma pure_apply (a a' : α) : pure a a' = (if a' = a then 1 else 0) := rfl

lemma mem_support_pure_iff (a a' : α) : a' ∈ (pure a).support ↔ a' = a :=
by simp

instance [inhabited α] : inhabited (pmf α) := ⟨pure (default α)⟩

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

@[simp] lemma bind_apply (p : pmf α) (f : α → pmf β) (b : β) : p.bind f b = ∑'a, p a * f a b :=
rfl

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

end bind

instance : monad pmf :=
{ pure := λ A a, pure a,
  bind := λ A B pa pb, pa.bind pb }

section outer_measure

open measure_theory measure_theory.outer_measure

/-- Construct an `outer_measure` from a `pmf`, by assigning measure to each set `s : set α` equal
  to the sum of `p x` for for each `x ∈ α` -/
def to_outer_measure (p : pmf α) : outer_measure α :=
outer_measure.sum (λ (x : α), p x • dirac x)

variables (p : pmf α) (s t : set α)

lemma to_outer_measure_apply : p.to_outer_measure s = ∑' x, s.indicator (λ x, (p x : ℝ≥0∞)) x :=
tsum_congr (λ x, smul_dirac_apply (p x) x s)

lemma to_outer_measure_apply' : p.to_outer_measure s = ↑(∑' (x : α), s.indicator p x) :=
by simp only [ennreal.coe_tsum (nnreal.indicator_summable (summable_coe p) s),
  ennreal.coe_indicator, to_outer_measure_apply]

@[simp]
lemma to_outer_measure_apply_finset (s : finset α) :
  p.to_outer_measure s = ∑ x in s, (p x : ℝ≥0∞) :=
begin
  refine (to_outer_measure_apply p s).trans ((@tsum_eq_sum _ _ _ _ _ _ s _).trans _),
  { exact λ x hx, set.indicator_of_not_mem hx _ },
  { exact finset.sum_congr rfl (λ x hx, set.indicator_of_mem hx _) }
end

@[simp]
lemma to_outer_measure_apply_fintype [fintype α] (s : set α) :
  p.to_outer_measure s = ∑ x, (s.indicator (λ x, (p x : ℝ≥0∞)) x) :=
(p.to_outer_measure_apply s).trans (tsum_eq_sum (λ x h, absurd (finset.mem_univ x) h))

lemma to_outer_measure_apply_eq_zero_iff : p.to_outer_measure s = 0 ↔ disjoint p.support s :=
begin
  rw [to_outer_measure_apply', ennreal.coe_eq_zero,
    tsum_eq_zero_iff (nnreal.indicator_summable (summable_coe p) s)],
  exact function.funext_iff.symm.trans set.indicator_eq_zero',
end

lemma to_outer_measure_apply_eq_one_iff : p.to_outer_measure s = 1 ↔ p.support ⊆ s :=
begin
  rw [to_outer_measure_apply', ennreal.coe_eq_one],
  refine ⟨λ h a ha, _, λ h, _⟩,
  { by_contradiction has,
    refine (ne_of_lt $ lt_of_lt_of_le _ (le_of_eq p.tsum_coe)) h,
    have : s.indicator p a < p a,
    by simpa [set.indicator_apply, has] using lt_of_le_of_ne zero_le' (ne.symm ha),
    exact nnreal.tsum_lt_tsum (λ a, set.indicator_apply_le (λ _, le_rfl)) this p.summable_coe },
  { refine trans (tsum_congr $ λ a, _) (p.tsum_coe),
    rw [set.indicator_apply, ite_eq_left_iff],
    exact λ ha, ((p.apply_eq_zero_iff a).2 $ set.not_mem_subset h ha).symm }
end

lemma to_outer_measure_apply_eq_of_inter_support_eq {s t : set α}
  (h : s ∩ p.support = t ∩ p.support) : p.to_outer_measure s = p.to_outer_measure t :=
begin
  rw [to_outer_measure_apply' p, to_outer_measure_apply' p, ennreal.coe_eq_coe],
  refine tsum_congr (λ a, _),
  simp_rw [set.indicator_apply],
  split_ifs with has hat hat,
  { exact rfl },
  { rw apply_eq_zero_iff,
    refine λ ha, hat (set.mem_of_mem_inter_left (h ▸ ⟨has, ha⟩ : a ∈ t ∩ p.support)) },
  { rw [eq_comm, apply_eq_zero_iff],
    refine λ ha, has (set.mem_of_mem_inter_left (h.symm ▸ ⟨hat, ha⟩ : a ∈ s ∩ p.support)) },
  { exact rfl }
end

lemma to_outer_measure_apply_inter_support :
  p.to_outer_measure (s ∩ p.support) = p.to_outer_measure s :=
to_outer_measure_apply_eq_of_inter_support_eq p (by rw [set.inter_assoc, set.inter_self])

@[simp]
lemma to_outer_measure_caratheodory : (to_outer_measure p).caratheodory = ⊤ :=
begin
  refine (eq_top_iff.2 $ le_trans (le_Inf $ λ x hx, _) (le_sum_caratheodory _)),
  obtain ⟨y, hy⟩ := hx,
  exact ((le_of_eq (dirac_caratheodory y).symm).trans
    (le_smul_caratheodory _ _)).trans (le_of_eq hy),
end

end outer_measure

section measure

open measure_theory

/-- Since every set is Carathéodory-measurable under `pmf.to_outer_measure`,
  we can further extend this `outer_measure` to a `measure` on `α` -/
def to_measure [measurable_space α] (p : pmf α) : measure α :=
p.to_outer_measure.to_measure ((to_outer_measure_caratheodory p).symm ▸ le_top)

variables [measurable_space α] (p : pmf α) (s t : set α)

lemma to_measure_apply_eq_to_outer_measure_apply (hs : measurable_set s) :
  p.to_measure s = p.to_outer_measure s :=
to_measure_apply p.to_outer_measure _ hs

lemma to_outer_measure_apply_le_to_measure_apply :
  p.to_outer_measure s ≤ p.to_measure s :=
le_to_measure_apply p.to_outer_measure _ s

lemma to_measure_apply (hs : measurable_set s) :
  p.to_measure s = ∑' x, s.indicator (λ x, (p x : ℝ≥0∞)) x :=
(p.to_measure_apply_eq_to_outer_measure_apply s hs).trans (p.to_outer_measure_apply s)

lemma to_measure_apply' (hs : measurable_set s) :
  p.to_measure s = ↑(∑' x, s.indicator p x) :=
(p.to_measure_apply_eq_to_outer_measure_apply s hs).trans (p.to_outer_measure_apply' s)

@[simp]
lemma to_measure_apply_finset [measurable_singleton_class α] (s : finset α) :
  p.to_measure s = ∑ x in s, (p x : ℝ≥0∞) :=
(p.to_measure_apply_eq_to_outer_measure_apply s s.measurable_set).trans
  (p.to_outer_measure_apply_finset s)

lemma to_measure_apply_of_finite [measurable_singleton_class α] (s : set α) (hs : s.finite) :
  p.to_measure s = ∑' x, s.indicator (λ x, (p x : ℝ≥0∞)) x :=
(p.to_measure_apply_eq_to_outer_measure_apply s hs.measurable_set).trans
  (p.to_outer_measure_apply s)

@[simp]
lemma to_measure_apply_fintype [measurable_singleton_class α] [fintype α] (p : pmf α) (s : set α) :
  p.to_measure s = ∑ x, s.indicator (λ x, (p x : ℝ≥0∞)) x :=
(p.to_measure_apply_eq_to_outer_measure_apply s (set.finite.of_fintype s).measurable_set).trans
  (p.to_outer_measure_apply_fintype s)

lemma to_measure_apply_eq_zero_iff (hs : measurable_set s) :
  p.to_measure s = 0 ↔ disjoint p.support s :=
by rw [to_measure_apply_eq_to_outer_measure_apply p s hs, to_outer_measure_apply_eq_zero_iff p s]

lemma to_measure_apply_eq_one_iff (hs : measurable_set s) :
  p.to_measure s = 1 ↔ p.support ⊆ s :=
by rw [to_measure_apply_eq_to_outer_measure_apply p s hs, to_outer_measure_apply_eq_one_iff p s]

lemma to_measure_apply_eq_of_inter_eq {s t : set α} (hs : measurable_set s) (ht : measurable_set t)
  (hst : s ∩ p.support = t ∩ p.support) : p.to_measure s = p.to_measure t :=
by simpa only [to_measure_apply_eq_to_outer_measure_apply p s hs,
  to_measure_apply_eq_to_outer_measure_apply p t ht] using
    to_outer_measure_apply_eq_of_inter_support_eq p hst

lemma to_measure_apply_inter_support (hs : measurable_set s) (hp : measurable_set p.support) :
  p.to_measure (s ∩ p.support) = p.to_measure s :=
to_measure_apply_eq_of_inter_eq p (hs.inter hp) hs (by rw [set.inter_assoc, set.inter_self])

/-- The measure associated to a `pmf` by `to_measure` is a probability measure -/
instance to_measure.is_probability_measure (p : pmf α) : is_probability_measure (p.to_measure) :=
⟨by simpa only [measurable_set.univ, to_measure_apply_eq_to_outer_measure_apply, set.indicator_univ,
  to_outer_measure_apply', ennreal.coe_eq_one] using tsum_coe p⟩

end measure

-- TODO: Move bind and pure definitions down here after defining measures
section to_fix

variables {A B : Type*}

lemma to_outer_measure_pure_apply (a : A) (s : set A) :
  (pure a).to_outer_measure s = if a ∈ s then 1 else 0 :=
begin
  refine (to_outer_measure_apply' (pure a) s).trans _,
  split_ifs with ha ha,
  { refine ennreal.coe_eq_one.2 ((tsum_congr (λ b, _)).trans (tsum_ite_eq a 1)),
    exact ite_eq_left_iff.2 (λ hb, symm (ite_eq_right_iff.2 (λ h, (hb $ h.symm ▸ ha).elim))) },
  { refine ennreal.coe_eq_zero.2 ((tsum_congr (λ b, _)).trans (tsum_zero)),
    exact ite_eq_right_iff.2 (λ hb, ite_eq_right_iff.2 (λ h, (ha $ h ▸ hb).elim)) }
end

lemma to_measure_pure_apply [measurable_space A] (a : A) (s : set A) (hs : measurable_set s) :
  (pure a).to_measure s = if a ∈ s then 1 else 0 :=
(to_measure_apply_eq_to_outer_measure_apply (pure a) s hs).trans (to_outer_measure_pure_apply a s)

lemma to_outer_measure_bind_apply (pa : pmf A) (pb : A → pmf B) (s : set B) :
  (pa.bind pb).to_outer_measure s = ∑' (a : A), pa a * (pb a).to_outer_measure s :=
calc (pa.bind pb).to_outer_measure s
      = ∑' (b : B), if b ∈ s then ↑(∑' (a : A), pa a * pb a b) else 0
    : by simp [to_outer_measure_apply, set.indicator_apply]
  ... = ∑' (b : B), ↑(∑' (a : A), pa a * (if b ∈ s then pb a b else 0))
    : tsum_congr (λ b, by split_ifs; simp)
  ... = ∑' (b : B) (a : A), ↑(pa a * (if b ∈ s then pb a b else 0))
    : tsum_congr (λ b, ennreal.coe_tsum $
        nnreal.summable_of_le (by split_ifs; simp) (bind.summable pa pb b))
  ... = ∑' (a : A) (b : B), ↑(pa a) * ↑(if b ∈ s then pb a b else 0)
    : ennreal.tsum_comm.trans (tsum_congr $ λ a, tsum_congr $ λ b, ennreal.coe_mul)
  ... = ∑' (a : A), ↑(pa a) * ∑' (b : B), ↑(if b ∈ s then pb a b else 0)
    : tsum_congr (λ a, ennreal.tsum_mul_left)
  ... = ∑' (a : A), ↑(pa a) * ∑' (b : B), if b ∈ s then ↑(pb a b) else (0 : ℝ≥0∞)
    : tsum_congr (λ a, congr_arg (λ x, ↑(pa a) * x) $ tsum_congr (λ b, by split_ifs; refl))
  ... = ∑' (a : A), ↑(pa a) * (pb a).to_outer_measure s
    : tsum_congr (λ a, by rw [to_outer_measure_apply, set.indicator])

lemma to_measure_bind_apply [measurable_space B] (pa : pmf A) (pb : A → pmf B) (s : set B) (hs : measurable_set s) :
  (pa.bind pb).to_measure s = ∑' (a : A), pa a * (pb a).to_measure s :=
(to_measure_apply_eq_to_outer_measure_apply (pa.bind pb) s hs).trans
  ((to_outer_measure_bind_apply pa pb s).trans (tsum_congr (λ a, congr_arg (λ x, pa a * x)
  (to_measure_apply_eq_to_outer_measure_apply (pb a) s hs).symm)))

end to_fix

end pmf
