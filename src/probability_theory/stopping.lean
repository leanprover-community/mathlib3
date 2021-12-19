/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.constructions.borel_space
import measure_theory.function.l1_space

/-!
# Filtration and stopping time

This file defines some standard definition from the theory of stochastic processes including
filtrations and stopping times. These definitions are used to model the amount of information
at a specific time and is the first step in formalizing stochastic processes.

## Main definitions

* `measure_theory.filtration`: a filtration on a measurable space
* `measure_theory.adapted`: a sequence of functions `u` is said to be adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-measurable
* `measure_theory.filtration.natural`: the natural filtration with respect to a sequence of
  measurable functions is the smallest filtration to which it is adapted to
* `measure_theory.stopping_time`: a stopping time with respect to some filtration `f` is a
  function `τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is
  `f i`-measurable
* `measure_theory.stopping_time.measurable_space`: the σ-algebra associated with a stopping time

## Tags

filtration, stopping time, stochastic process

-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal topological_space big_operators

namespace measure_theory

/-- A `filtration` on measurable space `α` with σ-algebra `m` is a monotone
sequence of of sub-σ-algebras of `m`. -/
structure filtration {α : Type*} (ι : Type*) [preorder ι] (m : measurable_space α) :=
(seq : ι → measurable_space α)
(mono : monotone seq)
(le : ∀ i : ι, seq i ≤ m)

variables {α β ι : Type*} {m : measurable_space α}

open topological_space

section preorder

variables [preorder ι]

instance : has_coe_to_fun (filtration ι m) (λ _, ι → measurable_space α) :=
⟨λ f, f.seq⟩

/-- The constant filtration which is equal to `m` for all `i : ι`. -/
def const_filtration (m : measurable_space α) : filtration ι m :=
⟨λ _, m, monotone_const, λ _, le_rfl⟩

instance : inhabited (filtration ι m) :=
⟨const_filtration m⟩

lemma measurable_set_of_filtration {f : filtration ι m} {s : set α} {i : ι}
  (hs : measurable_set[f i] s) : measurable_set[m] s :=
f.le i s hs

/-- A measure is σ-finite with respect to filtration if it is σ-finite with respect
to all the sub-σ-algebra of the filtration. -/
class sigma_finite_filtration (μ : measure α) (f : filtration ι m) : Prop :=
(sigma_finite : ∀ i : ι, sigma_finite (μ.trim (f.le i)))

instance sigma_finite_of_sigma_finite_filtration (μ : measure α) (f : filtration ι m)
  [hf : sigma_finite_filtration μ f] (i : ι) :
  sigma_finite (μ.trim (f.le i)) :=
by apply hf.sigma_finite -- can't exact here

variable [measurable_space β]

/-- A sequence of functions `u` is adapted to a filtration `f` if for all `i`,
`u i` is `f i`-measurable. -/
def adapted (f : filtration ι m) (u : ι → α → β) : Prop :=
∀ i : ι, measurable[f i] (u i)

namespace adapted

lemma add [has_add β] [has_measurable_add₂ β] {u v : ι → α → β} {f : filtration ι m}
  (hu : adapted f u) (hv : adapted f v) : adapted f (u + v):=
λ i, @measurable.add _ _ _ _ (f i) _ _ _ (hu i) (hv i)

lemma neg [has_neg β] [has_measurable_neg β] {u : ι → α → β} {f : filtration ι m}
  (hu : adapted f u) : adapted f (-u) :=
λ i, @measurable.neg _ α _ _ _ (f i) _ (hu i)

lemma smul [has_scalar ℝ β] [has_measurable_smul ℝ β] {u : ι → α → β} {f : filtration ι m}
  (c : ℝ) (hu : adapted f u) : adapted f (c • u) :=
λ i, @measurable.const_smul ℝ β α _ _ _ (f i) _ _ (hu i) c

end adapted

variable (β)

lemma adapted_zero [has_zero β] (f : filtration ι m) : adapted f (0 : ι → α → β) :=
λ i, @measurable_zero β α _ (f i) _

variable {β}

namespace filtration

/-- Given a sequence of functions, the natural filtration is the smallest sequence
of σ-algebras such that that sequence of functions is measurable with respect to
the filtration. -/
def natural (u : ι → α → β) (hum : ∀ i, measurable (u i)) : filtration ι m :=
{ seq := λ i, ⨆ j ≤ i, measurable_space.comap (u j) infer_instance,
  mono := λ i j hij, bsupr_le_bsupr' $ λ k hk, le_trans hk hij,
  le := λ i, bsupr_le (λ j hj s hs, let ⟨t, ht, ht'⟩ := hs in ht' ▸ hum j ht) }

lemma adapted_natural {u : ι → α → β} (hum : ∀ i, measurable[m] (u i)) :
  adapted (natural u hum) u :=
λ i, measurable.le (le_bsupr_of_le i (le_refl i) (le_refl _)) (λ s hs, ⟨s, hs, rfl⟩)

end filtration

variables {μ : measure α} {f : filtration ι m}

/-- A stopping time with respect to some filtration `f` is a function
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at time
`i`, we may determine it with the information we have at time `i`. -/
def is_stopping_time (f : filtration ι m) (τ : α → ι) :=
∀ i : ι, measurable_set[f i] $ {x | τ x ≤ i}

lemma is_stopping_time.measurable_set_eq
  {f : filtration ℕ m} {τ : α → ℕ} (hτ : is_stopping_time f τ) (i : ℕ) :
  measurable_set[f i] $ {x | τ x = i} :=
begin
  cases i,
  { convert (hτ 0),
    simp only [set.set_of_eq_eq_singleton, le_zero_iff] },
  { rw (_ : {x | τ x = i + 1} = {x | τ x ≤ i + 1} \ {x | τ x ≤ i}),
    { exact @measurable_set.diff _ (f (i + 1)) _ _ (hτ (i + 1))
        (f.mono (nat.le_succ _) _ (hτ i)) },
    { ext, simp only [set.mem_diff, not_le, set.mem_set_of_eq],
      split,
      { intro h, simp [h] },
      { rintro ⟨h₁, h₂⟩,
        linarith } } }
end

lemma is_stopping_time.measurable_set_eq_le
  {f : filtration ℕ m} {τ : α → ℕ} (hτ : is_stopping_time f τ) {i j : ℕ} (hle : i ≤ j) :
  measurable_set[f j] $ {x | τ x = i} :=
f.mono hle _ $ hτ.measurable_set_eq i

lemma is_stopping_time_of_measurable_set_eq
  {f : filtration ℕ m} {τ : α → ℕ} (hτ : ∀ i, measurable_set[f i] $ {x | τ x = i}) :
  is_stopping_time f τ :=
begin
  intro i,
  rw show {x | τ x ≤ i} = ⋃ k ≤ i, {x | τ x = k}, by { ext, simp },
  refine @measurable_set.bUnion _ _ (f i) _ _ (set.countable_encodable _) (λ k hk, _),
  exact f.mono hk _ (hτ k),
end

lemma is_stopping_time_const {f : filtration ι m} (i : ι) :
  is_stopping_time f (λ x, i) :=
λ j, by simp

end preorder

namespace is_stopping_time

lemma max [linear_order ι] {f : filtration ι m} {τ π : α → ι}
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  is_stopping_time f (λ x, max (τ x) (π x)) :=
begin
  intro i,
  simp_rw [max_le_iff, set.set_of_and],
  exact @measurable_set.inter _ (f i) _ _ (hτ i) (hπ i),
end

lemma min [linear_order ι] {f : filtration ι m} {τ π : α → ι}
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  is_stopping_time f (λ x, min (τ x) (π x)) :=
begin
  intro i,
  simp_rw [min_le_iff, set.set_of_or],
  exact @measurable_set.union _ (f i) _ _ (hτ i) (hπ i),
end

lemma add_const
  [add_group ι] [preorder ι] [covariant_class ι ι (function.swap (+)) (≤)]
  [covariant_class ι ι (+) (≤)]
  {f : filtration ι m} {τ : α → ι} (hτ : is_stopping_time f τ) {i : ι} (hi : 0 ≤ i) :
  is_stopping_time f (λ x, τ x + i) :=
begin
  intro j,
  simp_rw [← le_sub_iff_add_le],
  exact f.mono (sub_le_self j hi) _ (hτ (j - i)),
end

section preorder

variables [preorder ι] {f : filtration ι m}

/-- The associated σ-algebra with a stopping time. -/
protected def measurable_space
  {τ : α → ι} (hτ : is_stopping_time f τ) : measurable_space α :=
{ measurable_set' := λ s, ∀ i : ι, measurable_set[f i] (s ∩ {x | τ x ≤ i}),
  measurable_set_empty :=
    λ i, (set.empty_inter {x | τ x ≤ i}).symm ▸ @measurable_set.empty _ (f i),
  measurable_set_compl := λ s hs i,
    begin
      rw (_ : sᶜ ∩ {x | τ x ≤ i} = (sᶜ ∪ {x | τ x ≤ i}ᶜ) ∩ {x | τ x ≤ i}),
      { refine @measurable_set.inter _ (f i) _ _ _ _,
        { rw ← set.compl_inter,
          exact @measurable_set.compl _ _ (f i) (hs i) },
        { exact hτ i} },
      { rw set.union_inter_distrib_right,
        simp only [set.compl_inter_self, set.union_empty] }
    end,
  measurable_set_Union := λ s hs i,
    begin
      rw forall_swap at hs,
      rw set.Union_inter,
      exact @measurable_set.Union _ _ (f i) _ _ (hs i),
    end }

@[protected]
lemma measurable_set {τ : α → ι} (hτ : is_stopping_time f τ) (s : set α) :
  measurable_set[hτ.measurable_space] s ↔
  ∀ i : ι, measurable_set[f i] (s ∩ {x | τ x ≤ i}) :=
iff.rfl

lemma measurable_space_mono
  {τ π : α → ι} (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) (hle : τ ≤ π) :
  hτ.measurable_space ≤ hπ.measurable_space :=
begin
  intros s hs i,
  rw (_ : s ∩ {x | π x ≤ i} = s ∩ {x | τ x ≤ i} ∩ {x | π x ≤ i}),
  { exact @measurable_set.inter _ (f i) _ _ (hs i) (hπ i) },
  { ext,
    simp only [set.mem_inter_eq, iff_self_and, and.congr_left_iff, set.mem_set_of_eq],
    intros hle' _,
    exact le_trans (hle _) hle' },
end

lemma measurable_space_le [encodable ι] {τ : α → ι} (hτ : is_stopping_time f τ) :
  hτ.measurable_space ≤ m :=
begin
  intros s hs,
  change ∀ i, measurable_set[f i] (s ∩ {x | τ x ≤ i}) at hs,
  rw (_ : s = ⋃ i, s ∩ {x | τ x ≤ i}),
  { exact measurable_set.Union (λ i, f.le i _ (hs i)) },
  { ext x, split; rw set.mem_Union,
    { exact λ hx, ⟨τ x, hx, le_refl _⟩ },
    { rintro ⟨_, hx, _⟩,
      exact hx } }
end

section nat

lemma measurable_set_eq_const {f : filtration ℕ m}
  {τ : α → ℕ} (hτ : is_stopping_time f τ) (i : ℕ) :
  measurable_set[hτ.measurable_space] {x | τ x = i} :=
begin
  rw hτ.measurable_set,
  intro j,
  by_cases i ≤ j,
  { rw (_ : {x | τ x = i} ∩ {x | τ x ≤ j} = {x | τ x = i}),
    { exact hτ.measurable_set_eq_le h },
    { ext,
      simp only [set.mem_inter_eq, and_iff_left_iff_imp, set.mem_set_of_eq],
      rintro rfl,
      assumption } },
  { rw (_ : {x | τ x = i} ∩ {x | τ x ≤ j} = ∅),
    { exact @measurable_set.empty _ (f j) },
    { ext,
      simp only [set.mem_empty_eq, set.mem_inter_eq, not_and, not_le, set.mem_set_of_eq, iff_false],
      rintro rfl,
      rwa not_le at h } }
end

end nat

end preorder

section linear_order

variable [linear_order ι]

lemma measurable [topological_space ι] [measurable_space ι]
  [borel_space ι] [order_topology ι] [second_countable_topology ι]
  {f : filtration ι m} {τ : α → ι} (hτ : is_stopping_time f τ) :
  measurable[hτ.measurable_space] τ :=
begin
  refine @measurable_of_Iic ι α _ _ _ hτ.measurable_space _ _ _ _ _,
  simp_rw [hτ.measurable_set, set.preimage, set.mem_Iic],
  intros i j,
  rw (_ : {x | τ x ≤ i} ∩ {x | τ x ≤ j} = {x | τ x ≤ linear_order.min i j}),
  { exact f.mono (min_le_right i j) _ (hτ (linear_order.min i j)) },
  { ext,
    simp only [set.mem_inter_eq, iff_self, le_min_iff, set.mem_set_of_eq] }
end

end linear_order

end is_stopping_time

section linear_order

/-- Given a map `u : ι → α → E`, the stopped process with respect to `τ` is `u i x` if
`i < τ x`, and `u (τ x) x` otherwise.

Intuitively, the stopped process stop evolving once the stopping time has occured. -/
def stopped_process [linear_order ι] (u : ι → α → β) (τ : α → ι) : ι → α → β :=
λ i x, u (linear_order.min i (τ x)) x

/-- Given a map `u : ι → α → E`, its stopped value with respect to the stopping
time `τ` is the map `x ↦ u (τ x) x`. -/
def stopped_value (u : ι → α → β) (τ : α → ι) : α → β :=
λ x, u (τ x) x

variable [linear_order ι]

-- We will need cadlag to generalize the following to continuous processes
section nat

open filtration

variables [hβ : add_comm_monoid β] {f : filtration ℕ m} {u : ℕ → α → β} {τ : α → ℕ}

include hβ

lemma stopped_process_eq (n : ℕ) :
  stopped_process u τ n =
  set.indicator (λ a, n ≤ τ a) (u n) +
    ∑ i in finset.range n, set.indicator (λ a, i = τ a) (u i) :=
begin
  ext x,
  rw [pi.add_apply, finset.sum_apply],
  by_cases h : τ x < n,
  { simp only [stopped_process, min_eq_right (le_of_lt h)],
    rw finset.sum_eq_single_of_mem (τ x),
    { rw [set.indicator_of_not_mem, zero_add, set.indicator_of_mem],
      { exact rfl }, -- refl does not work
      { exact not_le.2 h } },
    { rwa [finset.mem_range] },
    { intros b hb hneq,
      rw set.indicator_of_not_mem,
      exact hneq } },
  { rw not_lt at h,
    simp only [stopped_process, min_eq_left h],
    rw [set.indicator_of_mem, finset.sum_eq_zero, add_zero],
    { intros m hm,
      rw finset.mem_range at hm,
      exact set.indicator_of_not_mem ((lt_of_lt_of_le hm h).ne) _ },
    { exact h } }
end

lemma adapted.stopped_process_adapted
  [measurable_space β] [has_measurable_add₂ β]
  (hu : adapted f u) (hτ : is_stopping_time f τ) :
  adapted f (stopped_process u τ) :=
begin
  intro i,
  rw stopped_process_eq,
  refine @measurable.add _ _ _ _ (f i) _ _ _ _ _,
  { refine @measurable.indicator _ _ (f i) _ _ _ _ (hu i) _,
    convert @measurable_set.union _ (f i) _ _
      (@measurable_set.compl _ _ (f i) (hτ i)) (hτ.measurable_set_eq i),
    ext x,
    change i ≤ τ x ↔ ¬ τ x ≤ i ∨ τ x = i,
    rw [not_le, le_iff_lt_or_eq, eq_comm] },
  { refine @finset.measurable_sum' _ _ _ _ _ _ (f i) _ _ _,
    refine λ j hij, @measurable.indicator _ _ (f i) _ _ _ _ _ _,
    { rw finset.mem_range at hij,
      exact measurable.le (f.mono hij.le) (hu j) },
    { rw finset.mem_range at hij,
      refine f.mono hij.le _ _,
      convert hτ.measurable_set_eq j,
      simpa only [eq_comm] } }
end

section

omit hβ

lemma stopped_process_has_finite_integral
  [measurable_space β] [normed_group β] [borel_space β]
  {μ : measure α} (hτ : is_stopping_time f τ)
  (hu₁ : adapted f u) (hu₂ : ∀ n, has_finite_integral (u n) μ) (n : ℕ) :
  has_finite_integral (stopped_process u τ n) μ :=
begin
  rw [has_finite_integral, stopped_process_eq],
  have : ∀ x, (∥(set.indicator {x | n ≤ τ x} (u n) +
    ∑ i in finset.range n, set.indicator {x | i = τ x} (u i)) x∥₊ : ℝ≥0∞) ≤
    ∥set.indicator (λ a, n ≤ τ a) (u n) x∥₊ +
    ∑ i in finset.range n, ∥set.indicator {x | i = τ x} (u i) x∥₊,
  { intro x,
    rw [pi.add_apply, finset.sum_apply, ← ennreal.coe_of_nnreal_hom,
        ← ennreal.of_nnreal_hom.map_sum, ← ring_hom.map_add, ennreal.coe_of_nnreal_hom,
        ennreal.coe_le_coe],
    exact le_trans (nnnorm_add_le _ _) (add_le_add_left (nnnorm_sum_le _ _) _) },
  refine lt_of_le_of_lt (lintegral_mono this) _,
  rw [lintegral_add],
  { rw ennreal.add_lt_top,
    refine ⟨lt_of_le_of_lt (lintegral_mono _) (hu₂ n), _⟩,
    { intro x,
      by_cases hx : x ∈ {x | n ≤ τ x},
      { simp only [ennreal.coe_le_coe],
        erw [set.indicator_of_mem hx] },
      { simp only [ennreal.coe_le_coe],
        erw [set.indicator_of_not_mem hx],
        simp only [nnnorm_zero, zero_le'] } },
    { rw lintegral_finset_sum,
      { refine ennreal.sum_lt_top (λ i hi, (lt_of_le_of_lt (lintegral_mono _) (hu₂ i)).ne),
        intro x,
        by_cases hx : x ∈ {x | i = τ x},
        { simp only [ennreal.coe_le_coe],
          erw [set.indicator_of_mem hx] },
        { simp only [ennreal.coe_le_coe],
          erw [set.indicator_of_not_mem hx],
          simp only [nnnorm_zero, zero_le'] } },
      { intros i hi,
        refine (measurable.indicator ((hu₁ i).le (f.le _)) _).nnnorm.coe_nnreal_ennreal,
        convert f.le _ _ (hτ.measurable_set_eq i),
        simp [eq_comm] } } },
  { refine (measurable_nnnorm.comp (((hu₁ n).le (f.le _)).indicator _)).coe_nnreal_ennreal,
    erw [← measurable_set.compl_iff, set.compl_set_of],
    simp_rw not_le,
    rw (by { ext x, simp [lt_iff_le_and_ne] } : {x | τ x < n} = {x | τ x ≤ n} \ {x | τ x = n}),
    exact measurable_set.diff (f.le _ _ (hτ n)) (f.le _ _ (hτ.measurable_set_eq n)) },
  { refine (finset.range n).measurable_sum
      (λ n h, (measurable.indicator ((hu₁ n).le (f.le _))
        (f.le n _ _)).nnnorm.coe_nnreal_ennreal),
    convert hτ.measurable_set_eq n,
    simp [eq_comm] }
end

lemma stopped_process_measurable [measurable_space β] [normed_group β] [has_measurable_add₂ β]
  (hτ : is_stopping_time f τ) (hu₁ : adapted f u) (n : ℕ) :
  measurable (stopped_process u τ n) :=
(hu₁.stopped_process_adapted hτ n).le (f.le _)

lemma stopped_process_integrable
  [measurable_space β] [normed_group β] [borel_space β] [has_measurable_add₂ β]
  {μ : measure α} (hτ : is_stopping_time f τ)
  (hu₁ : adapted f u) (hu₂ : ∀ n, has_finite_integral (u n) μ) (n : ℕ) :
  integrable (stopped_process u τ n) μ :=
⟨(stopped_process_measurable hτ hu₁ n).ae_measurable,
    stopped_process_has_finite_integral hτ hu₁ hu₂ n⟩

end

end nat

end linear_order

end measure_theory
