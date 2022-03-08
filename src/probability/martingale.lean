/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import probability.notation
import probability.stopping

/-!
# Martingales

A family of functions `f : ι → α → E` is a martingale with respect to a filtration `ℱ` if every
`f i` is integrable, `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] =ᵐ[μ] f i`. On the other hand, `f : ι → α → E` is said to be a supermartingale
with respect to the filtration `ℱ` if `f i` is integrable, `f` is adapted with resepct to `ℱ`
and for all `i ≤ j`, `μ[f j | ℱ.le i] ≤ᵐ[μ] f i`. Finally, `f : ι → α → E` is said to be a
submartingale with respect to the filtration `ℱ` if `f i` is integrable, `f` is adapted with
resepct to `ℱ` and for all `i ≤ j`, `f i ≤ᵐ[μ] μ[f j | ℱ.le i]`.

The definitions of filtration and adapted can be found in `probability.stopping`.

### Definitions

* `measure_theory.martingale f ℱ μ`: `f` is a martingale with respect to filtration `ℱ` and
  measure `μ`.
* `measure_theory.supermartingale f ℱ μ`: `f` is a supermartingale with respect to
  filtration `ℱ` and measure `μ`.
* `measure_theory.submartingale f ℱ μ`: `f` is a submartingale with respect to filtration `ℱ` and
  measure `μ`.

### Results

* `measure_theory.martingale_condexp f ℱ μ`: the sequence `λ i, μ[f | ℱ i, ℱ.le i])` is a
  martingale with respect to `ℱ` and `μ`.

-/

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators

namespace measure_theory

variables {α E ι : Type*} [preorder ι] [measurable_space E]
  {m0 : measurable_space α} {μ : measure α}
  [normed_group E] [normed_space ℝ E] [complete_space E] [borel_space E]
  [second_countable_topology E]
  {f g : ι → α → E} {ℱ : filtration ι m0} [sigma_finite_filtration μ ℱ]

/-- A family of functions `f : ι → α → E` is a martingale with respect to a filtration `ℱ` if `f`
is adapted with respect to `ℱ` and for all `i ≤ j`, `μ[f j | ℱ.le i] =ᵐ[μ] f i`. -/
def martingale (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] : Prop :=
adapted ℱ f ∧ ∀ i j, i ≤ j → μ[f j | ℱ i, ℱ.le i] =ᵐ[μ] f i

/-- A family of integrable functions `f : ι → α → E` is a supermartingale with respect to a
filtration `ℱ` if `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] ≤ᵐ[μ] f i`. -/
def supermartingale [has_le E] (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] : Prop :=
adapted ℱ f ∧ (∀ i j, i ≤ j → μ[f j | ℱ i, ℱ.le i] ≤ᵐ[μ] f i) ∧ ∀ i, integrable (f i) μ

/-- A family of integrable functions `f : ι → α → E` is a submartingale with respect to a
filtration `ℱ` if `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`f i ≤ᵐ[μ] μ[f j | ℱ.le i]`. -/
def submartingale [has_le E] (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] : Prop :=
adapted ℱ f ∧ (∀ i j, i ≤ j → f i ≤ᵐ[μ] μ[f j | ℱ i, ℱ.le i]) ∧ ∀ i, integrable (f i) μ

variables (E)
lemma martingale_zero (ℱ : filtration ι m0) (μ : measure α) [sigma_finite_filtration μ ℱ] :
  martingale (0 : ι → α → E) ℱ μ :=
⟨adapted_zero E ℱ, λ i j hij, by { rw [pi.zero_apply, condexp_zero], simp, }⟩
variables {E}

namespace martingale

@[protected]
lemma adapted (hf : martingale f ℱ μ) : adapted ℱ f := hf.1

@[protected]
lemma measurable (hf : martingale f ℱ μ) (i : ι) : measurable[ℱ i] (f i) := hf.adapted i

lemma condexp_ae_eq (hf : martingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  μ[f j | ℱ i, ℱ.le i] =ᵐ[μ] f i :=
hf.2 i j hij

@[protected]
lemma integrable (hf : martingale f ℱ μ) (i : ι) : integrable (f i) μ :=
integrable_condexp.congr (hf.condexp_ae_eq (le_refl i))

lemma set_integral_eq (hf : martingale f ℱ μ) {i j : ι} (hij : i ≤ j) {s : set α}
  (hs : measurable_set[ℱ i] s) :
  ∫ x in s, f i x ∂μ = ∫ x in s, f j x ∂μ :=
begin
  rw ← @set_integral_condexp _ _ _ _ _ _ _ _ (ℱ i) m0 _ (ℱ.le i) _ _ _ (hf.integrable j) hs,
  refine set_integral_congr_ae (ℱ.le i s hs) _,
  filter_upwards [hf.2 i j hij] with _ heq _ using heq.symm,
end

lemma add (hf : martingale f ℱ μ) (hg : martingale g ℱ μ) : martingale (f + g) ℱ μ :=
begin
  refine ⟨hf.adapted.add hg.adapted, λ i j hij, _⟩,
  exact (condexp_add (hf.integrable j) (hg.integrable j)).trans
    ((hf.2 i j hij).add (hg.2 i j hij)),
end

lemma neg (hf : martingale f ℱ μ) : martingale (-f) ℱ μ :=
⟨hf.adapted.neg, λ i j hij, (condexp_neg (f j)).trans ((hf.2 i j hij).neg)⟩

lemma sub (hf : martingale f ℱ μ) (hg : martingale g ℱ μ) : martingale (f - g) ℱ μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg, }

lemma smul (c : ℝ) (hf : martingale f ℱ μ) : martingale (c • f) ℱ μ :=
begin
  refine ⟨hf.adapted.smul c, λ i j hij, _⟩,
  refine (condexp_smul c (f j)).trans ((hf.2 i j hij).mono (λ x hx, _)),
  rw [pi.smul_apply, hx, pi.smul_apply, pi.smul_apply],
end

lemma supermartingale [preorder E] (hf : martingale f ℱ μ) : supermartingale f ℱ μ :=
⟨hf.1, λ i j hij, (hf.2 i j hij).le, λ i, hf.integrable i⟩

lemma submartingale [preorder E] (hf : martingale f ℱ μ) : submartingale f ℱ μ :=
⟨hf.1, λ i j hij, (hf.2 i j hij).symm.le, λ i, hf.integrable i⟩

end martingale

lemma martingale_iff [partial_order E] : martingale f ℱ μ ↔
  supermartingale f ℱ μ ∧ submartingale f ℱ μ :=
⟨λ hf, ⟨hf.supermartingale, hf.submartingale⟩,
 λ ⟨hf₁, hf₂⟩, ⟨hf₁.1, λ i j hij, (hf₁.2.1 i j hij).antisymm (hf₂.2.1 i j hij)⟩⟩

lemma martingale_condexp (f : α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] :
  martingale (λ i, μ[f | ℱ i, ℱ.le i]) ℱ μ :=
⟨λ i, measurable_condexp, λ i j hij, condexp_condexp_of_le (ℱ.mono hij) _⟩

namespace supermartingale

@[protected]
lemma adapted [has_le E] (hf : supermartingale f ℱ μ) : adapted ℱ f := hf.1

@[protected]
lemma measurable [has_le E] (hf : supermartingale f ℱ μ) (i : ι) : measurable[ℱ i] (f i) :=
hf.adapted i

@[protected]
lemma integrable [has_le E] (hf : supermartingale f ℱ μ) (i : ι) : integrable (f i) μ := hf.2.2 i

lemma condexp_ae_le [has_le E] (hf : supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  μ[f j | ℱ i, ℱ.le i] ≤ᵐ[μ] f i :=
hf.2.1 i j hij

lemma set_integral_le {f : ι → α → ℝ} (hf : supermartingale f ℱ μ)
  {i j : ι} (hij : i ≤ j) {s : set α} (hs : measurable_set[ℱ i] s) :
  ∫ x in s, f j x ∂μ ≤ ∫ x in s, f i x ∂μ :=
begin
  rw ← set_integral_condexp (ℱ.le i) (hf.integrable j) hs,
  refine set_integral_mono_ae integrable_condexp.integrable_on (hf.integrable i).integrable_on _,
  filter_upwards [hf.2.1 i j hij] with _ heq using heq,
end

lemma add [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) (hg : supermartingale g ℱ μ) : supermartingale (f + g) ℱ μ :=
begin
  refine ⟨hf.1.add hg.1, λ i j hij, _, λ i, (hf.2.2 i).add (hg.2.2 i)⟩,
  refine (condexp_add (hf.integrable j) (hg.integrable j)).le.trans _,
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij],
  intros,
  refine add_le_add _ _; assumption,
end

lemma add_martingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) (hg : martingale g ℱ μ) : supermartingale (f + g) ℱ μ :=
hf.add hg.supermartingale

lemma neg [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) : submartingale (-f) ℱ μ :=
begin
  refine ⟨hf.1.neg, λ i j hij, _, λ i, (hf.2.2 i).neg⟩,
  refine eventually_le.trans _ (condexp_neg (f j)).symm.le,
  filter_upwards [hf.2.1 i j hij] with _ _,
  simpa,
end

end supermartingale

namespace submartingale

@[protected]
lemma adapted [has_le E] (hf : submartingale f ℱ μ) : adapted ℱ f := hf.1

@[protected]
lemma measurable [has_le E] (hf : submartingale f ℱ μ) (i : ι) : measurable[ℱ i] (f i) :=
hf.adapted i

@[protected]
lemma integrable [has_le E] (hf : submartingale f ℱ μ) (i : ι) : integrable (f i) μ := hf.2.2 i

lemma ae_le_condexp [has_le E] (hf : submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  f i ≤ᵐ[μ] μ[f j | ℱ i, ℱ.le i] :=
hf.2.1 i j hij

lemma add [preorder E] [covariant_class E E (+) (≤)]
  (hf : submartingale f ℱ μ) (hg : submartingale g ℱ μ) : submartingale (f + g) ℱ μ :=
begin
  refine ⟨hf.1.add hg.1, λ i j hij, _, λ i, (hf.2.2 i).add (hg.2.2 i)⟩,
  refine eventually_le.trans _ (condexp_add (hf.integrable j) (hg.integrable j)).symm.le,
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij],
  intros,
  refine add_le_add _ _; assumption,
end

lemma add_martingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : submartingale f ℱ μ) (hg : martingale g ℱ μ) : submartingale (f + g) ℱ μ :=
hf.add hg.submartingale

lemma neg [preorder E] [covariant_class E E (+) (≤)]
  (hf : submartingale f ℱ μ) : supermartingale (-f) ℱ μ :=
begin
  refine ⟨hf.1.neg, λ i j hij, (condexp_neg (f j)).le.trans _, λ i, (hf.2.2 i).neg⟩,
  filter_upwards [hf.2.1 i j hij] with _ _,
  simpa,
end

lemma set_integral_le {f : ι → α → ℝ} (hf : submartingale f ℱ μ)
  {i j : ι} (hij : i ≤ j) {s : set α} (hs : measurable_set[ℱ i] s) :
  ∫ x in s, f i x ∂μ ≤ ∫ x in s, f j x ∂μ :=
begin
  rw [← neg_le_neg_iff, ← integral_neg, ← integral_neg],
  exact supermartingale.set_integral_le hf.neg hij hs,
end

lemma sub_supermartingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : submartingale f ℱ μ) (hg : supermartingale g ℱ μ) : submartingale (f - g) ℱ μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg }

lemma sub_martingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : submartingale f ℱ μ) (hg : martingale g ℱ μ) : submartingale (f - g) ℱ μ :=
hf.sub_supermartingale hg.supermartingale

end submartingale

namespace supermartingale

lemma sub_submartingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) (hg : submartingale g ℱ μ) : supermartingale (f - g) ℱ μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg }

lemma sub_martingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) (hg : martingale g ℱ μ) : supermartingale (f - g) ℱ μ :=
hf.sub_submartingale hg.submartingale

section

variables {F : Type*} [measurable_space F] [normed_lattice_add_comm_group F]
  [normed_space ℝ F] [complete_space F] [borel_space F] [second_countable_topology F]
  [ordered_smul ℝ F]

lemma smul_nonneg {f : ι → α → F}
  {c : ℝ} (hc : 0 ≤ c) (hf : supermartingale f ℱ μ) :
  supermartingale (c • f) ℱ μ :=
begin
  refine ⟨hf.1.smul c, λ i j hij, _, λ i, (hf.2.2 i).smul c⟩,
  refine (condexp_smul c (f j)).le.trans _,
  filter_upwards [hf.2.1 i j hij] with _ hle,
  simp,
  exact smul_le_smul_of_nonneg hle hc,
end

lemma smul_nonpos {f : ι → α → F}
  {c : ℝ} (hc : c ≤ 0) (hf : supermartingale f ℱ μ) :
  submartingale (c • f) ℱ μ :=
begin
  rw [← neg_neg c, (by { ext i x, simp } : - -c • f = -(-c • f))],
  exact (hf.smul_nonneg $ neg_nonneg.2 hc).neg,
end

end

end supermartingale

namespace submartingale

section

variables {F : Type*} [measurable_space F] [normed_lattice_add_comm_group F]
  [normed_space ℝ F] [complete_space F] [borel_space F] [second_countable_topology F]
  [ordered_smul ℝ F]

lemma smul_nonneg {f : ι → α → F}
  {c : ℝ} (hc : 0 ≤ c) (hf : submartingale f ℱ μ) :
  submartingale (c • f) ℱ μ :=
begin
  rw [← neg_neg c, (by { ext i x, simp } : - -c • f = -(c • -f))],
  exact supermartingale.neg (hf.neg.smul_nonneg hc),
end

lemma smul_nonpos {f : ι → α → F}
  {c : ℝ} (hc : c ≤ 0) (hf : submartingale f ℱ μ) :
  supermartingale (c • f) ℱ μ :=
begin
  rw [← neg_neg c, (by { ext i x, simp } : - -c • f = -(-c • f))],
  exact (hf.smul_nonneg $ neg_nonneg.2 hc).neg,
end

end

end submartingale

section nat

variables {𝒢 : filtration ℕ m0} [sigma_finite_filtration μ 𝒢]

namespace submartingale

lemma integrable_stopped_value [has_le E] {f : ℕ → α → E} (hf : submartingale f 𝒢 μ) {τ : α → ℕ}
  (hτ : is_stopping_time 𝒢 τ) {N : ℕ} (hbdd : ∀ x, τ x ≤ N) :
  integrable (stopped_value f τ) μ :=
integrable_stopped_value hτ hf.integrable hbdd

-- We may generalize the below lemma to functions taking value in a `normed_lattice_add_comm_group`.
-- Similarly, generalize `(super/)submartingale.set_integral_le`.

/-- Given a submartingale `f` and bounded stopping times `τ` and `π` such that `τ ≤ π`, the
expectation of `stopped_value f τ` is less or equal to the expectation of `stopped_value f π`.
This is the forward direction of the optional stopping theorem. -/
lemma expected_stopped_value_mono {f : ℕ → α → ℝ} (hf : submartingale f 𝒢 μ) {τ π : α → ℕ}
  (hτ : is_stopping_time 𝒢 τ) (hπ : is_stopping_time 𝒢 π) (hle : τ ≤ π)
  {N : ℕ} (hbdd : ∀ x, π x ≤ N) :
  μ[stopped_value f τ] ≤ μ[stopped_value f π] :=
begin
  rw [← sub_nonneg, ← integral_sub', stopped_value_sub_eq_sum' hle hbdd],
  { simp only [finset.sum_apply],
    have : ∀ i, measurable_set[𝒢 i] {x : α | τ x ≤ i ∧ i < π x},
    { intro i,
      refine (hτ i).inter _,
      convert (hπ i).compl,
      ext x,
      simpa },
    rw integral_finset_sum,
    { refine finset.sum_nonneg (λ i hi, _),
      rw [integral_indicator (𝒢.le _ _ (this _)), integral_sub', sub_nonneg],
      { exact hf.set_integral_le (nat.le_succ i) (this _) },
      { exact (hf.integrable _).integrable_on },
      { exact (hf.integrable _).integrable_on } },
    intros i hi,
    exact integrable.indicator (integrable.sub (hf.integrable _) (hf.integrable _))
      (𝒢.le _ _ (this _)) },
  { exact hf.integrable_stopped_value hπ hbdd },
  { exact hf.integrable_stopped_value hτ (λ x, le_trans (hle x) (hbdd x)) }
end

section upcrossing

/-
Upcrossing.

The main idea we need from the definition of upcrossing is:
{x | lim f_n(x) DNE} = {x | lim inf f_n(x) < lim sup f_n(x)} =
⋃ (a < b : ℝ) {x | lim U_n([a, b])(x) = ∞} =
⋃ (a < b : ℚ) {x | lim U_n([a, b])(x) = ∞}

To define upcrossing, we consider the following stopping times.
-/

-- **Update doc string**
/-- The upper crossing of a random process on the interval `[a, b]` before time `n + 1` is the
ℕ-valued random variable corresponding to the first time the process is above `b` after the
`n + 1`-th lower crossing. -/
noncomputable
def upper_crossing (f : ℕ → α → ℝ) (a b : ℝ) (N : ℕ) : ℕ → α → ℕ
| 0 x := 0
| (n + 1) x := if h : ∃ s, s ≤ N ∧
  (if h : ∃ t, t ≤ N ∧ upper_crossing n x < t ∧ f t x ≤ a then nat.find h else N) < s ∧ b ≤ f s x
  then nat.find h else N

lemma upper_crossing_zero {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} :
  upper_crossing f a b N 0 = 0 :=
rfl

lemma upper_crossing_succ {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} (n : ℕ) :
  upper_crossing f a b N (n + 1) =
  λ x, if h : ∃ s, s ≤ N ∧
      (if h : ∃ t, t ≤ N ∧ upper_crossing f a b N n x < t ∧ f t x ≤ a then nat.find h else N) < s ∧
        b ≤ f s x
    then nat.find h else N :=
by { ext x, dsimp [upper_crossing], refl } -- `refl` without `dsimp` only does not work

/-- The lower crossing of a random process on the interval `[a, b]` before time `n + 1` is the
ℕ-valued random variable corresponding to the first time the process is below `a` after the
`n`-th upper crossing. -/
noncomputable
def lower_crossing (f : ℕ → α → ℝ) (a b : ℝ) (N : ℕ) : ℕ → α → ℕ
| 0 x := 0
| (n + 1) x := if h : ∃ t, t ≤ N ∧ upper_crossing f a b N n x < t ∧ f t x ≤ a
  then nat.find h else N

lemma upper_crossing_succ_eq_dite_lower_crossing {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} (n : ℕ) :
  upper_crossing f a b N (n + 1) =
  λ x, if h : ∃ s, s ≤ N ∧ lower_crossing f a b N (n + 1) x < s ∧ b ≤ f s x
    then nat.find h else N :=
begin
  ext x,
  rw upper_crossing_succ,
  refl,
end

lemma lower_crossing_zero {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} :
  lower_crossing f a b N 0 = 0 :=
rfl

lemma lower_crossing_succ {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} (n : ℕ) :
  lower_crossing f a b N (n + 1) =
  λ x, if h : ∃ t, t ≤ N ∧ upper_crossing f a b N n x < t ∧ f t x ≤ a then nat.find h else N :=
rfl

-- lemma upper_crossing_is_stopping_time {f : ℕ → α → ℝ} (hf : adapted 𝒢 f) {a b : ℝ} {N : ℕ} {n : ℕ} :
--   is_stopping_time 𝒢 (upper_crossing f a b N n) :=
-- begin
--   intro i,
--   induction n with k ih,
--   { simp [upper_crossing_zero] },
--   { rw upper_crossing_succ,
--     sorry,
--   }
-- end

-- lemma lower_crossing_is_stopping_time {f : ℕ → α → ℝ} (hf : adapted 𝒢 f) {a b : ℝ} {N : ℕ} {n : ℕ} :
--   is_stopping_time 𝒢 (lower_crossing f a b N n) :=
-- sorry

lemma stopped_value_upper_crossing_ge (f : ℕ → α → ℝ) (a b : ℝ) (N : ℕ) (n : ℕ) (x : α) :
  upper_crossing f a b N (n + 1) x = N ∨
  b ≤ stopped_value f (upper_crossing f a b N (n + 1)) x :=
begin
  rw or_iff_not_imp_left,
  intro h,
  have : ∃ s, s ≤ N ∧ lower_crossing f a b N (n + 1) x < s ∧ b ≤ f s x,
  { by_contra h',
    refine h _,
    rw upper_crossing_succ_eq_dite_lower_crossing,
    exact dif_neg h' },
  convert (nat.find_spec this).2.2,
  rw [stopped_value, upper_crossing_succ_eq_dite_lower_crossing],
  dsimp,
  rw dif_pos this,
end

lemma stopped_value_lower_crossing_le (f : ℕ → α → ℝ) (a b : ℝ) (N : ℕ) (n : ℕ) (x : α) :
  lower_crossing f a b N (n + 1) x = N ∨
  stopped_value f (lower_crossing f a b N (n + 1)) x ≤ a :=
begin
  rw or_iff_not_imp_left,
  intro h,
  have : ∃ t, t ≤ N ∧ upper_crossing f a b N n x < t ∧ f t x ≤ a,
  { by_contra h',
    exact h (dif_neg h') },
  convert (nat.find_spec this).2.2,
  rw [stopped_value, lower_crossing_succ],
  dsimp,
  rw dif_pos this,
end

lemma upper_crossing_stabilize {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} {n m : ℕ} (hnm : n ≤ m) {x : α}
  (h : upper_crossing f a b N n x = N) : upper_crossing f a b N m x = N :=
begin
  induction hnm with k _ ih,
  { assumption },
  { rw upper_crossing_succ,
    dsimp,
    rw dif_neg,
    push_neg,
    intros t ht hlt,
    rw [ih, dif_neg] at hlt,
    { exact (hlt.not_le ht).elim },
    { push_neg,
      intros s hs hls,
      exact (hls.not_le hs).elim } }
end

lemma upper_crossing_stabilize_of_lower_crossing
  {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} {n m : ℕ} (hnm : n ≤ m) {x : α}
  (h : lower_crossing f a b N n x = N) : upper_crossing f a b N m x = N :=
begin
  induction hnm with k _ ih,
  { induction n with k ih,
    { rw lower_crossing_zero at h,
      rwa upper_crossing_zero },
    { rw upper_crossing_succ_eq_dite_lower_crossing,
      dsimp,
      rw [h, dif_neg],
      push_neg,
      intros t ht hlt,
      exact (hlt.not_le ht).elim } },
  { exact upper_crossing_stabilize (nat.le_succ _) ih }
end

lemma lower_crossing_stabilize {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} {n m : ℕ} (hnm : n ≤ m) {x : α}
  (h : lower_crossing f a b N n x = N) : lower_crossing f a b N m x = N :=
begin
  induction hnm with k _ ih,
  { assumption },
  { rw lower_crossing_succ,
    dsimp,
    rw dif_neg,
    { rw upper_crossing_stabilize_of_lower_crossing le_rfl ih,
      push_neg,
      intros t ht hlt,
      exact (hlt.not_le ht).elim } }
end

lemma upper_crossing_sub_lower_crossing {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} {n : ℕ} {x : α}
  (h : upper_crossing f a b N (n + 1) x ≠ N) :
  b - a ≤ stopped_value f (upper_crossing f a b N (n + 1)) x -
    stopped_value f (lower_crossing f a b N (n + 1)) x :=
begin
  cases stopped_value_lower_crossing_le f a b N n x with heq hle,
  { cases stopped_value_upper_crossing_ge f a b N n x with _ hle',
    { contradiction },
    { exact (h $ upper_crossing_stabilize_of_lower_crossing le_rfl heq).elim } },
  { cases stopped_value_upper_crossing_ge f a b N n x with _ hle',
    { contradiction },
    { linarith } }
end

/-- The `t`-th upcrossing of a random process on the interval `[a, b]` is the ℕ-valued random
variable corresponding to the maximum number of times the random process crossed from below `a` to
above `b` before (not including) time `t`.

**Upcrossing is actually 1 more than what the doc-string suggests here in the non-zero case**
In particular, `upcrossing f a b n` provides the first time the `upper_crossing` reaches `N`
(hence indicating the last time the process performs an upcrossing) if such a time exists and
0 otherwise. -/
noncomputable
def upcrossing (f : ℕ → α → ℝ) (a b : ℝ) (N : ℕ) : α → ℕ :=
λ x, if h : ∃ n, n < N ∧ upper_crossing f a b N n x = N then nat.find h else 0

lemma upper_crossing_upcrossing_zero {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} {n : ℕ}
  {x : α} (hn : upcrossing f a b N x ≠ 0) :
  upper_crossing f a b N n x = N :=
begin
  rw [upcrossing, dite_ne_right_iff] at hn,
  sorry
end

lemma upcrossing_le {f : ℕ → α → ℝ} {a b : ℝ} {N : ℕ} {x : α} :
  ↑(upcrossing f a b N x) * (b - a) ≤
  stopped_value f (lower_crossing f a b N 1) x - a +
  ∑ i in finset.range N,
  (stopped_value f (upper_crossing f a b N i) x -
   stopped_value f (lower_crossing f a b N i) x) :=
begin
  set k := if h : ∃ n, n < N ∧ upper_crossing f a b N n x = N then nat.find h else 0 with hk,
  split_ifs at hk,
  { rw ← finset.sum_range_add_sum_Ico _ (nat.find_spec h).1.le,
    have : ∑ k in finset.Ico k N, (stopped_value f (upper_crossing f a b N k) x -
      stopped_value f (lower_crossing f a b N k) x) = 0,
    { sorry },
    rw [← hk, this, add_zero],
    have h' : ∑ i in finset.range k,
      (stopped_value f (upper_crossing f a b N i) x - stopped_value f (lower_crossing f a b N i) x)
    = stopped_value f (upper_crossing f a b N 1) x - stopped_value f (lower_crossing f a b N 1) x +
      ∑ i in finset.Ico 2 k,
      (stopped_value f (upper_crossing f a b N i) x - stopped_value f (lower_crossing f a b N i) x),
    { sorry },
    rw h',
    clear h',
    have h'' : ∑ i in finset.Ico 2 k, (b - a) ≤ ∑ i in finset.Ico 2 k,
      (stopped_value f (upper_crossing f a b N i) x - stopped_value f (lower_crossing f a b N i) x),
    { refine finset.sum_le_sum (λ i hi, _),
      rw finset.mem_Ico at hi,
      cases hi with hi₁ hi₂,
      have hnonneg : i ≠ 0,
      { linarith },
      rcases nat.exists_eq_succ_of_ne_zero hnonneg with ⟨j, rfl⟩,
      refine upper_crossing_sub_lower_crossing (λ hu, _),
      rw hk at hi₂,
      exact nat.find_min h hi₂ ⟨lt_trans hi₂ (nat.find_spec h).1, hu⟩ },
    ring_nf,
    rw ← add_assoc,
    refine le_trans _ (add_le_add le_rfl h''),
    rw finset.sum_const,
    sorry
  },
  { simp only [upcrossing],
    rw [dif_neg h, nat.cast_zero, zero_mul],
    sorry }
end

end upcrossing

end submartingale

end nat

end measure_theory
