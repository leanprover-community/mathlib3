/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import probability.notation
import probability.process.stopping

/-!
# Martingales

A family of functions `f : ι → Ω → E` is a martingale with respect to a filtration `ℱ` if every
`f i` is integrable, `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ i] =ᵐ[μ] f i`. On the other hand, `f : ι → Ω → E` is said to be a supermartingale
with respect to the filtration `ℱ` if `f i` is integrable, `f` is adapted with resepct to `ℱ`
and for all `i ≤ j`, `μ[f j | ℱ i] ≤ᵐ[μ] f i`. Finally, `f : ι → Ω → E` is said to be a
submartingale with respect to the filtration `ℱ` if `f i` is integrable, `f` is adapted with
resepct to `ℱ` and for all `i ≤ j`, `f i ≤ᵐ[μ] μ[f j | ℱ i]`.

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

variables {Ω E ι : Type*} [preorder ι]
  {m0 : measurable_space Ω} {μ : measure Ω}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  {f g : ι → Ω → E} {ℱ : filtration ι m0}

/-- A family of functions `f : ι → Ω → E` is a martingale with respect to a filtration `ℱ` if `f`
is adapted with respect to `ℱ` and for all `i ≤ j`, `μ[f j | ℱ i] =ᵐ[μ] f i`. -/
def martingale (f : ι → Ω → E) (ℱ : filtration ι m0) (μ : measure Ω . volume_tac) : Prop :=
adapted ℱ f ∧ ∀ i j, i ≤ j → μ[f j | ℱ i] =ᵐ[μ] f i

/-- A family of integrable functions `f : ι → Ω → E` is a supermartingale with respect to a
filtration `ℱ` if `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] ≤ᵐ[μ] f i`. -/
def supermartingale [has_le E] (f : ι → Ω → E) (ℱ : filtration ι m0) (μ : measure Ω . volume_tac) :
  Prop :=
adapted ℱ f ∧ (∀ i j, i ≤ j → μ[f j | ℱ i] ≤ᵐ[μ] f i) ∧ ∀ i, integrable (f i) μ

/-- A family of integrable functions `f : ι → Ω → E` is a submartingale with respect to a
filtration `ℱ` if `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`f i ≤ᵐ[μ] μ[f j | ℱ.le i]`. -/
def submartingale [has_le E] (f : ι → Ω → E) (ℱ : filtration ι m0) (μ : measure Ω . volume_tac) :
  Prop :=
adapted ℱ f ∧ (∀ i j, i ≤ j → f i ≤ᵐ[μ] μ[f j | ℱ i]) ∧ ∀ i, integrable (f i) μ

lemma martingale_const (ℱ : filtration ι m0) (μ : measure Ω) [is_finite_measure μ] (x : E) :
  martingale (λ _ _, x) ℱ μ :=
⟨adapted_const ℱ _, λ i j hij, by rw condexp_const (ℱ.le _)⟩

lemma martingale_const_fun [order_bot ι]
  (ℱ : filtration ι m0) (μ : measure Ω) [is_finite_measure μ]
  {f : Ω → E} (hf : strongly_measurable[ℱ ⊥] f) (hfint : integrable f μ) :
  martingale (λ _, f) ℱ μ :=
begin
  refine ⟨λ i, hf.mono $ ℱ.mono bot_le, λ i j hij, _⟩,
  rw condexp_of_strongly_measurable (ℱ.le _) (hf.mono $ ℱ.mono bot_le) hfint,
  apply_instance,
end

variables (E)
lemma martingale_zero (ℱ : filtration ι m0) (μ : measure Ω) :
  martingale (0 : ι → Ω → E) ℱ μ :=
⟨adapted_zero E ℱ, λ i j hij, by { rw [pi.zero_apply, condexp_zero], simp, }⟩
variables {E}

namespace martingale

@[protected]
lemma adapted (hf : martingale f ℱ μ) : adapted ℱ f := hf.1

@[protected]
lemma strongly_measurable (hf : martingale f ℱ μ) (i : ι) : strongly_measurable[ℱ i] (f i) :=
hf.adapted i

lemma condexp_ae_eq (hf : martingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  μ[f j | ℱ i] =ᵐ[μ] f i :=
hf.2 i j hij

@[protected]
lemma integrable (hf : martingale f ℱ μ) (i : ι) : integrable (f i) μ :=
integrable_condexp.congr (hf.condexp_ae_eq (le_refl i))

lemma set_integral_eq [sigma_finite_filtration μ ℱ] (hf : martingale f ℱ μ) {i j : ι} (hij : i ≤ j)
  {s : set Ω} (hs : measurable_set[ℱ i] s) :
  ∫ ω in s, f i ω ∂μ = ∫ ω in s, f j ω ∂μ :=
begin
  rw ← @set_integral_condexp _ _ _ _ _ (ℱ i) m0 _ _ _ (ℱ.le i) _ (hf.integrable j) hs,
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

lemma martingale_condexp (f : Ω → E) (ℱ : filtration ι m0) (μ : measure Ω)
  [sigma_finite_filtration μ ℱ] :
  martingale (λ i, μ[f | ℱ i]) ℱ μ :=
⟨λ i, strongly_measurable_condexp, λ i j hij, condexp_condexp_of_le (ℱ.mono hij) (ℱ.le j)⟩

namespace supermartingale

@[protected]
lemma adapted [has_le E] (hf : supermartingale f ℱ μ) : adapted ℱ f := hf.1

@[protected]
lemma strongly_measurable [has_le E] (hf : supermartingale f ℱ μ) (i : ι) :
  strongly_measurable[ℱ i] (f i) :=
hf.adapted i

@[protected]
lemma integrable [has_le E] (hf : supermartingale f ℱ μ) (i : ι) : integrable (f i) μ := hf.2.2 i

lemma condexp_ae_le [has_le E] (hf : supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  μ[f j | ℱ i] ≤ᵐ[μ] f i :=
hf.2.1 i j hij

lemma set_integral_le [sigma_finite_filtration μ ℱ] {f : ι → Ω → ℝ} (hf : supermartingale f ℱ μ)
  {i j : ι} (hij : i ≤ j) {s : set Ω} (hs : measurable_set[ℱ i] s) :
  ∫ ω in s, f j ω ∂μ ≤ ∫ ω in s, f i ω ∂μ :=
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
lemma strongly_measurable [has_le E] (hf : submartingale f ℱ μ) (i : ι) :
  strongly_measurable[ℱ i] (f i) :=
hf.adapted i

@[protected]
lemma integrable [has_le E] (hf : submartingale f ℱ μ) (i : ι) : integrable (f i) μ := hf.2.2 i

lemma ae_le_condexp [has_le E] (hf : submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  f i ≤ᵐ[μ] μ[f j | ℱ i] :=
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

/-- The converse of this lemma is `measure_theory.submartingale_of_set_integral_le`. -/
lemma set_integral_le [sigma_finite_filtration μ ℱ] {f : ι → Ω → ℝ} (hf : submartingale f ℱ μ)
  {i j : ι} (hij : i ≤ j) {s : set Ω} (hs : measurable_set[ℱ i] s) :
  ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f j ω ∂μ :=
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

protected lemma sup {f g : ι → Ω → ℝ} (hf : submartingale f ℱ μ) (hg : submartingale g ℱ μ) :
  submartingale (f ⊔ g) ℱ μ :=
begin
  refine ⟨λ i, @strongly_measurable.sup _ _ _ _ (ℱ i) _ _ _ (hf.adapted i) (hg.adapted i),
    λ i j hij, _, λ i, integrable.sup (hf.integrable _) (hg.integrable _)⟩,
  refine eventually_le.sup_le _ _,
  { exact eventually_le.trans (hf.2.1 i j hij)
      (condexp_mono (hf.integrable _) (integrable.sup (hf.integrable j) (hg.integrable j))
      (eventually_of_forall (λ x, le_max_left _ _))) },
  { exact eventually_le.trans (hg.2.1 i j hij)
      (condexp_mono (hg.integrable _) (integrable.sup (hf.integrable j) (hg.integrable j))
      (eventually_of_forall (λ x, le_max_right _ _))) }
end

protected lemma pos {f : ι → Ω → ℝ} (hf : submartingale f ℱ μ) :
  submartingale (f⁺) ℱ μ :=
hf.sup (martingale_zero _ _ _).submartingale

end submartingale

section submartingale

lemma submartingale_of_set_integral_le [is_finite_measure μ]
  {f : ι → Ω → ℝ} (hadp : adapted ℱ f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i j : ι, i ≤ j → ∀ s : set Ω, measurable_set[ℱ i] s →
    ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f j ω ∂μ) :
  submartingale f ℱ μ :=
begin
  refine ⟨hadp, λ i j hij, _, hint⟩,
  suffices : f i ≤ᵐ[μ.trim (ℱ.le i)] μ[f j| ℱ i],
  { exact ae_le_of_ae_le_trim this },
  suffices : 0 ≤ᵐ[μ.trim (ℱ.le i)] μ[f j| ℱ i] - f i,
  { filter_upwards [this] with x hx,
    rwa ← sub_nonneg },
  refine ae_nonneg_of_forall_set_integral_nonneg
    ((integrable_condexp.sub (hint i)).trim _ (strongly_measurable_condexp.sub $ hadp i))
    (λ s hs h's, _),
  specialize hf i j hij s hs,
  rwa [← set_integral_trim _ (strongly_measurable_condexp.sub $ hadp i) hs,
    integral_sub' integrable_condexp.integrable_on (hint i).integrable_on, sub_nonneg,
    set_integral_condexp (ℱ.le i) (hint j) hs],
end

lemma submartingale_of_condexp_sub_nonneg [is_finite_measure μ]
  {f : ι → Ω → ℝ} (hadp : adapted ℱ f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[f j - f i | ℱ i]) :
  submartingale f ℱ μ :=
begin
  refine ⟨hadp, λ i j hij, _, hint⟩,
  rw [← condexp_of_strongly_measurable (ℱ.le _) (hadp _) (hint _), ← eventually_sub_nonneg],
  exact eventually_le.trans (hf i j hij) (condexp_sub (hint _) (hint _)).le,
  apply_instance
end

lemma submartingale.condexp_sub_nonneg
  {f : ι → Ω → ℝ} (hf : submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  0 ≤ᵐ[μ] μ[f j - f i | ℱ i] :=
begin
  by_cases h : sigma_finite (μ.trim (ℱ.le i)),
  swap, { rw condexp_of_not_sigma_finite (ℱ.le i) h },
  refine eventually_le.trans _ (condexp_sub (hf.integrable _) (hf.integrable _)).symm.le,
  rw [eventually_sub_nonneg,
    condexp_of_strongly_measurable (ℱ.le _) (hf.adapted _) (hf.integrable _)],
  { exact hf.2.1 i j hij },
  { exact h }
end

lemma submartingale_iff_condexp_sub_nonneg [is_finite_measure μ] {f : ι → Ω → ℝ} :
  submartingale f ℱ μ ↔ adapted ℱ f ∧ (∀ i, integrable (f i) μ) ∧ ∀ i j, i ≤ j →
  0 ≤ᵐ[μ] μ[f j - f i | ℱ i] :=
⟨λ h, ⟨h.adapted, h.integrable, λ i j, h.condexp_sub_nonneg⟩,
 λ ⟨hadp, hint, h⟩, submartingale_of_condexp_sub_nonneg hadp hint h⟩

end submartingale

namespace supermartingale

lemma sub_submartingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) (hg : submartingale g ℱ μ) : supermartingale (f - g) ℱ μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg }

lemma sub_martingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) (hg : martingale g ℱ μ) : supermartingale (f - g) ℱ μ :=
hf.sub_submartingale hg.submartingale

section

variables {F : Type*} [normed_lattice_add_comm_group F]
  [normed_space ℝ F] [complete_space F] [ordered_smul ℝ F]

lemma smul_nonneg {f : ι → Ω → F}
  {c : ℝ} (hc : 0 ≤ c) (hf : supermartingale f ℱ μ) :
  supermartingale (c • f) ℱ μ :=
begin
  refine ⟨hf.1.smul c, λ i j hij, _, λ i, (hf.2.2 i).smul c⟩,
  refine (condexp_smul c (f j)).le.trans _,
  filter_upwards [hf.2.1 i j hij] with _ hle,
  simp,
  exact smul_le_smul_of_nonneg hle hc,
end

lemma smul_nonpos {f : ι → Ω → F}
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

variables {F : Type*} [normed_lattice_add_comm_group F]
  [normed_space ℝ F] [complete_space F] [ordered_smul ℝ F]

lemma smul_nonneg {f : ι → Ω → F}
  {c : ℝ} (hc : 0 ≤ c) (hf : submartingale f ℱ μ) :
  submartingale (c • f) ℱ μ :=
begin
  rw [← neg_neg c, (by { ext i x, simp } : - -c • f = -(c • -f))],
  exact supermartingale.neg (hf.neg.smul_nonneg hc),
end

lemma smul_nonpos {f : ι → Ω → F}
  {c : ℝ} (hc : c ≤ 0) (hf : submartingale f ℱ μ) :
  supermartingale (c • f) ℱ μ :=
begin
  rw [← neg_neg c, (by { ext i x, simp } : - -c • f = -(-c • f))],
  exact (hf.smul_nonneg $ neg_nonneg.2 hc).neg,
end

end

end submartingale

section nat

variables {𝒢 : filtration ℕ m0}

lemma submartingale_of_set_integral_le_succ [is_finite_measure μ]
  {f : ℕ → Ω → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, ∀ s : set Ω, measurable_set[𝒢 i] s → ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f (i + 1) ω ∂μ) :
  submartingale f 𝒢 μ :=
begin
  refine submartingale_of_set_integral_le hadp hint (λ i j hij s hs, _),
  induction hij with k hk₁ hk₂,
  { exact le_rfl },
  { exact le_trans hk₂ (hf k s (𝒢.mono hk₁ _ hs)) }
end

lemma supermartingale_of_set_integral_succ_le [is_finite_measure μ]
  {f : ℕ → Ω → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, ∀ s : set Ω, measurable_set[𝒢 i] s → ∫ ω in s, f (i + 1) ω ∂μ ≤ ∫ ω in s, f i ω ∂μ) :
  supermartingale f 𝒢 μ :=
begin
  rw ← neg_neg f,
  refine (submartingale_of_set_integral_le_succ hadp.neg (λ i, (hint i).neg) _).neg,
  simpa only [integral_neg, pi.neg_apply, neg_le_neg_iff],
end

lemma martingale_of_set_integral_eq_succ [is_finite_measure μ]
  {f : ℕ → Ω → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, ∀ s : set Ω, measurable_set[𝒢 i] s → ∫ ω in s, f i ω ∂μ = ∫ ω in s, f (i + 1) ω ∂μ) :
  martingale f 𝒢 μ :=
martingale_iff.2
  ⟨supermartingale_of_set_integral_succ_le hadp hint $ λ i s hs, (hf i s hs).ge,
   submartingale_of_set_integral_le_succ hadp hint $ λ i s hs, (hf i s hs).le⟩

lemma submartingale_nat [is_finite_measure μ]
  {f : ℕ → Ω → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, f i ≤ᵐ[μ] μ[f (i + 1) | 𝒢 i]) :
  submartingale f 𝒢 μ :=
begin
  refine submartingale_of_set_integral_le_succ hadp hint (λ i s hs, _),
  have : ∫ ω in s, f (i + 1) ω ∂μ = ∫ ω in s, μ[f (i + 1)|𝒢 i] ω ∂μ :=
    (set_integral_condexp (𝒢.le i) (hint _) hs).symm,
  rw this,
  exact set_integral_mono_ae (hint i).integrable_on integrable_condexp.integrable_on (hf i),
end

lemma supermartingale_nat [is_finite_measure μ]
  {f : ℕ → Ω → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, μ[f (i + 1) | 𝒢 i] ≤ᵐ[μ] f i) :
  supermartingale f 𝒢 μ :=
begin
  rw ← neg_neg f,
  refine (submartingale_nat hadp.neg (λ i, (hint i).neg) $ λ i,
    eventually_le.trans _ (condexp_neg _).symm.le).neg,
  filter_upwards [hf i] with x hx using neg_le_neg hx,
end

lemma martingale_nat [is_finite_measure μ]
  {f : ℕ → Ω → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, f i =ᵐ[μ] μ[f (i + 1) | 𝒢 i]) :
  martingale f 𝒢 μ :=
martingale_iff.2 ⟨supermartingale_nat hadp hint $ λ i, (hf i).symm.le,
  submartingale_nat hadp hint $ λ i, (hf i).le⟩

lemma submartingale_of_condexp_sub_nonneg_nat [is_finite_measure μ]
  {f : ℕ → Ω → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, 0 ≤ᵐ[μ] μ[f (i + 1) - f i | 𝒢 i]) :
  submartingale f 𝒢 μ :=
begin
  refine submartingale_nat hadp hint (λ i, _),
  rw [← condexp_of_strongly_measurable (𝒢.le _) (hadp _) (hint _), ← eventually_sub_nonneg],
  exact eventually_le.trans (hf i) (condexp_sub (hint _) (hint _)).le,
  apply_instance
end

lemma supermartingale_of_condexp_sub_nonneg_nat [is_finite_measure μ]
  {f : ℕ → Ω → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, 0 ≤ᵐ[μ] μ[f i - f (i + 1) | 𝒢 i]) :
  supermartingale f 𝒢 μ :=
begin
  rw ← neg_neg f,
  refine (submartingale_of_condexp_sub_nonneg_nat hadp.neg (λ i, (hint i).neg) _).neg,
  simpa only [pi.zero_apply, pi.neg_apply, neg_sub_neg]
end

lemma martingale_of_condexp_sub_eq_zero_nat [is_finite_measure μ]
  {f : ℕ → Ω → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, μ[f (i + 1) - f i | 𝒢 i] =ᵐ[μ] 0) :
  martingale f 𝒢 μ :=
begin
  refine martingale_iff.2 ⟨supermartingale_of_condexp_sub_nonneg_nat hadp hint $ λ i, _,
    submartingale_of_condexp_sub_nonneg_nat hadp hint $ λ i, (hf i).symm.le⟩,
  rw ← neg_sub,
  refine (eventually_eq.trans _ (condexp_neg _).symm).le,
  filter_upwards [hf i] with x hx,
  simpa only [pi.zero_apply, pi.neg_apply, zero_eq_neg],
end

-- Note that one cannot use `submartingale.zero_le_of_predictable` to prove the other two
-- corresponding lemmas without imposing more restrictions to the ordering of `E`
/-- A predictable submartingale is a.e. greater equal than its initial state. -/
lemma submartingale.zero_le_of_predictable [preorder E] [sigma_finite_filtration μ 𝒢]
  {f : ℕ → Ω → E} (hfmgle : submartingale f 𝒢 μ) (hfadp : adapted 𝒢 (λ n, f (n + 1))) (n : ℕ) :
  f 0 ≤ᵐ[μ] f n :=
begin
  induction n with k ih,
  { refl },
  { exact ih.trans ((hfmgle.2.1 k (k + 1) k.le_succ).trans_eq $ germ.coe_eq.mp $ congr_arg coe $
      condexp_of_strongly_measurable (𝒢.le _) (hfadp _) $ hfmgle.integrable _) }
end

/-- A predictable supermartingale is a.e. less equal than its initial state. -/
lemma supermartingale.le_zero_of_predictable [preorder E] [sigma_finite_filtration μ 𝒢]
  {f : ℕ → Ω → E} (hfmgle : supermartingale f 𝒢 μ) (hfadp : adapted 𝒢 (λ n, f (n + 1))) (n : ℕ) :
  f n ≤ᵐ[μ] f 0 :=
begin
  induction n with k ih,
  { refl },
  { exact ((germ.coe_eq.mp $ congr_arg coe $ condexp_of_strongly_measurable (𝒢.le _) (hfadp _) $
      hfmgle.integrable _).symm.trans_le (hfmgle.2.1 k (k + 1) k.le_succ)).trans ih }
end

/-- A predictable martingale is a.e. equal to its initial state. -/
lemma martingale.eq_zero_of_predictable [sigma_finite_filtration μ 𝒢]
  {f : ℕ → Ω → E} (hfmgle : martingale f 𝒢 μ) (hfadp : adapted 𝒢 (λ n, f (n + 1))) (n : ℕ) :
  f n =ᵐ[μ] f 0 :=
begin
  induction n with k ih,
  { refl },
  { exact ((germ.coe_eq.mp (congr_arg coe $ condexp_of_strongly_measurable (𝒢.le _) (hfadp _)
      (hfmgle.integrable _))).symm.trans (hfmgle.2 k (k + 1) k.le_succ)).trans ih }
end

namespace submartingale

@[protected]
lemma integrable_stopped_value [has_le E] {f : ℕ → Ω → E} (hf : submartingale f 𝒢 μ) {τ : Ω → ℕ}
  (hτ : is_stopping_time 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
  integrable (stopped_value f τ) μ :=
integrable_stopped_value ℕ hτ hf.integrable hbdd

end submartingale

lemma submartingale.sum_mul_sub [is_finite_measure μ] {R : ℝ} {ξ f : ℕ → Ω → ℝ}
  (hf : submartingale f 𝒢 μ) (hξ : adapted 𝒢 ξ)
  (hbdd : ∀ n ω, ξ n ω ≤ R) (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
  submartingale (λ n, ∑ k in finset.range n, ξ k * (f (k + 1) - f k)) 𝒢 μ :=
begin
  have hξbdd : ∀ i, ∃ C, ∀ ω, |ξ i ω| ≤ C :=
    λ i, ⟨R, λ ω, (abs_of_nonneg (hnonneg i ω)).trans_le (hbdd i ω)⟩,
  have hint : ∀ m, integrable (∑ k in finset.range m, ξ k * (f (k + 1) - f k)) μ :=
    λ m, integrable_finset_sum' _
      (λ i hi, integrable.bdd_mul ((hf.integrable _).sub (hf.integrable _))
      hξ.strongly_measurable.ae_strongly_measurable (hξbdd _)),
  have hadp : adapted 𝒢 (λ n, ∑ k in finset.range n, ξ k * (f (k + 1) - f k)),
  { intro m,
    refine finset.strongly_measurable_sum' _ (λ i hi, _),
    rw finset.mem_range at hi,
    exact (hξ.strongly_measurable_le hi.le).mul
      ((hf.adapted.strongly_measurable_le (nat.succ_le_of_lt hi)).sub
      (hf.adapted.strongly_measurable_le hi.le)) },
  refine submartingale_of_condexp_sub_nonneg_nat hadp hint (λ i, _),
  simp only [← finset.sum_Ico_eq_sub _ (nat.le_succ _), finset.sum_apply, pi.mul_apply,
    pi.sub_apply, nat.Ico_succ_singleton, finset.sum_singleton],
  exact eventually_le.trans (eventually_le.mul_nonneg (eventually_of_forall (hnonneg _))
    (hf.condexp_sub_nonneg (nat.le_succ _))) (condexp_strongly_measurable_mul (hξ _)
    (((hf.integrable _).sub (hf.integrable _)).bdd_mul
      hξ.strongly_measurable.ae_strongly_measurable (hξbdd _))
    ((hf.integrable _).sub (hf.integrable _))).symm.le,
end

/-- Given a discrete submartingale `f` and a predictable process `ξ` (i.e. `ξ (n + 1)` is adapted)
the process defined by `λ n, ∑ k in finset.range n, ξ (k + 1) * (f (k + 1) - f k)` is also a
submartingale. -/
lemma submartingale.sum_mul_sub' [is_finite_measure μ] {R : ℝ} {ξ f : ℕ → Ω → ℝ}
  (hf : submartingale f 𝒢 μ) (hξ : adapted 𝒢 (λ n, ξ (n + 1)))
  (hbdd : ∀ n ω, ξ n ω ≤ R) (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
  submartingale (λ n, ∑ k in finset.range n, ξ (k + 1) * (f (k + 1) - f k)) 𝒢 μ :=
hf.sum_mul_sub hξ (λ n, hbdd _) (λ n, hnonneg _)

end nat

end measure_theory
