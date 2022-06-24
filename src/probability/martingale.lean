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
`μ[f j | ℱ i] =ᵐ[μ] f i`. On the other hand, `f : ι → α → E` is said to be a supermartingale
with respect to the filtration `ℱ` if `f i` is integrable, `f` is adapted with resepct to `ℱ`
and for all `i ≤ j`, `μ[f j | ℱ i] ≤ᵐ[μ] f i`. Finally, `f : ι → α → E` is said to be a
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

variables {α E ι : Type*} [preorder ι]
  {m0 : measurable_space α} {μ : measure α}
  [normed_group E] [normed_space ℝ E] [complete_space E]
  {f g : ι → α → E} {ℱ : filtration ι m0}

/-- A family of functions `f : ι → α → E` is a martingale with respect to a filtration `ℱ` if `f`
is adapted with respect to `ℱ` and for all `i ≤ j`, `μ[f j | ℱ i] =ᵐ[μ] f i`. -/
def martingale (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α) : Prop :=
adapted ℱ f ∧ ∀ i j, i ≤ j → μ[f j | ℱ i] =ᵐ[μ] f i

/-- A family of integrable functions `f : ι → α → E` is a supermartingale with respect to a
filtration `ℱ` if `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] ≤ᵐ[μ] f i`. -/
def supermartingale [has_le E] (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α) : Prop :=
adapted ℱ f ∧ (∀ i j, i ≤ j → μ[f j | ℱ i] ≤ᵐ[μ] f i) ∧ ∀ i, integrable (f i) μ

/-- A family of integrable functions `f : ι → α → E` is a submartingale with respect to a
filtration `ℱ` if `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`f i ≤ᵐ[μ] μ[f j | ℱ.le i]`. -/
def submartingale [has_le E] (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α) : Prop :=
adapted ℱ f ∧ (∀ i j, i ≤ j → f i ≤ᵐ[μ] μ[f j | ℱ i]) ∧ ∀ i, integrable (f i) μ

lemma martingale_const (ℱ : filtration ι m0) (μ : measure α) [is_finite_measure μ] (x : E) :
  martingale (λ _ _, x) ℱ μ :=
⟨adapted_const ℱ _, λ i j hij, by rw condexp_const (ℱ.le _)⟩

variables (E)
lemma martingale_zero (ℱ : filtration ι m0) (μ : measure α) :
  martingale (0 : ι → α → E) ℱ μ :=
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
  {s : set α} (hs : measurable_set[ℱ i] s) :
  ∫ x in s, f i x ∂μ = ∫ x in s, f j x ∂μ :=
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

lemma martingale_condexp (f : α → E) (ℱ : filtration ι m0) (μ : measure α)
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

lemma set_integral_le [sigma_finite_filtration μ ℱ] {f : ι → α → ℝ} (hf : supermartingale f ℱ μ)
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
lemma set_integral_le [sigma_finite_filtration μ ℱ] {f : ι → α → ℝ} (hf : submartingale f ℱ μ)
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

lemma eventually_le.max_le_max [linear_order E] {f₁ f₂ g₁ g₂ : α → E}
  (hf : f₁ ≤ᵐ[μ] f₂) (hg : g₁ ≤ᵐ[μ] g₂) :
  (λ x, max (f₁ x) (g₁ x)) ≤ᵐ[μ] (λ x, max (f₂ x) (g₂ x)) :=
by filter_upwards [hf, hg] with x hfx hgx using max_le_max hfx hgx

lemma eventually_le.max_le [linear_order E] {f g h : α → E}
  (hf : f ≤ᵐ[μ] h) (hg : g ≤ᵐ[μ] h) :
  (λ x, max (f x) (g x)) ≤ᵐ[μ] h :=
by filter_upwards [hf, hg] with x hfx hgx using max_le hfx hgx

lemma eventually_le.le_max_of_le_left [linear_order E] {f g h : α → E}
  (hf : h ≤ᵐ[μ] f) :
  h ≤ᵐ[μ] (λ x, max (f x) (g x)) :=
by filter_upwards [hf] with x hfx using le_max_of_le_left hfx

lemma eventually_le.le_max_of_le_right [linear_order E] {f g h : α → E}
  (hg : h ≤ᵐ[μ] g) :
  h ≤ᵐ[μ] (λ x, max (f x) (g x)) :=
by filter_upwards [hg] with x hgx using le_max_of_le_right hgx

-- move to `ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_strongly_measurable`
lemma ae_le_of_forall_set_integral_le [is_finite_measure μ] {f g : α → ℝ}
  (hfm : strongly_measurable f) (hgm : strongly_measurable g)
  (hf : integrable f μ) (hg : integrable g μ)
  (hf_le : ∀ s, measurable_set s → ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ) :
  f ≤ᵐ[μ] g :=
begin
  rw ← eventually_sub_nonneg,
  refine ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_strongly_measurable
    (hgm.sub hfm) (hg.sub hf) (λ s hs, _),
  rw [integral_sub' hg.integrable_on hf.integrable_on, sub_nonneg],
  exact hf_le s hs
end

-- move
lemma condexp_mono {m : measurable_space α} [is_finite_measure μ] {f g : α → ℝ}
  (hf : integrable f μ) (hg : integrable g μ) (hfg : f ≤ᵐ[μ] g) :
  μ[f | m] ≤ᵐ[μ] μ[g | m] :=
begin
  by_cases hm : m ≤ m0,
  { refine @ae_le_of_ae_le_trim _ _ _ _ _ _ hm _ _ (ae_le_of_forall_set_integral_le
      strongly_measurable_condexp strongly_measurable_condexp
      (integrable_condexp.trim hm strongly_measurable_condexp)
      (integrable_condexp.trim hm strongly_measurable_condexp) (λ s hs, _)),
    rw [← set_integral_trim hm strongly_measurable_condexp hs,
      ← set_integral_trim hm strongly_measurable_condexp hs,
      set_integral_condexp hm hf hs, set_integral_condexp hm hg hs],
    exact @set_integral_mono_ae _ m0 _ _ _ _
      (@integrable.integrable_on _ _ m0 _ _ _ _ hf)
      (@integrable.integrable_on _ _ m0 _ _ _ _ hg) hfg },
  { rw [condexp_of_not_le hm, condexp_of_not_le hm] }
end

-- move
lemma integrable.sup {f g : α → ℝ} (hf : integrable f μ) (hg : integrable g μ) :
  integrable (f ⊔ g) μ :=
begin
  refine integrable.mono' (hf.abs.add hg.abs) (hf.1.sup hg.1) (eventually_of_forall (λ x, _)),
  simp only [pi.add_apply, real.norm_eq_abs, abs_le],
  refine ⟨_, max_le
    (le_add_of_le_of_nonneg (le_abs_self _) (abs_nonneg _))
    (le_add_of_nonneg_of_le (abs_nonneg _) (le_abs_self _))⟩,
  refine le_max_of_le_left _,
  rw [neg_add', sub_le_iff_le_add],
  exact le_trans (neg_abs_le_self _) (le_add_of_nonneg_right (abs_nonneg _)),
end

lemma sup [is_finite_measure μ]
  {f g : ι → α → ℝ} (hf : submartingale f ℱ μ) (hg : submartingale g ℱ μ) :
  submartingale (f ⊔ g) ℱ μ :=
begin
  refine ⟨λ i, @strongly_measurable.sup _ _ _ _ (ℱ i) _ _ _ (hf.adapted i) (hg.adapted i),
    λ i j hij, _, λ i, integrable.sup (hf.integrable _) (hg.integrable _)⟩,
  refine eventually_le.max_le _ _,
  { exact eventually_le.trans (hf.2.1 i j hij)
      (condexp_mono (hf.integrable _) (integrable.sup (hf.integrable j) (hg.integrable j))
      (eventually_of_forall (λ x, le_max_left _ _))) },
  { exact eventually_le.trans (hg.2.1 i j hij)
      (condexp_mono (hg.integrable _) (integrable.sup (hf.integrable j) (hg.integrable j))
      (eventually_of_forall (λ x, le_max_right _ _))) }
end

lemma pos [is_finite_measure μ] {f : ι → α → ℝ} (hf : submartingale f ℱ μ) :
  submartingale (f⁺) ℱ μ :=
hf.sup (martingale_zero _ _ _).submartingale

end submartingale

section temp

variables {m : measurable_space α}

-- Remy will prove this sometime after after this week
lemma condexp_measurable_mul {ξ ζ : α → ℝ} (hξm : strongly_measurable[m] ξ) (hζ : integrable ζ μ)
  -- (hξ : integrable ξ μ) hopefully won't need this
  (hζξ : integrable (ξ * ζ) μ) :
  μ[ξ * ζ | m] =ᵐ[μ] ξ * μ[ζ | m] :=
sorry

end temp

section submartingale

lemma submartingale_of_set_integral_le [is_finite_measure μ]
  {f : ι → α → ℝ} (hadp : adapted ℱ f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i j : ι, i ≤ j → ∀ s : set α, measurable_set[ℱ i] s →
    ∫ x in s, f i x ∂μ ≤ ∫ x in s, f j x ∂μ) :
  submartingale f ℱ μ :=
begin
  refine ⟨hadp, λ i j hij, _, hint⟩,
  suffices : f i ≤ᵐ[μ.trim (ℱ.le i)] μ[f j| ℱ i],
  { exact ae_le_of_ae_le_trim this },
  suffices : 0 ≤ᵐ[μ.trim (ℱ.le i)] μ[f j| ℱ i] - f i,
  { filter_upwards [this] with x hx,
    rwa ← sub_nonneg },
  refine ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure
    ((integrable_condexp.sub (hint i)).trim _ (strongly_measurable_condexp.sub $ hadp i))
    (λ s hs, _),
  specialize hf i j hij s hs,
  rwa [← set_integral_trim _ (strongly_measurable_condexp.sub $ hadp i) hs,
    integral_sub' integrable_condexp.integrable_on (hint i).integrable_on, sub_nonneg,
    set_integral_condexp (ℱ.le i) (hint j) hs],
end

lemma submartingale_of_condexp_sub_nonneg [is_finite_measure μ]
  {f : ι → α → ℝ} (hadp : adapted ℱ f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[f j - f i | ℱ i]) :
  submartingale f ℱ μ :=
begin
  refine ⟨hadp, λ i j hij, _, hint⟩,
  rw [← condexp_of_strongly_measurable (ℱ.le _) (hadp _) (hint _), ← eventually_sub_nonneg],
  exact eventually_le.trans (hf i j hij) (condexp_sub (hint _) (hint _)).le,
  apply_instance
end

lemma submartingale.condexp_sub_nonneg [is_finite_measure μ]
  {f : ι → α → ℝ} (hf : submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  0 ≤ᵐ[μ] μ[f j - f i | ℱ i] :=
begin
  refine eventually_le.trans _ (condexp_sub (hf.integrable _) (hf.integrable _)).symm.le,
  rw [eventually_sub_nonneg,
    condexp_of_strongly_measurable (ℱ.le _) (hf.adapted _) (hf.integrable _)],
  exact hf.2.1 i j hij,
  apply_instance
end

lemma submartingale_iff_condexp_sub_nonneg [is_finite_measure μ] {f : ι → α → ℝ} :
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

variables {F : Type*} [normed_lattice_add_comm_group F]
  [normed_space ℝ F] [complete_space F] [ordered_smul ℝ F]

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

variables {𝒢 : filtration ℕ m0}

lemma submartingale_of_set_integral_le_succ [is_finite_measure μ]
  {f : ℕ → α → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, ∀ s : set α, measurable_set[𝒢 i] s → ∫ x in s, f i x ∂μ ≤ ∫ x in s, f (i + 1) x ∂μ) :
  submartingale f 𝒢 μ :=
begin
  refine submartingale_of_set_integral_le hadp hint (λ i j hij s hs, _),
  induction hij with k hk₁ hk₂,
  { exact le_rfl },
  { exact le_trans hk₂ (hf k s (𝒢.mono hk₁ _ hs)) }
end

lemma submartingale_nat [is_finite_measure μ]
  {f : ℕ → α → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, f i ≤ᵐ[μ] μ[f (i + 1) | 𝒢 i]) :
  submartingale f 𝒢 μ :=
begin
  refine submartingale_of_set_integral_le_succ hadp hint (λ i s hs, _),
  have : ∫ x in s, f (i + 1) x ∂μ = ∫ x in s, μ[f (i + 1)|𝒢 i] x ∂μ :=
    (set_integral_condexp (𝒢.le i) (hint _) hs).symm,
  rw this,
  exact set_integral_mono_ae (hint i).integrable_on integrable_condexp.integrable_on (hf i),
end

lemma submartingale_of_condexp_sub_nonneg_nat [is_finite_measure μ]
  {f : ℕ → α → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, 0 ≤ᵐ[μ] μ[f (i + 1) - f i | 𝒢 i]) :
  submartingale f 𝒢 μ :=
begin
  refine submartingale_nat hadp hint (λ i, _),
  rw [← condexp_of_strongly_measurable (𝒢.le _) (hadp _) (hint _), ← eventually_sub_nonneg],
  exact eventually_le.trans (hf i) (condexp_sub (hint _) (hint _)).le,
  apply_instance
end

namespace submartingale

lemma integrable_stopped_value [has_le E] {f : ℕ → α → E} (hf : submartingale f 𝒢 μ) {τ : α → ℕ}
  (hτ : is_stopping_time 𝒢 τ) {N : ℕ} (hbdd : ∀ x, τ x ≤ N) :
  integrable (stopped_value f τ) μ :=
integrable_stopped_value hτ hf.integrable hbdd

-- We may generalize the below lemma to functions taking value in a `normed_lattice_add_comm_group`.
-- Similarly, generalize `(super/)submartingale.set_integral_le`.

/-- Given a submartingale `f` and bounded stopping times `τ` and `π` such that `τ ≤ π`, the
expectation of `stopped_value f τ` is less than or equal to the expectation of `stopped_value f π`.
This is the forward direction of the optional stopping theorem. -/
lemma expected_stopped_value_mono [sigma_finite_filtration μ 𝒢]
  {f : ℕ → α → ℝ} (hf : submartingale f 𝒢 μ) {τ π : α → ℕ}
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

end submartingale

/-- The converse direction of the optional stopping theorem, i.e. an adapted integrable process `f`
is a submartingale if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
lemma submartingale_of_expected_stopped_value_mono [is_finite_measure μ]
  {f : ℕ → α → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ τ π : α → ℕ, is_stopping_time 𝒢 τ → is_stopping_time 𝒢 π → τ ≤ π → (∃ N, ∀ x, π x ≤ N) →
    μ[stopped_value f τ] ≤ μ[stopped_value f π]) :
  submartingale f 𝒢 μ :=
begin
  refine submartingale_of_set_integral_le hadp hint (λ i j hij s hs, _),
  classical,
  specialize hf (s.piecewise (λ _, i) (λ _, j)) _
    (is_stopping_time_piecewise_const hij hs)
    (is_stopping_time_const 𝒢 j) (λ x, (ite_le_sup _ _ _).trans (max_eq_right hij).le)
    ⟨j, λ x, le_rfl⟩,
  rwa [stopped_value_const, stopped_value_piecewise_const,
    integral_piecewise (𝒢.le _ _ hs) (hint _).integrable_on (hint _).integrable_on,
    ← integral_add_compl (𝒢.le _ _ hs) (hint j), add_le_add_iff_right] at hf,
end

/-- **The optional stopping theorem** (fair game theorem): an adapted integrable process `f`
is a submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
lemma submartingale_iff_expected_stopped_value_mono [is_finite_measure μ]
  {f : ℕ → α → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ) :
  submartingale f 𝒢 μ ↔
  ∀ τ π : α → ℕ, is_stopping_time 𝒢 τ → is_stopping_time 𝒢 π → τ ≤ π → (∃ N, ∀ x, π x ≤ N) →
    μ[stopped_value f τ] ≤ μ[stopped_value f π] :=
⟨λ hf _ _ hτ hπ hle ⟨N, hN⟩, hf.expected_stopped_value_mono hτ hπ hle hN,
 submartingale_of_expected_stopped_value_mono hadp hint⟩

lemma submartingale.sum_mul_sub [is_finite_measure μ] {ξ f : ℕ → α → ℝ}
  (hf : submartingale f 𝒢 μ) (hξ : adapted 𝒢 ξ)
  (hbdd : ∃ R, ∀ n x, ξ n x ≤ R) (hnonneg : ∀ n x, 0 ≤ ξ n x) :
  submartingale (λ n : ℕ, ∑ k in finset.range n, ξ k * (f (k + 1) - f k)) 𝒢 μ :=
begin
  have hξbdd : ∀ i, ∃ (C : ℝ), ∀ (x : α), |ξ i x| ≤ C,
  { obtain ⟨C, hC⟩ := hbdd,
    intro i,
    refine ⟨C, λ x, abs_le.2 ⟨le_trans (neg_le.1 (le_trans _ (hC 0 x))) (hnonneg _ _), hC _ _⟩⟩,
    rw neg_zero,
    exact hnonneg 0 x },
  have hint : ∀ m, integrable (∑ k in finset.range m, ξ k * (f (k + 1) - f k)) μ :=
    λ m, integrable_finset_sum' _
      (λ i hi, integrable.bdd_mul ((hf.integrable _).sub (hf.integrable _))
      hξ.strongly_measurable.ae_strongly_measurable (hξbdd _)),
  have hadp : adapted 𝒢 (λ (n : ℕ), ∑ (k : ℕ) in finset.range n, ξ k * (f (k + 1) - f k)),
  { intro m,
    refine finset.strongly_measurable_sum' _ (λ i hi, _),
    rw finset.mem_range at hi,
    exact (hξ.strongly_measurable_le hi.le).mul
      ((hf.adapted.strongly_measurable_le (nat.succ_le_of_lt hi)).sub
      (hf.adapted.strongly_measurable_le hi.le)) },
  refine submartingale_of_condexp_sub_nonneg_nat hadp hint (λ i, _),
  simp only [← finset.sum_Ico_eq_sub _ (nat.le_succ _), finset.sum_apply, pi.mul_apply,
    pi.sub_apply, nat.Ico_succ_singleton, finset.sum_singleton],
  refine eventually_le.trans (eventually_le.mul_nonneg (eventually_of_forall (hnonneg _))
    (hf.condexp_sub_nonneg (nat.le_succ _))) (condexp_measurable_mul (hξ _)
    ((hf.integrable _).sub (hf.integrable _)) (((hf.integrable _).sub (hf.integrable _)).bdd_mul
    hξ.strongly_measurable.ae_strongly_measurable (hξbdd _))).symm.le,
end

/-- Given a discrete submartingale `f` and a predicatable process `ξ` (i.e. `ξ (n + 1)` is adapted)
the process defined by `λ n, ∑ k in finset.range n, ξ (k + 1) * (f (k + 1) - f k)` is also a
submartingale. -/
lemma submartingale.sum_mul_sub' [is_finite_measure μ] {ξ f : ℕ → α → ℝ}
  (hf : submartingale f 𝒢 μ) (hξ : adapted 𝒢 (λ n, ξ (n + 1)))
  (hbdd : ∃ R, ∀ n x, ξ n x ≤ R) (hnonneg : ∀ n x, 0 ≤ ξ n x) :
  submartingale (λ n : ℕ, ∑ k in finset.range n, ξ (k + 1) * (f (k + 1) - f k)) 𝒢 μ :=
let ⟨R, hR⟩ := hbdd in hf.sum_mul_sub hξ ⟨R, λ n, hR _⟩ (λ n, hnonneg _)

end nat

end measure_theory
