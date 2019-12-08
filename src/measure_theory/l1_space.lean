/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/

import measure_theory.ae_eq_fun

/-!
# Integrable functions and L1 space

In the first part of this file, the predicate `integrable` is defined and basic properties of
integrable functions are proved.

In the second part, the space L1 of equivalence classes of integrable functions under the relation
of being almost everywhere equal is defined as a subspace of the space L0. See the file
`src/measure_theory/ae_eq_fun.lean` for information on L0 space.

## Notation

* `α →₁ β` is the type of L1 space, where `α` is a `measure_space` and `β` is a `normed_group` with
  a `second_countable_topology`. `f : α →ₘ β` is a "function" in L1. In comments, `[f]` is also used
  to denote an L1 function.

  `₁` can be typed as `\1`.

## Main definitions

* Let `f : α → β` be a function, where `α` is a `measure_space` and `β` a `normed_group`.
  Then `f` is called `integrable` if `(∫⁻ a, nnnorm (f a)) < ⊤` holds.

* The space L1 is defined as a subspace of L0 :
  An `ae_eq_fun` `[f] : α →ₘ β` is in the space L1 if `edist [f] 0 < ⊤`, which means
  `(∫⁻ a, edist (f a) 0) < ⊤` if we expand the definition of `edist` in L0.

## Main statements

L1, as a subspace, inherits most of the structures of L0.

## Implementation notes

Maybe `integrable f` should be mean `(∫⁻ a, edist (f a) 0) < ⊤`, so that `integrable` and
`ae_eq_fun.integrable` are more aligned. But in the end one can use the lemma
`lintegral_nnnorm_eq_lintegral_edist : (∫⁻ a, nnnorm (f a)) = (∫⁻ a, edist (f a) 0)` to switch the
two forms.

## Tags

integrable, function space, l1

-/

noncomputable theory
open_locale classical topological_space

set_option class.instance_max_depth 100

namespace measure_theory
open set lattice filter topological_space ennreal emetric

universes u v w
variables {α : Type u} [measure_space α]
variables {β : Type v} [normed_group β]

/-- A function is `integrable` if the integral of its pointwise norm is less than infinity. -/
def integrable (f : α → β) : Prop := (∫⁻ a, nnnorm (f a)) < ⊤

lemma integrable_iff_norm (f : α → β) : integrable f ↔ (∫⁻ a, ennreal.of_real ∥f a∥) < ⊤ :=
have eq : (λa, ennreal.of_real ∥f a∥) = (λa, (nnnorm(f a) : ennreal)),
  by { funext, rw of_real_norm_eq_coe_nnnorm },
iff.intro (by { rw eq, exact λh, h }) $ by { rw eq, exact λh, h }

lemma integrable_iff_edist (f : α → β) : integrable f ↔ (∫⁻ a, edist (f a) 0) < ⊤ :=
have eq : (λa, edist (f a) 0) = (λa, (nnnorm(f a) : ennreal)),
  by { funext, rw edist_eq_coe_nnnorm },
iff.intro (by { rw eq, exact λh, h }) $ by { rw eq, exact λh, h }

lemma integrable_iff_of_real {f : α → ℝ} (h : ∀ₘ a, 0 ≤ f a) :
  integrable f ↔ (∫⁻ a, ennreal.of_real (f a)) < ⊤ :=
have lintegral_eq :  (∫⁻ a, ennreal.of_real ∥f a∥) = (∫⁻ a, ennreal.of_real (f a)) :=
begin
  apply lintegral_congr_ae,
  filter_upwards [h],
  simp only [mem_set_of_eq],
  assume a h,
  rw [real.norm_eq_abs, abs_of_nonneg],
  exact h
end,
by rw [integrable_iff_norm, lintegral_eq]

lemma integrable_of_ae_eq {f g : α → β} (hf : integrable f) (h : ∀ₘ a, f a = g a) : integrable g :=
begin
  simp only [integrable] at *,
  have : (∫⁻ (a : α), ↑(nnnorm (f a))) = (∫⁻ (a : α), ↑(nnnorm (g a))),
  { apply lintegral_congr_ae,
    filter_upwards [h],
    assume a,
    simp only [mem_set_of_eq],
    assume h,
    rw h },
  rwa ← this
end

lemma integrable_iff_of_ae_eq {f g : α → β} (h : ∀ₘ a, f a = g a) : integrable f ↔ integrable g :=
iff.intro (λhf, integrable_of_ae_eq hf h) (λhg, integrable_of_ae_eq hg (all_ae_eq_symm h))

lemma integrable_of_ae_le {f g : α → ℝ} (h : ∀ₘ a, ∥f a∥ ≤ ∥g a∥) (hg : integrable g) : integrable f :=
begin
  simp only [integrable_iff_norm] at *,
  calc (∫⁻ a, ennreal.of_real ∥f a∥) ≤ (∫⁻ (a : α), ennreal.of_real ∥g a∥) :
    lintegral_le_lintegral_ae (by { filter_upwards [h], assume a h, exact of_real_le_of_real h })
    ... < ⊤ : hg
end

lemma lintegral_nnnorm_eq_lintegral_edist (f : α → β) :
  (∫⁻ a, nnnorm (f a)) = ∫⁻ a, edist (f a) 0 :=
by { congr, funext, rw edist_eq_coe_nnnorm }

lemma lintegral_norm_eq_lintegral_edist (f : α → β) :
  (∫⁻ a, ennreal.of_real ∥f a∥) = ∫⁻ a, edist (f a) 0 :=
by { congr, funext, rw [of_real_norm_eq_coe_nnnorm, edist_eq_coe_nnnorm] }

lemma lintegral_edist_triangle [second_countable_topology β] {f g h : α → β}
  (hf : measurable f) (hg : measurable g) (hh : measurable h) :
  (∫⁻ a, edist (f a) (g a)) ≤ (∫⁻ a, edist (f a) (h a)) + ∫⁻ a, edist (g a) (h a) :=
begin
  rw ← lintegral_add (measurable_edist hf hh) (measurable_edist hg hh),
  apply lintegral_le_lintegral,
  assume a,
  have := edist_triangle (f a) (h a) (g a),
  convert this,
  rw edist_comm (h a) (g a),
end

lemma lintegral_edist_lt_top [second_countable_topology β] {f g : α → β}
  (hfm : measurable f) (hfi : integrable f) (hgm : measurable g) (hgi : integrable g) :
  (∫⁻ a, edist (f a) (g a)) < ⊤ :=
lt_of_le_of_lt
  (lintegral_edist_triangle hfm hgm (measurable_const : measurable (λa, (0 : β))))
  (ennreal.add_lt_top.2 $ by { split; rw ← integrable_iff_edist; assumption })

@[simp] lemma lintegral_nnnorm_zero : (∫⁻ a : α, nnnorm (0 : β)) = 0 := by simp

lemma integrable_zero : integrable (0 : α → β) :=
by { have := coe_lt_top, simpa [integrable] }

lemma lintegral_nnnorm_add {f g : α → β} (hf : measurable f) (hg : measurable g) :
  (∫⁻ a, nnnorm (f a) + nnnorm (g a)) = (∫⁻ a, nnnorm (f a)) + ∫⁻ a, nnnorm (g a) :=
lintegral_add (measurable_coe_nnnorm hf) (measurable_coe_nnnorm hg)

lemma integrable_add {f g : α → β} (hfm : measurable f) (hgm : measurable g) :
  integrable f → integrable g → integrable (f + g) :=
assume hfi hgi,
  calc
    (∫⁻ (a : α), ↑(nnnorm ((f + g) a))) ≤ ∫⁻ (a : α), ↑(nnnorm (f a)) + ↑(nnnorm (g a)) :
      lintegral_le_lintegral _ _
        (assume a, by { simp only [coe_add.symm, coe_le_coe], exact nnnorm_add_le _ _ })
    ... = _ :
      lintegral_nnnorm_add hfm hgm
    ... < ⊤ : add_lt_top.2 ⟨hfi, hgi⟩

lemma lintegral_nnnorm_neg {f : α → β} :
  (∫⁻ (a : α), ↑(nnnorm ((-f) a))) = ∫⁻ (a : α), ↑(nnnorm ((f) a)) :=
lintegral_congr_ae $ by { filter_upwards [], simp }

lemma integrable_neg {f : α → β} : integrable f → integrable (-f) :=
assume hfi, calc _ = _ : lintegral_nnnorm_neg
                 ... < ⊤ : hfi

lemma integrable_neg_iff (f : α → β) : integrable (-f) ↔ integrable f :=
begin
  split,
  { assume h,
    have := integrable_neg h,
    rwa _root_.neg_neg at this },
  exact integrable_neg
end

lemma integrable_sub {f g : α → β} (hf : measurable f) (hg : measurable g) :
  integrable f → integrable g → integrable (f - g) :=
λ hfi hgi,
  by { rw sub_eq_add_neg, refine integrable_add hf (measurable_neg hg) hfi (integrable_neg hgi) }

lemma integrable_norm {f : α → β} (hfi : integrable f) : integrable (λa, ∥f a∥) :=
have eq : (λa, (nnnorm ∥f a∥ : ennreal)) = λa, (nnnorm (f a) : ennreal),
  by { funext, rw nnnorm_norm },
by { rwa [integrable, eq] }

lemma integrable_norm_iff (f : α → β) : integrable (λa, ∥f a∥) ↔ integrable f :=
have eq : (λa, (nnnorm ∥f a∥ : ennreal)) = λa, (nnnorm (f a) : ennreal),
  by { funext, rw nnnorm_norm },
by { rw [integrable, integrable, eq] }

lemma integrable_of_integrable_bound {f : α → β} {bound : α → ℝ} (h : integrable bound)
  (h_bound : ∀ₘ a, ∥f a∥ ≤ bound a) : integrable f :=
have h₁ : ∀ₘ a, (nnnorm (f a) : ennreal) ≤ ennreal.of_real (bound a),
begin
  filter_upwards [h_bound],
  simp only [mem_set_of_eq],
  assume a h,
  calc (nnnorm (f a) : ennreal) = ennreal.of_real (∥f a∥) : by rw of_real_norm_eq_coe_nnnorm
    ... ≤ ennreal.of_real (bound a) : ennreal.of_real_le_of_real h
end,
calc (∫⁻ a, nnnorm (f a)) ≤ (∫⁻ a, ennreal.of_real (bound a)) :
    by { apply lintegral_le_lintegral_ae, exact h₁ }
  ... ≤ (∫⁻ a, ennreal.of_real ∥bound a∥) : lintegral_le_lintegral _ _ $
    by { assume a, apply ennreal.of_real_le_of_real, exact le_max_left (bound a) (-bound a) }
  ... < ⊤ : by { rwa [integrable_iff_norm] at h }

section dominated_convergence

variables {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}

lemma all_ae_of_real_F_le_bound (h : ∀ n, ∀ₘ a, ∥F n a∥ ≤ bound a) :
  ∀ n, ∀ₘ a, ennreal.of_real ∥F n a∥ ≤ ennreal.of_real (bound a) :=
λn, by filter_upwards [h n] λ a h, ennreal.of_real_le_of_real h

lemma all_ae_tendsto_of_real_norm (h : ∀ₘ a, tendsto (λ n, F n a) at_top $ 𝓝 $ f a) :
  ∀ₘ a, tendsto (λn, ennreal.of_real ∥F n a∥) at_top $ 𝓝 $ ennreal.of_real ∥f a∥ :=
by filter_upwards [h]
  λ a h, tendsto_of_real $ tendsto.comp (continuous.tendsto continuous_norm _) h

lemma all_ae_of_real_f_le_bound (h_bound : ∀ n, ∀ₘ a, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ₘ a, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  ∀ₘ a, ennreal.of_real ∥f a∥ ≤ ennreal.of_real (bound a) :=
begin
  have F_le_bound := all_ae_of_real_F_le_bound h_bound,
  rw ← all_ae_all_iff at F_le_bound,
  filter_upwards [all_ae_tendsto_of_real_norm h_lim, F_le_bound],
  assume a tendsto_norm F_le_bound,
  refine le_of_tendsto at_top_ne_bot tendsto_norm _,
  simp only [mem_at_top_sets, ge_iff_le, mem_set_of_eq, preimage_set_of_eq, nonempty_of_inhabited],
  use 0,
  assume n hn,
  exact F_le_bound n
end

lemma integrable_of_dominated_convergence {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  (bound_integrable : integrable bound)
  (h_bound : ∀ n, ∀ₘ a, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ₘ a, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  integrable f :=
/- `∥F n a∥ ≤ bound a` and `∥F n a∥ --> ∥f a∥` implies `∥f a∥ ≤ bound a`,
  and so `∫ ∥f∥ ≤ ∫ bound < ⊤` since `bound` is integrable -/
begin
  rw integrable_iff_norm,
  calc (∫⁻ a, (ennreal.of_real ∥f a∥)) ≤ ∫⁻ a, ennreal.of_real (bound a) :
    lintegral_le_lintegral_ae $ all_ae_of_real_f_le_bound h_bound h_lim
    ... < ⊤ :
    begin
      rw ← integrable_iff_of_real,
      { exact bound_integrable },
      filter_upwards [h_bound 0] λ a h, le_trans (norm_nonneg _) h,
    end
end

lemma tendsto_lintegral_norm_of_dominated_convergence [second_countable_topology β]
  {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  (F_measurable : ∀ n, measurable (F n))
  (f_measurable : measurable f)
  (bound_integrable : integrable bound)
  (h_bound : ∀ n, ∀ₘ a, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ₘ a, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, ennreal.of_real ∥F n a - f a∥) at_top (𝓝 0) :=
let b := λa, 2 * ennreal.of_real (bound a) in
/- `∥F n a∥ ≤ bound a` and `F n a --> f a` implies `∥f a∥ ≤ bound a`, and thus by the
  triangle inequality, have `∥F n a - f a∥ ≤ 2 * (bound a). -/
have hb : ∀ n, ∀ₘ a, ennreal.of_real ∥F n a - f a∥ ≤ b a,
begin
  assume n,
  filter_upwards [all_ae_of_real_F_le_bound h_bound n, all_ae_of_real_f_le_bound h_bound h_lim],
  assume a h₁ h₂,
  calc ennreal.of_real ∥F n a - f a∥ ≤ (ennreal.of_real ∥F n a∥) + (ennreal.of_real ∥f a∥) :
  begin
    rw [← ennreal.of_real_add],
    apply of_real_le_of_real,
    { apply norm_sub_le }, { exact norm_nonneg _ }, { exact norm_nonneg _ }
  end
    ... ≤ (ennreal.of_real (bound a)) + (ennreal.of_real (bound a)) : add_le_add' h₁ h₂
    ... = b a : by rw ← two_mul
end,
/- On the other hand, `F n a --> f a` implies that `∥F n a - f a∥ --> 0`  -/
have h : ∀ₘ a, tendsto (λ n, ennreal.of_real ∥F n a - f a∥) at_top (𝓝 0),
begin
  suffices h : ∀ₘ a, tendsto (λ n, ennreal.of_real ∥F n a - f a∥) at_top (𝓝 $ ennreal.of_real 0),
  { rwa ennreal.of_real_zero at h },
  filter_upwards [h_lim],
  assume a h,
  refine tendsto.comp (continuous.tendsto continuous_of_real _) _,
  rw ← tendsto_iff_norm_tendsto_zero,
  exact h
end,
/- Therefore, by the dominated convergence theorem for nonnegative integration, have
  ` ∫ ∥f a - F n a∥ --> 0 ` -/
begin
  suffices h : tendsto (λn, ∫⁻ a, ennreal.of_real ∥F n a - f a∥) at_top (𝓝 (∫⁻ (a:α), 0)),
  { rwa lintegral_zero at h },
  -- Using the dominated convergence theorem.
  refine tendsto_lintegral_of_dominated_convergence _ hb _ _,
  -- Show `λa, ∥f a - F n a∥` is measurable for all `n`
  { exact λn, measurable.comp measurable_of_real (measurable_norm (measurable_sub (F_measurable n)
      f_measurable)) },
  -- Show `2 * bound` is integrable
  { rw integrable_iff_of_real at bound_integrable,
    { calc (∫⁻ a, b a) = 2 * (∫⁻ a, ennreal.of_real (bound a)) :
        by { rw lintegral_const_mul', exact coe_ne_top }
        ... < ⊤ : mul_lt_top (coe_lt_top) bound_integrable },
    filter_upwards [h_bound 0] λ a h, le_trans (norm_nonneg _) h },
  -- Show `∥f a - F n a∥ --> 0`
  { exact h }
end

end dominated_convergence

section pos_part
/-! Lemmas used for defining the positive part of a L1 function -/

lemma integrable_max_zero {f : α → ℝ} (hf : integrable f) : integrable (λa, max (f a) 0) :=
begin
  simp only [integrable_iff_norm] at *,
  calc (∫⁻ a, ennreal.of_real ∥max (f a) 0∥) ≤ (∫⁻ (a : α), ennreal.of_real ∥f a∥) :
    lintegral_le_lintegral _ _
    begin
      assume a,
      apply of_real_le_of_real,
      simp only [real.norm_eq_abs],
      calc abs (max (f a) 0) = max (f a) 0 : by { rw abs_of_nonneg, apply le_max_right }
        ... ≤ abs (f a) : max_le (le_abs_self _) (abs_nonneg _)
    end
    ... < ⊤ : hf
end

lemma integrable_min_zero {f : α → ℝ} (hf : integrable f) : integrable (λa, min (f a) 0) :=
begin
  have : (λa, min (f a) 0) = (λa, - max (-f a) 0),
  { funext, rw [min_eq_neg_max_neg_neg, neg_zero] },
  rw this,
  exact integrable_neg (integrable_max_zero $ integrable_neg hf),
end

end pos_part

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma integrable_smul (c : 𝕜) {f : α → β} : integrable f → integrable (c • f) :=
begin
  simp only [integrable], assume hfi,
  calc
    (∫⁻ (a : α), nnnorm ((c • f) a)) = (∫⁻ (a : α), (nnnorm c) * nnnorm (f a)) :
    begin
      apply lintegral_congr_ae,
      filter_upwards [],
      assume a,
      simp only [nnnorm_smul, set.mem_set_of_eq, pi.smul_apply, ennreal.coe_mul]
    end
    ... < ⊤ :
    begin
      rw lintegral_const_mul',
      apply mul_lt_top,
      { exact coe_lt_top },
      { exact hfi },
      { simp only [ennreal.coe_ne_top, ne.def, not_false_iff] }
    end
end

lemma integrable_smul_iff {c : 𝕜} (hc : c ≠ 0) (f : α → β) : integrable (c • f) ↔ integrable f :=
begin
  split,
  { assume h,
    have := integrable_smul c⁻¹ h,
    rwa [smul_smul, inv_mul_cancel hc, one_smul] at this },
  exact integrable_smul _
end

end normed_space

variables [second_countable_topology β]

namespace ae_eq_fun

/-- An almost everywhere equal function is `integrable` if it has a finite distance to the origin.
  Should mean the same thing as the predicate `integrable` over functions. -/
def integrable (f : α →ₘ β) : Prop := f ∈ ball (0 : α →ₘ β) ⊤

lemma integrable_mk (f : α → β) (hf : measurable f) :
  (integrable (mk f hf)) ↔ measure_theory.integrable f :=
by simp [integrable, zero_def, edist_mk_mk', measure_theory.integrable, nndist_eq_nnnorm]

lemma integrable_to_fun (f : α →ₘ β) : integrable f ↔ (measure_theory.integrable f.to_fun) :=
by conv_lhs { rw [self_eq_mk f, integrable_mk] }

local attribute [simp] integrable_mk

lemma integrable_zero : integrable (0 : α →ₘ β) := mem_ball_self coe_lt_top

lemma integrable_add : ∀ {f g : α →ₘ β}, integrable f → integrable g → integrable (f + g) :=
begin
  rintros ⟨f, hf⟩ ⟨g, hg⟩,
  have := measure_theory.integrable_add hf hg,
  simpa [mem_ball, zero_def]
end

lemma integrable_neg : ∀ {f : α →ₘ β}, integrable f → integrable (-f) :=
by { rintros ⟨f, hf⟩, have := measure_theory.integrable_neg, simpa }

lemma integrable_sub : ∀ {f g : α →ₘ β}, integrable f → integrable g → integrable (f - g) :=
by { rintros ⟨f, hf⟩ ⟨g, hg⟩, have := measure_theory.integrable_sub hf hg, simpa [mem_ball, zero_def] }

protected lemma is_add_subgroup : is_add_subgroup (ball (0 : α →ₘ β) ⊤) :=
{ zero_mem := integrable_zero,
  add_mem := λ _ _, integrable_add,
  neg_mem := λ _, integrable_neg }

section normed_space
variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma integrable_smul : ∀ {c : 𝕜} {f : α →ₘ β}, integrable f → integrable (c • f) :=
by { assume c, rintros ⟨f, hf⟩, simpa using integrable_smul _ }

end normed_space

end ae_eq_fun

section
variables (α β)

/-- The space of equivalence classes of integrable (and measurable) functions, where two integrable
    functions are equivalent if they agree almost everywhere, i.e., they differ on a set of measure
    `0`. -/
def l1 : Type* := subtype (@ae_eq_fun.integrable α _ β _ _)

infixr ` →₁ `:25 := l1

end

namespace l1
open ae_eq_fun
local attribute [instance] ae_eq_fun.is_add_subgroup

instance : has_coe (α →₁ β) (α →ₘ β) := ⟨subtype.val⟩

protected lemma eq {f g : α →₁ β} : (f : α →ₘ β) = (g : α →ₘ β) → f = g := subtype.eq
@[elim_cast] protected lemma eq_iff {f g : α →₁ β} : (f : α →ₘ β) = (g : α →ₘ β) ↔ f = g :=
iff.intro (l1.eq) (congr_arg coe)

/- TODO : order structure of l1-/

/-- L1 space forms a `emetric_space`, with the emetric being inherited from almost everywhere
  functions, i.e., `edist f g = ∫⁻ a, edist (f a) (g a)`. -/
instance : emetric_space (α →₁ β) := subtype.emetric_space

/-- L1 space forms a `metric_space`, with the metric being inherited from almost everywhere
  functions, i.e., `edist f g = ennreal.to_real (∫⁻ a, edist (f a) (g a))`. -/
instance : metric_space (α →₁ β) := metric_space_emetric_ball 0 ⊤
instance : add_comm_group (α →₁ β) := subtype.add_comm_group

@[simp] lemma coe_zero : ((0 : α →₁ β) : α →ₘ β) = 0 := rfl
@[simp] lemma coe_add (f g : α →₁ β) : ((f + g : α →₁ β) : α →ₘ β) = f + g := rfl
@[simp] lemma coe_neg (f : α →₁ β) : ((-f : α →₁ β) : α →ₘ β) = -f := rfl
@[simp] lemma coe_sub (f g : α →₁ β) : ((f - g : α →₁ β) : α →ₘ β) = f - g := rfl
@[simp] lemma edist_eq (f g : α →₁ β) : edist f g = edist (f : α →ₘ β) (g : α →ₘ β) := rfl

lemma dist_eq (f g : α →₁ β) : dist f g = ennreal.to_real (edist (f : α →ₘ β) (g : α →ₘ β)) := rfl

/-- The norm on L1 space is defined to be `∥f∥ = ∫⁻ a, edist (f a) 0`. -/
instance : has_norm (α →₁ β) := ⟨λ f, dist f 0⟩

lemma norm_eq (f : α →₁ β) : ∥f∥ = ennreal.to_real (edist (f : α →ₘ β) 0) := rfl

instance : normed_group (α →₁ β) := normed_group.of_add_dist (λ x, rfl) $ by
{ intros, simp only [dist_eq, coe_add], rw edist_eq_add_add }

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

instance : has_scalar 𝕜 (α →₁ β) := ⟨λ x f, ⟨x • (f : α →ₘ β), ae_eq_fun.integrable_smul f.2⟩⟩

@[simp] lemma coe_smul (c : 𝕜) (f : α →₁ β) : ((c • f : α →₁ β) : α →ₘ β) = c • (f : α →ₘ β) := rfl

instance : semimodule 𝕜 (α →₁ β) :=
{ one_smul  := λf, l1.eq (by { simp only [coe_smul], exact one_smul _ _ }),
  mul_smul  := λx y f, l1.eq (by { simp only [coe_smul], exact mul_smul _ _ _ }),
  smul_add  := λx f g, l1.eq (by { simp only [coe_smul, coe_add], exact smul_add _ _ _ }),
  smul_zero := λx, l1.eq (by { simp only [coe_zero, coe_smul], exact smul_zero _ }),
  add_smul  := λx y f, l1.eq (by { simp only [coe_smul], exact add_smul _ _ _ }),
  zero_smul := λf, l1.eq (by { simp only [coe_smul], exact zero_smul _ _ }) }

instance : module 𝕜 (α →₁ β) := { .. l1.semimodule }

instance : vector_space 𝕜 (α →₁ β) := { .. l1.semimodule }

instance : normed_space 𝕜 (α →₁ β) :=
⟨ begin
    rintros x ⟨f, hf⟩,
    show ennreal.to_real (edist (x • f) 0) = ∥x∥ * ennreal.to_real (edist f 0),
    rw [edist_smul, to_real_of_real_mul],
    exact norm_nonneg _
  end ⟩

end normed_space

section of_fun

/-- Construct the equivalence class `[f]` of a measurable and integrable function `f`. -/
def of_fun (f : α → β) (hfm : measurable f) (hfi : integrable f) : (α →₁ β) :=
⟨mk f hfm, by { rw integrable_mk, exact hfi }⟩

lemma of_fun_eq_mk (f : α → β) (hfm hfi) : (of_fun f hfm hfi : α →ₘ β) = mk f hfm := rfl

lemma of_fun_eq_of_fun (f g : α → β) (hfm hfi hgm hgi) :
  of_fun f hfm hfi = of_fun g hgm hgi ↔ ∀ₘ a, f a = g a :=
by { rw ← l1.eq_iff, simp only [of_fun_eq_mk, mk_eq_mk] }

lemma of_fun_zero : of_fun (0 : α → β) (@measurable_const _ _ _ _ (0:β)) integrable_zero = 0 := rfl

lemma of_fun_add (f g : α → β) (hfm hfi hgm hgi) :
  of_fun (f + g) (measurable_add hfm hgm) (integrable_add hfm hgm hfi hgi)
    = of_fun f hfm hfi + of_fun g hgm hgi :=
rfl

lemma of_fun_neg (f : α → β) (hfm hfi) :
  of_fun (-f) (measurable_neg hfm) (integrable_neg hfi) = - of_fun f hfm hfi := rfl

lemma of_fun_sub (f g : α → β) (hfm hfi hgm hgi) :
  of_fun (f - g) (measurable_sub hfm hgm) (integrable_sub hfm hgm hfi hgi)
    = of_fun f hfm hfi - of_fun g hgm hgi :=
rfl

lemma norm_of_fun (f : α → β) (hfm hfi) : ∥of_fun f hfm hfi∥ = ennreal.to_real (∫⁻ a, edist (f a) 0) :=
rfl

lemma norm_of_fun_eq_lintegral_norm (f : α → β) (hfm hfi) :
  ∥of_fun f hfm hfi∥ = ennreal.to_real (∫⁻ a, ennreal.of_real ∥f a∥) :=
by { rw [norm_of_fun, lintegral_norm_eq_lintegral_edist] }

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma of_fun_smul (f : α → β) (hfm hfi) (k : 𝕜) :
  of_fun (k • f) (measurable_smul _ hfm) (integrable_smul _ hfi) = k • of_fun f hfm hfi := rfl

end of_fun

section to_fun

/-- Find a representative of a L1 function [f] -/
@[reducible]
protected def to_fun (f : α →₁ β) : α → β := (f : α →ₘ β).to_fun

protected lemma measurable (f : α →₁ β) : measurable f.to_fun := f.1.measurable

protected lemma integrable (f : α →₁ β) : integrable f.to_fun :=
by { rw [l1.to_fun, ← integrable_to_fun], exact f.2 }

lemma of_fun_to_fun (f : α →₁ β) : of_fun (f.to_fun) f.measurable f.integrable = f :=
begin
  rcases f with ⟨f, hfi⟩,
  rw [of_fun, subtype.mk_eq_mk],
  exact (self_eq_mk f).symm
end

lemma mk_to_fun (f : α →₁ β) : mk (f.to_fun) f.measurable = f :=
by { rw ← of_fun_eq_mk, rw l1.eq_iff, exact of_fun_to_fun f }

lemma to_fun_of_fun (f : α → β) (hfm hfi) : ∀ₘ a, (of_fun f hfm hfi).to_fun a = f a :=
begin
  filter_upwards [all_ae_mk_to_fun f hfm],
  assume a,
  simp only [mem_set_of_eq],
  assume h,
  rw ← h,
  refl
end

variables (α β)
lemma zero_to_fun : ∀ₘ a, (0 : α →₁ β).to_fun a = 0 := ae_eq_fun.zero_to_fun
variables {α β}

lemma add_to_fun (f g : α →₁ β) : ∀ₘ a, (f + g).to_fun a = f.to_fun a + g.to_fun a :=
ae_eq_fun.add_to_fun _ _

lemma neg_to_fun (f : α →₁ β) : ∀ₘ a, (-f).to_fun a = -f.to_fun a := ae_eq_fun.neg_to_fun _

lemma sub_to_fun (f g : α →₁ β) : ∀ₘ a, (f - g).to_fun a = f.to_fun a - g.to_fun a :=
ae_eq_fun.sub_to_fun _ _

lemma dist_to_fun (f g : α →₁ β) : dist f g = ennreal.to_real (∫⁻ x, edist (f.to_fun x) (g.to_fun x)) :=
by { simp only [dist_eq, edist_to_fun] }

lemma norm_eq_nnnorm_to_fun (f : α →₁ β) : ∥f∥ = ennreal.to_real (∫⁻ a, nnnorm (f.to_fun a)) :=
by { rw [lintegral_nnnorm_eq_lintegral_edist, ← edist_zero_to_fun], refl }

lemma norm_eq_norm_to_fun (f : α →₁ β) : ∥f∥ = ennreal.to_real (∫⁻ a, ennreal.of_real ∥f.to_fun a∥) :=
by { rw norm_eq_nnnorm_to_fun, congr, funext, rw of_real_norm_eq_coe_nnnorm }

lemma lintegral_edist_to_fun_lt_top (f g : α →₁ β) : (∫⁻ a, edist (f.to_fun a) (g.to_fun a)) < ⊤ :=
begin
  apply lintegral_edist_lt_top,
  exact f.measurable, exact f.integrable, exact g.measurable, exact g.integrable
end

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

lemma smul_to_fun (c : 𝕜) (f : α →₁ β) : ∀ₘ a, (c • f).to_fun a = c • f.to_fun a :=
ae_eq_fun.smul_to_fun _ _

end to_fun

section pos_part

/-- Positive part of a function in L1 space. -/
def pos_part (f : α →₁ ℝ) : α →₁ ℝ :=
⟨ ae_eq_fun.pos_part f,
  begin
    rw [ae_eq_fun.integrable_to_fun, integrable_iff_of_ae_eq (pos_part_to_fun _)],
    exact integrable_max_zero f.integrable
  end ⟩

/-- Negative part of a function in L1 space. -/
def neg_part (f : α →₁ ℝ) : α →₁ ℝ := pos_part (-f)

@[move_cast] lemma coe_pos_part (f : α →₁ ℝ) : (f.pos_part : α →ₘ ℝ) = (f : α →ₘ ℝ).pos_part := rfl

lemma pos_part_to_fun (f : α →₁ ℝ) : ∀ₘ a, (pos_part f).to_fun a = max (f.to_fun a) 0 :=
ae_eq_fun.pos_part_to_fun _

lemma neg_part_to_fun_eq_max (f : α →₁ ℝ) : ∀ₘ a, (neg_part f).to_fun a = max (- f.to_fun a) 0 :=
begin
  rw neg_part,
  filter_upwards [pos_part_to_fun (-f), neg_to_fun f],
  simp only [mem_set_of_eq],
  assume a h₁ h₂,
  rw [h₁, h₂]
end

lemma neg_part_to_fun_eq_min (f : α →₁ ℝ) : ∀ₘ a, (neg_part f).to_fun a = - min (f.to_fun a) 0 :=
begin
  filter_upwards [neg_part_to_fun_eq_max f],
  simp only [mem_set_of_eq],
  assume a h,
  rw [h, min_eq_neg_max_neg_neg, _root_.neg_neg, neg_zero],
end

lemma norm_le_norm_of_ae_le {f g : α →₁ β} (h : ∀ₘ a, ∥f.to_fun a∥ ≤ ∥g.to_fun a∥) : ∥f∥ ≤ ∥g∥ :=
begin
  simp only [l1.norm_eq_norm_to_fun],
  rw to_real_le_to_real,
  { apply lintegral_le_lintegral_ae,
    filter_upwards [h],
    simp only [mem_set_of_eq],
    assume a h,
    exact of_real_le_of_real h },
  { rw [← lt_top_iff_ne_top, ← integrable_iff_norm], exact f.integrable },
  { rw [← lt_top_iff_ne_top, ← integrable_iff_norm], exact g.integrable }
end

lemma continuous_pos_part : continuous $ λf : α →₁ ℝ, pos_part f :=
begin
  simp only [metric.continuous_iff],
  assume g ε hε,
  use ε, use hε,
  simp only [dist_eq_norm],
  assume f hfg,
  refine lt_of_le_of_lt (norm_le_norm_of_ae_le _) hfg,
  filter_upwards [l1.sub_to_fun f g, l1.sub_to_fun (pos_part f) (pos_part g),
    pos_part_to_fun f, pos_part_to_fun g],
  simp only [mem_set_of_eq],
  assume a h₁ h₂ h₃ h₄,
  simp only [real.norm_eq_abs, h₁, h₂, h₃, h₄],
  exact abs_max_sub_max_le_abs _ _ _
end

lemma continuous_neg_part : continuous $ λf : α →₁ ℝ, neg_part f :=
have eq : (λf : α →₁ ℝ, neg_part f) = (λf : α →₁ ℝ, pos_part (-f)) := rfl,
by { rw eq, exact continuous_pos_part.comp continuous_neg }

end pos_part

/- TODO: l1 is a complete space -/

end l1

end measure_theory

#lint
