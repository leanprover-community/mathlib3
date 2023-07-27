/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import measure_theory.function.strongly_measurable.basic
import analysis.inner_product_space.basic

/-!
# Inner products of strongly measurable functions are strongly measurable.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

variables {α : Type*}
namespace measure_theory

/-! ## Strongly measurable functions -/

namespace strongly_measurable

protected lemma inner {𝕜 : Type*} {E : Type*}
  [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]
  {m : measurable_space α} {f g : α → E} (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (λ t, @inner 𝕜 _ _(f t) (g t)) :=
continuous.comp_strongly_measurable continuous_inner (hf.prod_mk hg)

end strongly_measurable

namespace ae_strongly_measurable

variables {m : measurable_space α} {μ : measure α} {𝕜 : Type*} {E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

protected lemma re {f : α → 𝕜} (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x, is_R_or_C.re (f x)) μ :=
is_R_or_C.continuous_re.comp_ae_strongly_measurable hf

protected lemma im {f : α → 𝕜} (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x, is_R_or_C.im (f x)) μ :=
is_R_or_C.continuous_im.comp_ae_strongly_measurable hf

protected lemma inner {m : measurable_space α} {μ : measure α} {f g : α → E}
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (λ x, ⟪f x, g x⟫) μ :=
continuous_inner.comp_ae_strongly_measurable (hf.prod_mk hg)

end ae_strongly_measurable

end measure_theory
