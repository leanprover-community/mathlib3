/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import measure_theory.function.special_functions.basic
import data.is_R_or_C.lemmas

/-!
# Measurability of the basic `is_R_or_C` functions

-/

noncomputable theory
open_locale nnreal ennreal


namespace is_R_or_C

variables {𝕜 : Type*} [is_R_or_C 𝕜]

@[measurability] lemma measurable_re : measurable (re : 𝕜 → ℝ) := continuous_re.measurable

@[measurability] lemma measurable_im : measurable (im : 𝕜 → ℝ) := continuous_im.measurable

end is_R_or_C

section is_R_or_C_composition

variables {α 𝕜 : Type*} [is_R_or_C 𝕜] {m : measurable_space α}
  {f : α → 𝕜} {μ : measure_theory.measure α}

include m

@[measurability] lemma measurable.re (hf : measurable f) : measurable (λ x, is_R_or_C.re (f x)) :=
is_R_or_C.measurable_re.comp hf

@[measurability] lemma ae_measurable.re (hf : ae_measurable f μ) :
  ae_measurable (λ x, is_R_or_C.re (f x)) μ :=
is_R_or_C.measurable_re.comp_ae_measurable hf

@[measurability] lemma measurable.im (hf : measurable f) : measurable (λ x, is_R_or_C.im (f x)) :=
is_R_or_C.measurable_im.comp hf

@[measurability] lemma ae_measurable.im (hf : ae_measurable f μ) :
  ae_measurable (λ x, is_R_or_C.im (f x)) μ :=
is_R_or_C.measurable_im.comp_ae_measurable hf

omit m

end is_R_or_C_composition

section

variables {α 𝕜 : Type*} [is_R_or_C 𝕜] [measurable_space α]
  {f : α → 𝕜} {μ : measure_theory.measure α}

@[measurability] lemma is_R_or_C.measurable_of_real : measurable (coe : ℝ → 𝕜) :=
is_R_or_C.continuous_of_real.measurable

lemma measurable_of_re_im
  (hre : measurable (λ x, is_R_or_C.re (f x)))
  (him : measurable (λ x, is_R_or_C.im (f x))) : measurable f :=
begin
  convert (is_R_or_C.measurable_of_real.comp hre).add
    ((is_R_or_C.measurable_of_real.comp him).mul_const is_R_or_C.I),
  { ext1 x,
    exact (is_R_or_C.re_add_im _).symm },
  all_goals { apply_instance },
end

lemma ae_measurable_of_re_im
  (hre : ae_measurable (λ x, is_R_or_C.re (f x)) μ)
  (him : ae_measurable (λ x, is_R_or_C.im (f x)) μ) : ae_measurable f μ :=
begin
  convert (is_R_or_C.measurable_of_real.comp_ae_measurable hre).add
    ((is_R_or_C.measurable_of_real.comp_ae_measurable him).mul_const is_R_or_C.I),
  { ext1 x,
    exact (is_R_or_C.re_add_im _).symm },
  all_goals { apply_instance },
end

end
