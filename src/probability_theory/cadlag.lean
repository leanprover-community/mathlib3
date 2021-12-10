/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.constructions.borel_space

noncomputable theory
open_locale classical measure_theory nnreal ennreal topological_space

variables {α β : Type*} [topological_space α] [partial_order α] [topological_space β]

open set filter

-- useful lemma: `continuous_within_at_Iio_iff_Iic`

/-- A function is said to be cadlag if it is right continuous with left limits. -/
def is_cadlag (f : α → β) : Prop :=
  ∀ a : α, continuous_within_at f (Ioi a) a ∧
  ∃ b : β, tendsto f (𝓝[Iic a] a) (𝓝 (b))

namespace is_cadlag

variables {f : α → β}

lemma continuous_with_at_Ioi (hf : is_cadlag f) (a : α) :
  continuous_within_at f (Ioi a) a :=
(hf a).1

lemma exist_tendsto_Iic (hf : is_cadlag f) (a : α) :
  ∃ b : β, tendsto f (𝓝[Iic a] a) (𝓝 (b)) :=
(hf a).2

lemma continuous_with_at_Ici (hf : is_cadlag f) (a : α) :
  continuous_within_at f (Ici a) a :=
continuous_within_at_Ioi_iff_Ici.1 (hf a).1

lemma exist_tendsto_Iio (hf : is_cadlag f) (a : α) :
  ∃ b : β, tendsto f (𝓝[Iio a] a) (𝓝 (b)) :=
let ⟨b, hb⟩ := hf.exist_tendsto_Iic a in
  ⟨b, tendsto_nhds_within_mono_left Iio_subset_Iic_self hb⟩

end is_cadlag

def skorokhod_space {α β : Type*} [topological_space α] [partial_order α] [topological_space β] :=
{f : α → β // is_cadlag f}
-- instance : normed_field ℝ := real.normed_field
