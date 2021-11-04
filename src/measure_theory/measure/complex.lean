/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/

import measure_theory.decomposition.jordan

/-!
# Complex measure

This file proves some elementary results about complex measures. In particular, we prove that
a complex measure is always in the form `s + it` where `s` and `t` are signed measures.

## Main definitions

* `measure_theory.complex_measure.re_part`: obtains a signed measure `s` from a complex measure `c`
  such that `s i = (c i).re` for all measurable sets `i`.
* `measure_theory.complex_measure.im_part`: obtains a signed measure `s` from a complex measure `c`
  such that `s i = (c i).im` for all measurable sets `i`.
* `measure_theory.signed_measure.to_complex_measure`: given two signed measures `s` and `t`,
  `s.to_complex_measure t` provides a complex measure of the form `s + it`.
* `measure_theory.complex_measure.equiv_signed_measure`: is the equivalence between the complex
  measures and the type of the product of the signed measures with itself.

# Tags

Complex measure
-/

noncomputable theory
open_locale classical measure_theory ennreal nnreal

variables {α β : Type*} {m : measurable_space α}

namespace measure_theory

open vector_measure

namespace complex_measure

include m

/-- The real part of a complex measure is a signed measure. -/
@[simps]
def re_part (c : complex_measure α) : signed_measure α :=
{ measure_of' := λ i, (c i).re,
  empty' := by simp only [c.empty, complex.zero_re],
  not_measurable' := λ i hi, by simp only [c.not_measurable hi, complex.zero_re],
  m_Union' := λ f hfm hfdisj, (c.m_Union hfm hfdisj).mapL complex.re_clm }

lemma re_part_add (c d : complex_measure α) :
  (c + d).re_part = c.re_part + d.re_part :=
rfl

/-- The imaginary part of a complex measure is a signed measure. -/
@[simps]
def im_part (c : complex_measure α) : signed_measure α :=
{ measure_of' := λ i, (c i).im,
  empty' := by simp only [c.empty, complex.zero_im],
  not_measurable' := λ i hi, by simp only [c.not_measurable hi, complex.zero_im],
  m_Union' := λ f hfm hfdisj, (c.m_Union hfm hfdisj).mapL complex.im_clm }

lemma im_part_add (c d : complex_measure α) :
  (c + d).im_part = c.im_part + d.im_part :=
rfl

/-- Given `s` and `t` signed measures, `s + it` is a complex measure-/
@[simps]
def _root_.measure_theory.signed_measure.to_complex_measure (s t : signed_measure α) :
  complex_measure α :=
{ measure_of' := λ i, ⟨s i, t i⟩,
  empty' := by rw [s.empty, t.empty]; refl,
  not_measurable' := λ i hi, by rw [s.not_measurable hi, t.not_measurable hi]; refl,
  m_Union' := λ f hf hfdisj,
    (complex.has_sum_iff _ _).2 ⟨s.m_Union hf hfdisj, t.m_Union hf hfdisj⟩ }

lemma _root_.measure_theory.signed_measure.to_complex_measure_apply
  {s t : signed_measure α} {i : set α} : s.to_complex_measure t i = ⟨s i, t i⟩ := rfl

lemma to_complex_measure_to_signed_measure (c : complex_measure α) :
  c.re_part.to_complex_measure c.im_part = c :=
by { ext i hi; refl }

lemma _root_.measure_theory.signed_measure.re_part_to_complex_measure
  (s t : signed_measure α) : (s.to_complex_measure t).re_part = s :=
by { ext i hi, refl }

lemma _root_.measure_theory.signed_measure.im_part_to_complex_measure
  (s t : signed_measure α) : (s.to_complex_measure t).im_part = t :=
by { ext i hi, refl }

/-- The complex measures form an equivalence to the type of pairs of signed measures. -/
@[simps]
def equiv_signed_measure : complex_measure α ≃ signed_measure α × signed_measure α :=
{ to_fun := λ c, ⟨c.re_part, c.im_part⟩,
  inv_fun := λ ⟨s, t⟩, s.to_complex_measure t,
  left_inv := λ c, c.to_complex_measure_to_signed_measure,
  right_inv := λ ⟨s, t⟩,
    prod.mk.inj_iff.2 ⟨s.re_part_to_complex_measure t, s.im_part_to_complex_measure t⟩ }

section

variables {R : Type*} [semiring R] [module R ℝ]
variables [topological_space R] [has_continuous_smul R ℝ] [has_continuous_smul R ℂ]

/-- The complex measures form an linear isomorphism to the type of pairs of signed measures. -/
@[simps]
def equiv_signed_measureₗ : complex_measure α ≃ₗ[R] signed_measure α × signed_measure α :=
{ map_add' := λ c d, by { ext i hi; refl },
  map_smul' :=
  begin
    intros r c, ext i hi,
    { change (r • c i).re = r • (c i).re,
      simp [complex.smul_re] },
    { ext i hi,
      change (r • c i).im = r • (c i).im,
      simp [complex.smul_im] }
  end, .. equiv_signed_measure }

end

lemma absolutely_continuous_ennreal_iff (c : complex_measure α) (μ : vector_measure α ℝ≥0∞) :
  c ≪ᵥ μ ↔ c.re_part ≪ᵥ μ ∧ c.im_part ≪ᵥ μ :=
begin
  split; intro h,
  { split; { intros i hi, simp [h hi] } },
  { intros i hi,
    rw [← complex.re_add_im (c i), (_ : (c i).re = 0), (_ : (c i).im = 0)],
    exacts [by simp, h.2 hi, h.1 hi] }
end

end complex_measure

end measure_theory
