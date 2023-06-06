/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.kernel.composition

/-!
# Invariance of measures along a kernel

We say that a measure `μ` is invariant with respect to a kernel `κ` if its push-forward along the
kernel `μ.bind κ` is the same measure.

## Main definitions

* `probability_theory.kernel.invariant`: invariance of a given measure with respect to a kernel.

## Useful lemmas

* `probability_theory.kernel.const_bind_eq_comp_const`, and
  `probability_theory.kernel.comp_const_apply_eq_bind` established the relationship between
  the push-forward measure and the composition of kernels.

-/

open measure_theory

open_locale measure_theory ennreal probability_theory

namespace probability_theory

variables {α β γ : Type*} {mα : measurable_space α} {mβ : measurable_space β}
  {mγ : measurable_space γ}

include mα mβ

namespace kernel

/-! ### Push-forward of measures along a kernel -/

@[simp]
lemma bind_add (μ ν : measure α) (κ : kernel α β) :
  (μ + ν).bind κ = μ.bind κ + ν.bind κ :=
begin
  ext1 s hs,
  rw [measure.bind_apply hs (kernel.measurable _), lintegral_add_measure, measure.coe_add,
    pi.add_apply, measure.bind_apply hs (kernel.measurable _),
    measure.bind_apply hs (kernel.measurable _)],
end

@[simp]
lemma bind_smul (κ : kernel α β) (μ : measure α) (r : ℝ≥0∞) :
  (r • μ).bind κ = r • μ.bind κ :=
begin
  ext1 s hs,
  rw [measure.bind_apply hs (kernel.measurable _), lintegral_smul_measure, measure.coe_smul,
    pi.smul_apply, measure.bind_apply hs (kernel.measurable _), smul_eq_mul],
end

lemma const_bind_eq_comp_const (κ : kernel α β) (μ : measure α) :
  const α (μ.bind κ) = κ ∘ₖ const α μ :=
begin
  ext a s hs : 2,
  simp_rw [comp_apply' _ _ _ hs, const_apply, measure.bind_apply hs (kernel.measurable _)],
end

lemma comp_const_apply_eq_bind (κ : kernel α β) (μ : measure α) (a : α) :
  (κ ∘ₖ const α μ) a = μ.bind κ :=
by rw [← const_apply (μ.bind κ) a, const_bind_eq_comp_const κ μ]

omit mβ

/-! ### Invariant measures of kernels -/

/-- A measure `μ` is invariant with respect to the kernel `κ` if the push-forward measure of `μ`
along `κ` equals `μ`. -/
def invariant (κ : kernel α α) (μ : measure α) : Prop :=
μ.bind κ = μ

variables {κ η : kernel α α} {μ : measure α}

lemma invariant.def (hκ : invariant κ μ) : μ.bind κ = μ := hκ

lemma invariant.comp_const (hκ : invariant κ μ) : κ ∘ₖ const α μ = const α μ :=
by rw [← const_bind_eq_comp_const κ μ, hκ.def]

lemma invariant.comp [is_s_finite_kernel κ] (hκ : invariant κ μ) (hη : invariant η μ) :
  invariant (κ ∘ₖ η) μ :=
begin
  casesI is_empty_or_nonempty α with _ hα,
  { exact subsingleton.elim _ _ },
  { simp_rw [invariant, ← comp_const_apply_eq_bind (κ ∘ₖ η) μ hα.some, comp_assoc,
      hη.comp_const, hκ.comp_const, const_apply] },
end

end kernel

end probability_theory
