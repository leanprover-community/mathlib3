/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.group.fundamental_domain
import measure_theory.integral.interval_integral

/-!
# Integrals of periodic functions

In this file we prove that `∫ x in b..b + a, f x = ∫ x in c..c + a, f x` for any (not necessarily
measurable) function periodic function with period `a`.
-/

open set function measure_theory measure_theory.measure topological_space
open_locale measure_theory

lemma is_add_fundamental_domain_Ioc {a : ℝ} (ha : 0 < a) (b : ℝ) (μ : measure ℝ . volume_tac) :
  is_add_fundamental_domain (add_subgroup.zmultiples a) (Ioc b (b + a)) μ :=
begin
  refine is_add_fundamental_domain.mk' measurable_set_Ioc (λ x, _),
  have : bijective (cod_restrict (λ n : ℤ, n • a) (add_subgroup.zmultiples a) _),
    from (equiv.of_injective (λ n : ℤ, n • a) (zsmul_strict_mono_left ha).injective).bijective,
  refine this.exists_unique_iff.2 _,
  simpa only [add_comm x] using exists_unique_add_zsmul_mem_Ioc ha x b
end

variables {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [complete_space E] [second_countable_topology E]

namespace function

namespace periodic

/-- An auxiliary lemma for a more general `function.periodic.interval_integral_add_eq`. -/
lemma interval_integral_add_eq_of_pos {f : ℝ → E} {a : ℝ} (hf : periodic f a)
  (ha : 0 < a) (b c : ℝ) : ∫ x in b..b + a, f x = ∫ x in c..c + a, f x :=
begin
  haveI : encodable (add_subgroup.zmultiples a) := (countable_range _).to_encodable,
  simp only [interval_integral.integral_of_le, ha.le, le_add_iff_nonneg_right],
  haveI : vadd_invariant_measure (add_subgroup.zmultiples a) ℝ volume :=
    ⟨λ c s hs, real.volume_preimage_add_left _ _⟩,
  exact (is_add_fundamental_domain_Ioc ha b).set_integral_eq
    (is_add_fundamental_domain_Ioc ha c) hf.map_vadd_zmultiples
end
  
/-- If `f` is a periodic function with period `a`, then its integral over `[b, b + a]` does not
depend on `b`. -/
lemma interval_integral_add_eq {f : ℝ → E} {a : ℝ} (hf : periodic f a)
  (b c : ℝ) : ∫ x in b..b + a, f x = ∫ x in c..c + a, f x :=
begin
  rcases lt_trichotomy 0 a with (ha|rfl|ha),
  { exact hf.interval_integral_add_eq_of_pos ha b c },
  { simp },
  { rw [← neg_inj, ← interval_integral.integral_symm, ← interval_integral.integral_symm],
    simpa only [← sub_eq_add_neg, add_sub_cancel]
      using (hf.neg.interval_integral_add_eq_of_pos (neg_pos.2 ha) (b + a) (c + a)) }
end

end periodic

end function
