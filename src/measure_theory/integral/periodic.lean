import measure_theory.group.fundamental_domain
import measure_theory.integral.interval_integral

/-!
# Integrals of periodic functions
-/

open set measure_theory measure_theory.measure

lemma is_add_fundamental_domain_Ioc {a : ℝ} (ha : 0 < a) (b : ℝ) (μ : measure ℝ . volume_tac) :
  is_add_fundamental_domain (add_subgroup.zmultiples a) (Ioc b (b + a)) :=
