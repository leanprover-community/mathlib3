import analysis.asymptotics.asymptotic_equivalent
import measure_theory.integral.interval_integral
import measure_theory.measure.vector_measure

variables {α β γ δ : Type*}

section is_equivalent

open_locale asymptotics

example {l : filter α} {u v w : α → β} [normed_add_comm_group β]
  (huv : u ~[l] v) (hvw : v ~[l] w) : u ~[l] w :=
calc u ~[l] v : huv
   ... ~[l] w : hvw

end is_equivalent

section interval_integral

variables {f : ℝ → ℝ} {μ : measure_theory.measure ℝ}
local notation u ` ~[`:50 a:50`-`:40 b `] `:0 v:50 := interval_integrable a b u v

example {a b c : ℝ} (hab : a ~[f-μ] b)
  (hbc : b ~[f-μ] c) : interval_integrable f μ a c :=
calc a ~[f-μ] b : hab
   ... ~[f-μ] c : hbc

end interval_integral

section vector_measure

open measure_theory measure_theory.vector_measure

open_locale measure_theory

example {u : vector_measure ℝ ℝ} {v : vector_measure ℝ ℝ} {w : vector_measure ℝ ℝ}
  (huv : u ≪ᵥ v) (hvw : v ≪ᵥ w) : u ≪ᵥ w :=
calc u ≪ᵥ v : huv
   ... ≪ᵥ w : hvw

end vector_measure
