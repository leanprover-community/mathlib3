import analysis.complex.exponential

section
open real

example : differentiable ℝ (λ (x : ℝ), exp x) :=
begin
  simp
end

example : differentiable ℝ (λ (x : ℝ), exp (x^2)) :=
begin
  simp,
end


end
