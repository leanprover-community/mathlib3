import ring_theory.algebraic
import topology.algebra.polynomial
import analysis.calculus.mean_value
import number_theory.liouville.liouville_constant

noncomputable theory

/--
 define α to be Σᵢ 1/10^i!
-/
def α := liouville.liouville_number (10 : ℕ)

-- Then α is a Liouville number hence a transcendental number.
theorem liouville_α : liouville α :=
begin
  apply liouville.is_liouville,
  norm_num,
end

-- Then our general theory about Liouville number in particular applies to α giving us α transcendental number
theorem transcendental_α : transcendental ℤ α := liouville_α.transcendental
