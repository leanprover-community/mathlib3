import number_theory.mod_forms.mod_forms2
import number_theory.mod_forms.congruence_subgroups
import algebraic_geometry.EllipticCurve
import measure_theory.integral.unform_limits_of_holomorphic

open modular_forms complex
open_locale interval real

local notation `ℍ`:=upper_half_plane

noncomputable theory

def map_to_upper (x : ℝ) : ℍ := ⟨(x + I),
  by {simp only [complex.add_im, complex.of_real_im, complex.I_im, zero_add, zero_lt_one],} ⟩

def modular_form_an {N  : ℕ} {k : ℤ} (n : ℕ) (f : space_of_mod_forms_of_level_and_weight (Gamma0_N N) k)
: ℂ := ∫ (x : ℝ) in 0..1, ( exp (-2 * π * I * n *(x + I))) * f.1 (map_to_upper x)

def rat_red (q : ℚ) ( p : ℕ) : (zmod p) := (q.num : zmod p) * (q.denom : zmod p)⁻¹

def set_of_points_mod_n (E : EllipticCurve ℚ) (n : ℕ) := {P : (zmod n) × (zmod n) |
  let ⟨x, y⟩ := P in  y^2 + (rat_red E.a1 n)* x * y+ (rat_red E.a3 n) * y   =
  x^3 +(rat_red E.a2 n)* x^2 + (rat_red E.a4 n) * x + (rat_red E.a6 n)}

def EllipticCurve.ap (E : EllipticCurve ℚ) (p : ℕ) : ℕ :=
  p-(cardinal.mk (set_of_points_mod_n E p)).to_nat

theorem modularity_conjecture (E : EllipticCurve ℚ) : ∃ (N : ℕ)
  (f : space_of_mod_forms_of_level_and_weight (Gamma0_N N) 2),
   ∀ (p : ℕ) (hp : p.prime ) (hN : (N : zmod p ) ≠ 0 ),
   modular_form_an p f = E.ap p :=
begin
sorry,
end
