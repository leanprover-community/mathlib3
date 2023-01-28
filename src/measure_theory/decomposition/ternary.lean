import measure_theory.measure.complex
import measure_theory.decomposition.jordan
import analysis.complex.roots_of_unity
import analysis.normed_space.operator_norm

attribute [simps] measure_theory.vector_measure.map_rangeₗ

namespace continuous_linear_map
variables
  {R : Type*} {S : Type*} [semiring R] [semiring S] (σ : R →+* S)
  (M : Type*) [topological_space M] [add_comm_monoid M]
  (M₂ : Type*) [topological_space M₂] [add_comm_monoid M₂]
  [module R M] [module S M₂] (f : M →SL[σ] M₂)

@[simp] lemma coe_to_linear_map : ⇑f.to_linear_map = f := rfl

end continuous_linear_map

noncomputable theory
open_locale classical measure_theory ennreal nnreal real

variables {α β : Type*} {m : measurable_space α}

namespace measure_theory

open complex_measure vector_measure complex

section move

include m

/-- Reinterpret a signed measure as a complex measure. -/
@[reducible] def signed_measure.to_complex_measure' : signed_measure α →ₗ[ℝ] complex_measure α :=
vector_measure.map_rangeₗ (algebra.linear_map ℝ ℂ) $ sorry

namespace measure

def to_complex_measure (μ : measure α) [is_finite_measure μ] :=
μ.to_signed_measure.to_complex_measure'

@[simp]
lemma to_complex_measure_apply (μ : measure α) [is_finite_measure μ]
  {s : set α} (hs : measurable_set s) :
  μ.to_complex_measure s = (μ s).to_real :=
by simp [to_complex_measure, hs]

@[simp]
lemma to_complex_measure_zero : (0 : measure α).to_complex_measure = 0 :=
by simp [to_complex_measure]

@[simp]
lemma to_complex_measure_add (μ ν : measure α) [is_finite_measure μ] [is_finite_measure ν] :
  (μ + ν).to_complex_measure = μ.to_complex_measure + ν.to_complex_measure :=
by simp [to_complex_measure]

@[simp]
lemma to_complex_measure_smul (μ : measure α) [is_finite_measure μ] (r : ℝ≥0) :
  (r • μ).to_complex_measure = r • μ.to_complex_measure :=
by { rw [to_complex_measure, to_signed_measure_smul], exact linear_map.map_smul _ _ _ }

end measure

end move

namespace ternary

local notation `ω` := (exp (2 * π * I / 3) : ℂ)

def rotate (j : ℤ) : ℂ →L[ℝ] ℝ := re_clm.comp $ continuous_linear_map.mul _ _ (ω^(-j))

@[simp] lemma rotate_apply (j : ℤ) (z : ℂ) : rotate j z = (ω^(-j) * z).re := rfl

include m

def signed_decomp (j : ℤ) : complex_measure α →ₗ[ℝ] signed_measure α :=
map_rangeₗ (rotate j).to_linear_map (rotate j).continuous

lemma signed_decomp_spec (μ : complex_measure α) (j : ℤ) :
  (signed_decomp 0 μ).to_complex_measure' +
  ω • (signed_decomp 1 μ).to_complex_measure' +
  ω^2 • (signed_decomp 2 μ).to_complex_measure' = μ :=
begin
  ext s hs : 1,
  simp only [signed_decomp, continuous_linear_map.to_linear_map_eq_coe, map_rangeₗ_apply, coe_add,
    vector_measure.coe_smul,
  pi.add_apply, map_range_apply, linear_map.to_add_monoid_hom_coe, rotate_apply, pow_zero, one_mul,
  pi.smul_apply,
  pow_one, algebra.id.smul_eq_mul, algebra.linear_map_apply, coe_algebra_map, of_real_sub,
   of_real_mul,
  continuous_linear_map.coe_coe],
end

-- @[derive is_finite_measure]
-- def pos_decomp (μ : complex_measure α) (j : ℕ) : measure α :=
-- (signed_measure.to_jordan_decomposition $
--   map_rangeₗ (rotate j).to_linear_map (rotate j).continuous μ).pos_part

-- theorem decomp_spec (μ : complex_measure α) (j : ℕ) :
--   (decomp μ 0).to_complex_measure + ω • (decomp μ 1).to_complex_measure
--     + ω^2 • (decomp μ 2).to_complex_measure = μ:=
-- begin
--   ext s hs : 1,
--   simp,
--   sorry
-- end


end ternary

end measure_theory
