import ring_theory.fractional_ideal

namespace ring.fractional_ideal

open ring

section fraction_map

variables {R K : Type*} [integral_domain R] [field K] {f : fraction_map R K}

@[simp]
lemma fractional_ideal.coe_ideal_le {I : ideal R} {J : fractional_ideal f} :
  ↑I ≤ J ↔ ∀ x ∈ I, f.to_map x ∈ J :=
⟨λ h x hx, h (by simpa only [localization_map.coe_submodule,
    localization_map.lin_coe_apply, fractional_ideal.exists_mem_to_map_eq,
    submodule.mem_map, fractional_ideal.coe_coe_ideal,
    fractional_ideal.val_eq_coe] using hx),
 λ h x hx, let ⟨x', hx', eq_x⟩ := fractional_ideal.mem_coe_ideal.mp hx in eq_x ▸ h x' hx'⟩

lemma fractional_ideal.mem_coe {x : f.codomain} {I : fractional_ideal f} :
  x ∈ (I : submodule R f.codomain) ↔ x ∈ I :=
iff.rfl

@[simp, norm_cast]
lemma fractional_ideal.coe_to_fractional_ideal_mul (I J : ideal R) :
  (↑(I * J) : fractional_ideal f) = I * J :=
begin
  apply le_antisymm,
  { rw fractional_ideal.coe_ideal_le,
    intros x hx,
    refine submodule.mul_induction_on hx (λ x hx y hy, _) _ (λ x y hx hy, _) (λ r x hx, _),
    { rw f.to_map.map_mul,
      apply fractional_ideal.mul_mem_mul; rw fractional_ideal.mem_coe_ideal,
      { exact ⟨x, hx, rfl⟩ },
      { exact ⟨y, hy, rfl⟩ } },
    { rw f.to_map.map_zero,
      exact submodule.zero_mem _ },
    { rw f.to_map.map_add,
      exact submodule.add_mem _ hx hy },
    { rw [smul_eq_mul, f.to_map.map_mul],
      exact submodule.smul_mem _ _ hx } },
  { rw fractional_ideal.mul_le,
    intros x hx y hy,
    obtain ⟨x', hx', rfl⟩ := fractional_ideal.mem_coe_ideal.mp hx,
    obtain ⟨y', hy', rfl⟩ := fractional_ideal.mem_coe_ideal.mp hy,
    rw fractional_ideal.mem_coe_ideal,
    exact ⟨x' * y', ideal.mul_mem_mul hx' hy', f.to_map.map_mul _ _⟩ },
end

end fraction_map

end ring.fractional_ideal
