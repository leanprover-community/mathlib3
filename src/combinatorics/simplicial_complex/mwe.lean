import linear_algebra.finite_dimensional
import data.real.basic

variables {E : Type*} [add_comm_group E] [vector_space ℝ E]

open finite_dimensional

lemma findim_le_findim_of_le {x y : submodule ℝ E} (h : x ≤ y) [finite_dimensional ℝ y] :
  findim ℝ x ≤ findim ℝ y :=
begin
  let f : x →ₗ[ℝ] y := submodule.of_le h,
  have hf : function.injective f,
  { intros x₁ x₂ h',
    apply subtype.ext,
    apply subtype.ext_iff.1 h' },
  haveI : finite_dimensional ℝ x := submodule.finite_dimensional_of_le h,
  apply linear_map.findim_le_findim_of_injective hf,
end
