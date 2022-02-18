
import analysis.convex.function
import analysis.convex.hull
import analysis.convex.topology
import analysis.normed_space.ordered
import analysis.seminorm


open normed_field set
open_locale pointwise topological_space nnreal big_operators

variables {R 𝕜 𝕜₁ E F G ι ι' : Type*}

section add_comm_monoid

variables (𝕜)

variables [normed_ring 𝕜] [normed_space ℝ 𝕜] [has_scalar 𝕜 E] [has_scalar ℝ E]
variables [is_scalar_tower ℝ 𝕜 E] [add_comm_monoid E] [topological_space E]

def barrel (A : set E) := absorbent 𝕜 A ∧ balanced 𝕜 A ∧ convex ℝ A ∧ is_closed A

end add_comm_monoid

variables [normed_field 𝕜] [normed_space ℝ 𝕜] [add_comm_group E]
variables [module 𝕜 E] [module ℝ E]
variables [is_scalar_tower ℝ 𝕜 E] [topological_space E] [topological_add_group E]
variables [has_continuous_smul ℝ E]
variables [has_continuous_smul 𝕜 E]

variables {A : set E}

variables (U : set E)
variables (hU : balanced 𝕜 U)

#check barrel 𝕜 A
#check convex_hull ℝ A
#check closure (convex_hull ℝ U)
#check hU.closure

#check norm_one.le
#check subset.trans

#check ⋃ (r : 𝕜) (hr : ∥r∥ ≤ 1), r • U

lemma test123 (U : set E) (hU : U ∈ 𝓝 (0 : E)) :
  barrel 𝕜 (closure (convex_hull ℝ (⋃ (r : 𝕜) (hr : ∥r∥ ≤ 1), r • U))) :=
begin
  split,
  {
    have h' : (⋃ (r : 𝕜) (hr : ∥r∥ ≤ 1), r • U) ⊆
      closure (convex_hull ℝ (⋃ (r : 𝕜) (hr : ∥r∥ ≤ 1), r • U)) := sorry,
    refine absorbent.subset (absorbent_nhds_zero _) h',
    refine filter.mem_of_superset hU _,
    refine subset.trans _ (set.subset_Union₂ (1 : 𝕜) norm_one.le),
    refine eq.subset _,

    sorry,
  },
  split,
  {
    refine balanced.closure _,
    sorry,
  },
  split,
  { exact convex.closure (convex_convex_hull _ _) },
  { exact is_closed_closure }
end

lemma contains_zero (hA : barrel 𝕜 A) : (0 : E) ∈ A :=
begin
  sorry,
end
