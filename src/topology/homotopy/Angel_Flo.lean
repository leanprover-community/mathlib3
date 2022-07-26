import analysis.complex.circle
import topology.metric_space.basic
import topology.homotopy.path

universe u

noncomputable theory

namespace H_space

class H_space (G : Type u) [topological_space G] :=
--(m : G → G → G)
(m : G × G → G)
(e : G)
--(m_e_e : m e e = e)
(m_e_e : m(e,e) = e)
-- m is continuous
(cont_m : continuous m) -- this is a term of type continuous m
(m_e_dot_homotopic_to_id : ∀ g : G,
  continuous_map.homotopy_rel
  ⟨(λ g : G, m (e, g)), (continuous.comp cont_m (continuous.prod_mk continuous_const continuous_id'))⟩
  --⟨(λ g : G, g), continuous_id'⟩
  ⟨id, continuous_id'⟩
  {e})
(m_dot_e_homotopic_to_id : ∀ g : G,
  continuous_map.homotopy_rel
  ⟨(λ g : G, m(g, e)), (continuous.comp cont_m (continuous.prod_mk continuous_id' continuous_const))⟩
  ⟨id, continuous_id'⟩
  {e})

instance top_group_is_H_space (G : Type u) [topological_space G] [group G] [topological_group G]
  : H_space G :=
{
  m := function.uncurry (*) ,
  e := 1,
  m_e_e := by {simp only [function.uncurry_apply_pair, mul_one], },
  cont_m := has_continuous_mul.continuous_mul,
  m_e_dot_homotopic_to_id := by {
    intro g,
    simp only [function.uncurry_apply_pair, one_mul],
    exact continuous_map.homotopy_rel.refl ⟨id, continuous_id'⟩  {1},
  },
  m_dot_e_homotopic_to_id := λ g, by {simp only [function.uncurry_apply_pair, mul_one],
    exact continuous_map.homotopy_rel.refl _ _}
}

example : H_space circle := infer_instance

-- exemple : H_space S^3 :=

end H_space
