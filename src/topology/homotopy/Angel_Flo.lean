import topology.homotopy.path

noncomputable theory

class H_space (G : Type*) [topological_space G] :=
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

lemma top_group_is_H_space (G : Type*) [topological_space G] [group G][topological_group G] : H_space G :=
begin
fconstructor,
{ exact function.uncurry has_mul.mul,
}
,
{
 exact has_one.one,
}
,
{
  sorry,
}

end
