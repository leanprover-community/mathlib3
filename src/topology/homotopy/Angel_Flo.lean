import analysis.complex.circle
import topology.metric_space.basic
import topology.homotopy.path
import data.real.basic

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

instance top_group_is_H_space (G : Type u) [topological_space G][group G] [topological_group G]
  : H_space G :=
{
  m := function.uncurry (*) ,
  e := 1,
  m_e_e := by {simp only [function.uncurry_apply_pair, mul_one]},
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

/-
Next, give an example of an H-space (ℝ,z,m) where m(x,y)=(x+y)/2 and z is arbitrary in ℝ. The point is to show that, in the definition of an H-space, the neutral element up to homotopy e is not unique in general.

lemma [Given m as above] ∀ z : ℝ, (R,m,z) is an H-space.

Proof:

m(z,z) = (z+z)/2 = (2*z)/2 = z

(ℝ,+) is a topological group, from which we should obtain that m(x,y)=(x+y)/2 is continuous.

m(x,e) = (x+e)/2 = (e+x)/2 = m(e,x) and this map is homotopic to id_X via
H(t,x) = (1-t) * (x+e)/2 + t * x
-/

variables x y z : ℝ

def our_m : ℝ := (x+y)/2

#check our_m

lemma our_m_continuous : continuous our_m :=
begin
  sorry
end

def R_with_our_m : H_space ℝ :=

example : H_space ℝ :=
{
  m := function.uncurry our_m,
  e := z,
  m_e_e := sorry,
  cont_m := our_m_continuous,
}

--  m := our_m,



-- example : H_space S^3 :=

end H_space
