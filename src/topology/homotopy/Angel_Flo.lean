import analysis.complex.circle
import topology.metric_space.basic
import topology.homotopy.path
import data.real.basic

universe u

noncomputable theory

open_locale unit_interval

namespace H_space

class H_space (G : Type u) [topological_space G] :=
--(m : G → G → G)
(m : G × G → G)
(e : G)
--(m_e_e : m e e = e)
(m_e_e : m(e,e) = e)
-- m is continuous
(cont_m : continuous m) -- this is a term of type continuous m
(m_e_dot_homotopic_to_id :
  continuous_map.homotopy_rel
  ⟨(λ g : G, m (e, g)), (continuous.comp cont_m (continuous.prod_mk continuous_const continuous_id'))⟩
  --⟨(λ g : G, g), continuous_id'⟩
  ⟨id, continuous_id'⟩
  {e})
(m_dot_e_homotopic_to_id :
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
    simp only [function.uncurry_apply_pair, one_mul],
    exact continuous_map.homotopy_rel.refl ⟨id, continuous_id'⟩  {1},
  },
  m_dot_e_homotopic_to_id := by {simp only [function.uncurry_apply_pair, mul_one],
    exact continuous_map.homotopy_rel.refl _ _}
}

example : H_space circle := infer_instance

/-
Next, give an example of an H-space (ℝ,z,m) where m(x,y)=(x+y)/2 and z is arbitrary in ℝ. The point is to show that, in the definition of an H-space, the neutral element up to homotopy e is not unique in general.

lemma [Given m as above] ∀ z : (ℝ,z,m) is an H-space.

Proof:

m(z,z) = (z+z)/2 = (2*z)/2 = z

(ℝ,+) is a topological group, from which we should obtain that m(x,y)=(x+y)/2 is continuous.

m(x,z) = (x+z)/2 = (z+x)/2 = m(z,x) and this map is homotopic to id_X via
H(t,x) = (1-t) * (x+z)/2 + t * x
-/


def H (z : ℝ) : I × ℝ → ℝ := λ p, (1 - p.1) * (p.2 + z)/2 + p.1 * p.2
lemma cont_H (z : ℝ) : continuous (H z) :=
begin
  dsimp [H],

  -- Handy trick continuity?,
  exact ((continuous_const.sub (continuous_induced_dom.comp continuous_fst)).mul
   (continuous_snd.add continuous_const)).div_const.add
  ((continuous_induced_dom.comp continuous_fst).mul continuous_snd),
end

def H' (z: ℝ) : C(I × ℝ, ℝ) := ⟨H(z), cont_H(z)⟩

def H_space_R_with_z (z : ℝ) : H_space ℝ :=
{ m := λ x, (x.1 + x.2)/2 ,
  e := z,
  m_e_e := by simp only [half_add_self],
  cont_m := continuous_add.div_const,
  m_e_dot_homotopic_to_id := begin
  use H' z,
  {
    intro x,
    dsimp [H', H],
    ring_nf,
  },
  {
   intro x,
    dsimp [H', H],
    ring_nf,
  },
  { simp only [set.mem_Icc, set.mem_singleton_iff, continuous_map.coe_mk, id.def, set_coe.forall, forall_eq, half_add_self, and_self],
    intros x _,
    dsimp [H', H],
    ring,
  },
  end,
  m_dot_e_homotopic_to_id := begin
  use H' z,
  {
    intro x,
    dsimp [H', H],
    ring_nf,
  },
  {
   intro x,
    dsimp [H', H],
    ring_nf,
  },
  { simp only [set.mem_Icc, set.mem_singleton_iff, continuous_map.coe_mk, id.def, set_coe.forall, forall_eq, half_add_self, and_self],
    intros x _,
    dsimp [H', H],
    ring,
  },
  end
}



class Ω (X : Type u) [topological_space X] :=
    (loop : ℝ → X)
    (boundary : loop 0 = loop 1)


example : Ω ℝ :=
{
  loop := λ t, t*(1-t),
  boundary := by ring
}

def juxt_loop (X : Type u) [topological_space X] (α β : Ω X) : Ω X :=
{
  loop :=  λ t, if t < 1/2 then (@Ω.loop X _ α (2*t)) else (@Ω.loop X _ β (1-2*t)),
  boundary :=
  begin
    simp,
  end,
}


instance loop_space_is_H_space (X : Type u) [topological_space X]
  : H_space C(circle, X) :=
{
  m := sorry,
  e := sorry,
  m_e_e := sorry,
  cont_m := sorry,
  m_e_dot_homotopic_to_id  := sorry,
  m_dot_e_homotopic_to_id := sorry,
}

variables x y : ℝ

-- def our_m : ℝ := (x+y)/2
-- #check our_m

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
/-
  Next, show that the sphere S^3 has a canonical H-space structure.

  We will think of S^3 as the quaternions of norm 1.

  The "usual" quaternions are denoted H[ℝ] in Lean. They form an ℝ-algebra, equipped with a conjugation x → quaternion.conj x and a norm |x|^2 = x * quaternion.conj x.

  This norm is multiplicative, so the elements of norm 1 form a group norm_1_quaternions. The quaternion algebra H[ℝ] should have a topology, and the induced topology on norm_1_quaternions makes it a topological group.

  In particular, the norm 1 quaternions form an H-space.

  There is a theorem in Lean saying that |x|^2 = x_1^2 + x_2^2 + x_3^2 + x_4^2 (coordinates in the canonical basis of H[ℝ]), so the norm one quaternions are identified with S^3.

  If SU(2) is already defined in Lean, it would be nice to also identify S^3 with SU(2), via u + v J → matrix (u & - complex.conj v \\ v & complex.conj u).

  Obs: a similar strategy will apply for S^7 (octonions of norm 1), except that the octonions of norm 1 do not form a group (no associativity).
-/


-- example : H_space S^3 :=

end H_space
