import tactic
import group_theory.group_action.conj_act
import group_theory.subgroup.basic
import algebra.star.unitary
import linear_algebra.clifford_algebra.star
import linear_algebra.clifford_algebra.even
import linear_algebra.clifford_algebra.basic
import linear_algebra.exterior_algebra.basic
import linear_algebra.clifford_algebra.contraction

variables {R : Type*} [field R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

section pin
open clifford_algebra mul_action
open_locale pointwise

def lipschitz (Q : quadratic_form R M) :=
subgroup.closure (coe ⁻¹' set.range (ι Q) : set (clifford_algebra Q)ˣ)

namespace linear_map

variables {R : Type*} {A : Type*} {B : Type*} [comm_semiring R] [semiring A] [semiring B]
  [algebra R A] [algebra R B]

/-- An alternate statement of `linear_map.map_smul` for when `algebra_map` is more convenient to
work with than `•`. -/
lemma map_algebra_map_mul (f : A →ₗ[R] B) (a : A) (r : R) :
  f (algebra_map R A r * a) = algebra_map R B r * f a :=
by rw [←algebra.smul_def, ←algebra.smul_def, map_smul]

lemma map_mul_algebra_map (f : A →ₗ[R] B) (a : A) (r : R) :
  f (a * algebra_map R A r) = f a * algebra_map R B r :=
by rw [←algebra.commutes, ←algebra.commutes, map_algebra_map_mul]

end linear_map

def exterior_invertible_of_clifford_invertible {Q : quadratic_form R M} {m : M}
  [invertible (2 : R)] (h : invertible ((algebra_map R (clifford_algebra Q)) (Q m))) :
    invertible ((algebra_map R (exterior_algebra R M)) (Q m)) :=
{ inv_of := equiv_exterior Q (⅟ (algebra_map R (clifford_algebra Q) (Q m))),
  inv_of_mul_self :=
  begin
    dsimp only [equiv_exterior],
    simp only [map_neg, alpha_equiv_apply],
    have h1 := h.2,
    rw ← algebra.commutes,
    rw ← algebra.smul_def,
    rw ← map_smul,
    rw algebra.smul_def,
    simp only [mul_inv_of_self],
    dsimp [alpha],
    simp,
  end,
  mul_inv_of_self :=
  begin
    dsimp only [equiv_exterior],
    simp only [map_neg, alpha_equiv_apply],
    rw ← algebra.smul_def,
    rw ← map_smul,
    rw algebra.smul_def,
    simp only [mul_inv_of_self],
    dsimp [alpha],
    simp,
  end }

def invertible_of_invertible_ι (Q : quadratic_form R M) (m : M) [invertible (ι Q m)]
  [invertible (2 : R)] : invertible (Q m) :=
begin
  have h1 : invertible (ι Q m * ι Q m) := invertible_mul (ι Q m) (ι Q m),
  simp only [ι_sq_scalar] at h1,
  have h2 : invertible ((algebra_map R (exterior_algebra R M)) (Q m)),
  { let g := equiv_exterior Q,
    dsimp only [equiv_exterior] at *,
    sorry},
  let f := @exterior_algebra.algebra_map_inv R _ M _ _,
  have h3 := h2.3,
  apply_fun f at h3,
  dsimp [f] at h3,
  rw map_mul f _ _ at h3,
  simp only [alg_hom.commutes, algebra.id.map_eq_id, ring_hom.id_apply, map_one] at h3,
  --let g := (equiv_exterior Q).comp f,



  sorry
end

#check set.differ

lemma unknown_name {x : (clifford_algebra Q)ˣ} (hx : x ∈ lipschitz Q) [invertible (2 : R)]:
    conj_act.to_conj_act x • (ι Q).range ≤ (ι Q).range :=
begin
  refine @subgroup.closure_induction'' _ _ _ _ _ hx _ _ _ _,
  {
    sorry}, -- one lemma needed
  { -- same lemma needed
    sorry},
  { -- solved
    sorry},
  { -- solved
    sorry},
end

/-
  ↑y * ⇑(ι Q) a * ↑y⁻¹
  refine subgroup.closure_induction hx _ _ _ _,
  { intros x hx1 y hy,
    dsimp [(•)] at hy,
    simp only [set.mem_preimage, set.mem_range] at hx1,
    simp only [exists_exists_eq_and] at hy,
    simp only [linear_map.mem_range],
    cases hx1 with z hz,
    cases hy with a ha,
    subst ha,
    letI := x.invertible,
    rw ← inv_of_units x,
    have hz1 := hz.symm,
    haveI : invertible ((ι Q) z),
    { rw ← hz1,
      exact _inst, },
    have goal : ∃ (y : M), (ι Q) y = (ι Q z) * (ι Q) a * ⅟ (ι Q z),
    { haveI :  invertible (Q z),
      { exact invertible_of_invertible_ι Q z, },
      use ((⅟(Q z) * quadratic_form.polar Q z a) • z - a),
      rw ι_mul_ι_mul_inv_of_ι z a, },
    convert goal,
    ext1,
    congr',
    exact subsingleton.helim (congr_arg invertible hz1) _inst _inst_5,


        sorry},
  { dsimp [(•)],
    intros y hy,
    simp only [linear_map.mem_range],
    simp only [submodule.mem_map, linear_map.mem_range, distrib_mul_action.to_linear_map_apply,
      one_smul, exists_exists_eq_and] at hy,
    exact hy,
    sorry },
  { intros x y hx1 hy1 z hz1,
    simp only [conj_act.to_conj_act_mul] at hz1,
    have goal : (conj_act.to_conj_act x * conj_act.to_conj_act y) • (ι Q).range
      ≤ (ι Q).range,
    { intros m hm,
      clear hz1,
      dsimp [(•)] at hm,
      simp only [mul_inv_rev, units.coe_mul, exists_exists_eq_and] at hm,
      cases hm with a hm,
      have hm1 : ↑x * (↑y * (ι Q) a * ↑y⁻¹) * ↑x⁻¹ = m,
      { rw ← hm,
        simp [mul_assoc], },
      have hy2 : ↑y * (ι Q) a * ↑y⁻¹ ∈ conj_act.to_conj_act y • (ι Q).range,
      { dsimp [(•)],
        simp only [exists_exists_eq_and, exists_apply_eq_apply], },
      specialize hy1 hy2,
      have hx2 : ↑x * (↑y * (ι Q) a * ↑y⁻¹) * ↑x⁻¹ ∈ conj_act.to_conj_act x • (ι Q).range,
      { dsimp [(•)],
        simp only [units.mul_left_inj, units.mul_right_inj, exists_exists_eq_and],
        exact hy1, },
      specialize hx1 hx2,
      rwa hm1 at hx1, },
    exact goal hz1, },
  { intros x hx1 y hy1,
    simp only [set.mem_preimage, set.mem_range] at hx1,
    cases hx1 with z hz1,
    dsimp [(•)] at hy1,
    simp only [inv_inv, exists_exists_eq_and] at hy1,
    cases hy1 with a ha1,
    sorry},
-/

#check lipschitz Q

end pin
