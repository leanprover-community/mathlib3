import topology.metric_space.isometry topology.instances.real_vector_space

open set

lemma set.Inter_set_of_eq {ι : Sort*} {α : Type*} (p : ι → α → Prop) :
  (⋂ i, {x | p i x}) = {x | ∀ i, p i x} :=
set.ext $ λ x, set.mem_Inter

section vector_space

variables (E : Type*) [add_comm_group E] [vector_space ℝ E]

/-- A linear map sending each point `(x, y)` to the midpoint of the segment `[x, y]`.
This map should be used only to prove properties of `midpoint` defined below. -/
noncomputable def midpoint.linear : E × E →ₗ[ℝ] E :=
(1/2:ℝ) • (linear_map.id.copair linear_map.id)

variable {E}

/-- `midpoint x y` is the midpoint of the segment `[x, y]`. -/
noncomputable def midpoint (x y : E) : E := midpoint.linear E (x, y)

lemma midpoint_def (x y : E) : midpoint x y = (1/2:ℝ) • (x + y) := rfl

lemma midpoint_self (x : E) : midpoint x x = x :=
by rw [midpoint_def, smul_add, ← add_smul, add_halves, one_smul]

lemma midpoint_comm (x y : E) : midpoint x y = midpoint y x :=
by simp only [midpoint_def, add_comm]

lemma midpoint_add_add (x y x' y' : E) :
  midpoint (x + x') (y + y') = midpoint x y + midpoint x' y' :=
(midpoint.linear E).map_add (x, y) (x', y')

lemma midpoint_add_right (x y z : E) : midpoint (x + z) (y + z) = midpoint x y + z :=
by rw [midpoint_add_add, midpoint_self]

lemma midpoint_add_left (x y z : E) : midpoint (x + y) (x + z) = x + midpoint y z :=
by rw [midpoint_add_add, midpoint_self]

lemma midpoint_neg_neg (x y : E) : midpoint (-x) (-y) = -midpoint x y :=
(midpoint.linear E).map_neg (x, y)

lemma midpoint_sub_sub (x y x' y' : E) :
  midpoint (x - x') (y - y') = midpoint x y - midpoint x' y' :=
(midpoint.linear E).map_sub (x, y) (x', y')

lemma midpoint_sub_right (x y z : E) : midpoint (x - z) (y - z) = midpoint x y - z :=
by rw [midpoint_sub_sub, midpoint_self]

lemma midpoint_sub_left (x y z : E) : midpoint (x - y) (x - z) = x - midpoint y z :=
by rw [midpoint_sub_sub, midpoint_self]

lemma midpoint_smul_smul (c : ℝ) (x y : E) : midpoint (c • x) (c • y) = c • midpoint x y :=
(midpoint.linear E).map_smul c (x, y)

end vector_space

namespace isometric

section normed_group

variables {E : Type*} [normed_group E]

/-- Reflection in `x` as an `isometric` homeomorphism. -/
def reflection (x : E) : E ≃ᵢ E :=
(isometric.neg E).trans (isometric.add_left (x + x))

lemma reflection_apply (x y : E) : (reflection x : E → E) y = x + x - y := rfl

@[simp] lemma reflection_self (x : E) : (reflection x : E → E) x = x := add_sub_cancel _ _

lemma reflection_involutive (x : E) : function.involutive (reflection x : E → E) :=
λ y, by simp only [reflection_apply, sub_sub_cancel]

@[simp] lemma reflection_symm (x : E) : (reflection x).symm = reflection x :=
by { ext y, rw [symm_apply_eq, reflection_involutive x y] }

@[simp] lemma reflection_dist_fixed (x y : E) :
  dist ((reflection x : E → E) y) x = dist y x :=
by { rw [reflection_apply, dist_comm, dist_eq_norm, dist_eq_norm], congr' 1, abel }

lemma reflection_dist_self' (x y : E) :
  dist ((reflection x : E → E) y) y = dist (x + x) (y + y) :=
by { simp only [reflection_apply, dist_eq_norm], congr' 1, abel }

end normed_group

section vector_space

variables {E : Type*} [normed_group E] [vector_space ℝ E]

@[simp] lemma reflection_midpoint_left (x y : E) : (reflection (midpoint x y) : E → E) x = y :=
by rw [reflection_apply, midpoint_def, ← add_smul, add_halves, one_smul, add_sub_cancel']

@[simp] lemma reflection_midpoint_right (x y : E) : (reflection (midpoint x y) : E → E) y = x :=
by rw [reflection_apply, midpoint_def, ← add_smul, add_halves, one_smul, add_sub_cancel]

end vector_space

section normed_space

variables {E : Type*} [normed_group E] [normed_space ℝ E]
 
lemma reflection_dist_self (x y : E) :
  dist ((reflection x : E → E) y) y = 2 * dist x y :=
begin
  rw [reflection_dist_self'],
  conv_lhs { rw [← one_smul ℝ x, ← one_smul ℝ y, ← add_smul, ← add_smul, dist_smul] },
  rw [← bit0, real.norm_eq_abs, abs_of_pos],
  exact two_pos
end

lemma reflection_fixed_iff {x y : E} : (reflection x : E → E) y = y ↔ y = x :=
by { rw [← dist_eq_zero, reflection_dist_self, mul_eq_zero, dist_eq_zero],
  simp only [two_ne_zero, false_or], exact eq_comm }

end normed_space

variables {E : Type*} [normed_group E] [normed_space ℝ E]
  {F : Type*} [normed_group F] [normed_space ℝ F]

/-- If an isometric self-homeomorphism of a normed vector space over `ℝ` fixes `x` and `y`,
then it fixes the midpoint of `[x, y]`. This is a lemma for a more general Mazur-Ulam theorem,
see below. -/
lemma midpoint_fixed {x y : E} :
  ∀ e : E ≃ᵢ E, e x = x → e y = y → e (midpoint x y) = midpoint x y :=
begin
  set z := midpoint x y,
  set s := { e : E ≃ᵢ E | e x = x ∧ e y = y },
  set c := ⨆ e : s, dist (e z) z,
  haveI : nonempty s := ⟨⟨isometric.refl E, rfl, rfl⟩⟩,
  have A : (0:ℝ) < 2 := two_pos,
  have B : bdd_above (range $ λ e : s, dist (e z) z),
  { refine ⟨dist x z + dist x z, forall_range_iff.2 $ λ e, _⟩,
    convert dist_triangle (e z) x z using 2,
    transitivity dist (e x) (e z),
    exact e.1.isometry_to_fun.dist_eq.symm,
    erw [dist_comm, e.2.1] },
  suffices : c ≤ 0,
  { intros e hx hy,
    have A : dist (e z) z ≤ c, from @le_csupr _ _ _ _ B ⟨e, hx, hy⟩,
    exact dist_le_zero.1 (le_trans A this) },
  suffices : c ≤ c / 2,
  { rw [← sub_nonpos, sub_half] at this,
    rw [← add_halves c],
    exact add_nonpos this this },
  apply csupr_le,
  set g : E ≃ᵢ E := reflection z,
  rintros ⟨e, he⟩,
  apply le_div_of_mul_le (zero_lt_two : 0 < (2:ℝ)),
  have : ((e.trans g).trans e.symm).trans g ∈ s,
    by split; simp [he.1, he.2, (e.symm_apply_eq).2 he.1.symm, (e.symm_apply_eq).2 he.2.symm],
  calc dist (e z) z * 2 = dist (g (e z)) (e z) :
    by rw [mul_comm, dist_comm, reflection_dist_self z]
  ... = dist (e.symm (g (e z))) (e.symm (e z)) :
    e.symm.isometry.dist_eq.symm
  ... = dist (e.symm (g (e z))) z : by erw e.to_equiv.symm_apply_apply
  ... = dist (g (e.symm (g (e z)))) z : by rw [reflection_dist_fixed]
  ... ≤ c : @le_csupr _ _ _ _ B ⟨_, this⟩
end

noncomputable def to_real_linear_equiv_of_map_zero (f : E ≃ᵢ F) (h0 : f 0 = 0) :
  E ≃L[ℝ] F :=
begin
  refine { .. add_monoid_hom.to_real_linear_map ⟨f, h0, _⟩ f.isometry_to_fun.continuous,
    .. f.to_homeomorph },
  suffices : ∀ x y, f (midpoint x y) = midpoint (f x) (f y),
  { intros x y,
    have A := this x y,
    have B := this 0 (x + y),
    simp only [midpoint_def, zero_add] at A B,
    have := congr_arg ((•) (2:ℝ)) (B.symm.trans A),
    rwa [smul_smul, smul_smul, one_div_eq_inv, mul_inv_cancel, one_smul, one_smul,
      h0, zero_add] at this,
    exact two_ne_zero },
  clear h0,
  intros x y,
  set e : E ≃ᵢ E := ((f.trans $ reflection $ midpoint (f x) (f y)).trans f.symm).trans
    (reflection $ midpoint x y),
  have hx : e x = x, by simp,
  have hy : e y = y, by simp,
  have hm := e.midpoint_fixed hx hy,
  simp only [e, trans_apply] at hm,
  rwa [← eq_symm_apply, reflection_symm, reflection_self, symm_apply_eq, reflection_fixed_iff] at hm
end

noncomputable def to_real_linear_equiv (f : E ≃ᵢ F) : E ≃L[ℝ] F :=
(f.trans (isometric.add_right (-f 0))).to_real_linear_equiv_of_map_zero (sub_self $ f 0)

end isometric
