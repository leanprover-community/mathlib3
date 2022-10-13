import analysis.normed_space.operator_norm
import analysis.normed_space.star.basic

-- these are all prerequisites and should moved to the appropriate places

lemma _root_.cstar_ring.nnnorm_self_mul_star {E : Type*} [non_unital_normed_ring E] [star_ring E]
  [cstar_ring E] {x : E} : ∥x * star x∥₊ = ∥x∥₊ * ∥x∥₊ :=
by simpa using @cstar_ring.nnnorm_star_mul_self _ _ _ _ (star x)

open_locale nnreal
open nnreal
namespace continuous_linear_map

lemma exists_mul_lt_apply_of_lt_op_nnnorm {𝕜 E F: Type*} [normed_add_comm_group E]
  [normed_add_comm_group F] [nontrivially_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
  (f : E →L[𝕜] F) {r : ℝ≥0} (hr : r < ∥f∥₊) : ∃ x, r * ∥x∥₊ < ∥f x∥₊ :=
by simpa only [not_forall, not_le, set.mem_set_of] using not_mem_of_lt_cInf
  (nnnorm_def f ▸ hr : r < Inf {c : ℝ≥0 | ∀ x, ∥f x∥₊ ≤ c * ∥x∥₊}) (order_bot.bdd_below _)

lemma exists_mul_lt_of_lt_op_norm {𝕜 E F: Type*} [normed_add_comm_group E]
  [normed_add_comm_group F] [nontrivially_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
  (f : E →L[𝕜] F) {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < ∥f∥) : ∃ x, r * ∥x∥ < ∥f x∥ :=
by { lift r to ℝ≥0 using hr₀, exact f.exists_mul_lt_apply_of_lt_op_nnnorm hr }

lemma exists_lt_apply_of_lt_op_nnnorm {𝕜 E F: Type*} [normed_add_comm_group E]
  [normed_add_comm_group F] [densely_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
  (f : E →L[𝕜] F) {r : ℝ≥0} (hr : r < ∥f∥₊) : ∃ x : E, ∥x∥₊ ≤ 1 ∧ r < ∥f x∥₊ :=
begin
  obtain ⟨y, hy⟩ := f.exists_mul_lt_apply_of_lt_op_nnnorm hr,
  have hy'' : ∥y∥₊ ≠ 0 := nnnorm_ne_zero_iff.2
    (λ heq, by simpa only [heq, nnnorm_zero, map_zero, not_lt_zero'] using hy),
  have hfy : ∥f y∥₊ ≠ 0 := (zero_le'.trans_lt hy).ne',
  rw [←inv_inv (∥f y∥₊), lt_inv_iff_mul_lt (inv_ne_zero hfy), mul_assoc, mul_comm (∥y∥₊),
    ←mul_assoc, ←lt_inv_iff_mul_lt hy''] at hy,
  obtain ⟨k, hk₁, hk₂⟩ := normed_field.exists_lt_nnnorm_lt 𝕜 hy,
  refine ⟨k • y, (nnnorm_smul k y).symm ▸ (nnreal.le_inv_iff_mul_le hy'').1 hk₂.le, _⟩,
  rwa [map_smul f, nnnorm_smul, ←nnreal.div_lt_iff hfy, div_eq_mul_inv],
end

lemma exists_lt_apply_of_lt_op_norm {𝕜 E F: Type*} [normed_add_comm_group E]
  [normed_add_comm_group F] [densely_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
  (f : E →L[𝕜] F) {r : ℝ} (hr : r < ∥f∥) : ∃ x : E, ∥x∥ ≤ 1 ∧ r < ∥f x∥ :=
begin
  by_cases hr₀ : r < 0,
  { refine ⟨0, by simpa using hr₀⟩, },
  { lift r to ℝ≥0 using not_lt.1 hr₀,
    exact f.exists_lt_apply_of_lt_op_nnnorm hr, }
end

lemma op_nnnorm_eq_Sup_unit_ball {𝕜 E F: Type*} [normed_add_comm_group E]
  [normed_add_comm_group F] [densely_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
  (f : E →L[𝕜] F) : Sup ((λ x, ∥f x∥₊) '' {x : E | ∥x∥₊ ≤ 1}) = ∥f∥₊ :=
begin
  have hball : {x : E | ∥x∥₊ ≤ 1}.nonempty := ⟨0, nnnorm_zero.trans_le zero_le_one⟩,
  refine cSup_eq_of_forall_le_of_forall_lt_exists_gt (hball.image _) _ (λ ub hub, _),
  { rintro - ⟨x, hx, rfl⟩, exact f.unit_le_op_norm x hx },
  { obtain ⟨x, hx, hxf⟩ := f.exists_lt_apply_of_lt_op_nnnorm hub,
    exact ⟨_, ⟨x, hx, rfl⟩, hxf⟩, }
end

lemma op_norm_eq_Sup_unit_ball {𝕜 E F: Type*} [normed_add_comm_group E]
  [normed_add_comm_group F] [densely_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
  (f : E →L[𝕜] F) : Sup ((λ x, ∥f x∥) '' {x : E | ∥x∥ ≤ 1}) = ∥f∥ :=
by simpa only [nnreal.coe_Sup, set.image_image] using nnreal.coe_eq.2 f.op_nnnorm_eq_Sup_unit_ball

end continuous_linear_map

namespace cstar_ring

open continuous_linear_map

lemma op_nnnorm_lmul {𝕜 E : Type*} [densely_normed_field 𝕜] [non_unital_normed_ring E] [star_ring E]
  [cstar_ring E] [normed_space 𝕜 E] [is_scalar_tower 𝕜 E E] [smul_comm_class 𝕜 E E] (a : E) :
  ∥lmul 𝕜 E a∥₊ = ∥a∥₊ :=
begin
  rw ←op_nnnorm_eq_Sup_unit_ball,
  refine cSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ (λ r hr, _),
  { refine set.nonempty.image _ _,
    exact ⟨0, nnnorm_zero.trans_le zero_le_one⟩, },
  { rintro - ⟨x, hx, rfl⟩,
    exact ((lmul 𝕜 E a).unit_le_op_norm x hx).trans (op_norm_lmul_apply_le 𝕜 E a) },
  { have ha := nnreal.inv_pos.2 (zero_le'.trans_lt hr),
    have ha' := (zero_le'.trans_lt hr),
    rw [←inv_inv (∥a∥₊), nnreal.lt_inv_iff_mul_lt ha.ne'] at hr,
    have := mul_lt_mul_of_pos_right hr ha,
    obtain ⟨k, hk₁, hk₂⟩ := normed_field.exists_lt_nnnorm_lt 𝕜 this,
    refine ⟨_, ⟨k • star a, _, rfl⟩, _⟩,
    { simpa only [set.mem_set_of, nnnorm_smul, nnnorm_star, ←nnreal.le_inv_iff_mul_le ha'.ne',
        one_mul] using hk₂.le, },
    { simp only [nnnorm_smul, mul_smul_comm, cstar_ring.nnnorm_self_mul_star, lmul_apply],
      rwa [←nnreal.div_lt_iff, div_eq_mul_inv, mul_inv, ←mul_assoc],
      exact (mul_pos ha' ha').ne' } },
end

/-- The left regular representation is an isometry for C⋆-algebras. -/
lemma op_norm_lmul {𝕜 E : Type*} [densely_normed_field 𝕜] [non_unital_normed_ring E] [star_ring E]
  [cstar_ring E] [normed_space 𝕜 E] [is_scalar_tower 𝕜 E E] [smul_comm_class 𝕜 E E] (a : E) :
  ∥lmul 𝕜 E a∥ = ∥a∥ :=
congr_arg coe $ op_nnnorm_lmul a

lemma op_nnnorm_lmul_flip {𝕜 E : Type*} [densely_normed_field 𝕜] [non_unital_normed_ring E]
  [star_ring E] [cstar_ring E] [normed_space 𝕜 E] [is_scalar_tower 𝕜 E E] [smul_comm_class 𝕜 E E]
  (a : E) : ∥(lmul 𝕜 E).flip a∥₊ = ∥a∥₊ :=
begin
  rw [←op_nnnorm_eq_Sup_unit_ball, ←nnnorm_star, ←@op_nnnorm_lmul 𝕜 E, ←op_nnnorm_eq_Sup_unit_ball],
  congr' 1,
  simp only [lmul_apply, flip_apply],
  refine set.subset.antisymm _ _;
  rintro - ⟨b, hb, rfl⟩;
  refine ⟨star b, (nnnorm_star b).trans_le hb, _⟩,
  { simp only [←star_mul, nnnorm_star] },
  { simpa using (nnnorm_star (star b * a)).symm }
end

lemma op_norm_lmul_flip {𝕜 E : Type*} [densely_normed_field 𝕜] [non_unital_normed_ring E]
  [star_ring E] [cstar_ring E] [normed_space 𝕜 E] [is_scalar_tower 𝕜 E E] [smul_comm_class 𝕜 E E]
  (a : E) : ∥(lmul 𝕜 E).flip a∥ = ∥a∥ :=
congr_arg coe $ op_nnnorm_lmul_flip a

end cstar_ring
