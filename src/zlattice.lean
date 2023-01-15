import group_theory.subgroup.basic
import data.real.basic
import topology.order
import topology.algebra.group.basic
import topology.constructions
import topology.instances.real
import linear_algebra.free_module.basic
import linear_algebra.free_module.pid
import analysis.normed.group.basic
import linear_algebra.finite_dimensional
import analysis.normed_space.basic
import group_theory.finiteness

open_locale classical

section basis

variables {R M ι : Type*} [semiring R]
variables [add_comm_monoid M] [module R M]  (b : basis ι R M)

lemma basis.ext_elem_iff {x y : M} :
    x = y ↔ (∀ i, b.repr x i = b.repr y i) :=
 by simp only [← finsupp.ext_iff, embedding_like.apply_eq_iff_eq]

end basis

section zspan

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {ι : Type*} [fintype ι] (b : basis ι ℝ E)

noncomputable def zspan.basis : basis ι ℤ (submodule.span ℤ (set.range b)) :=
basis.span (b.linear_independent.restrict_scalars (smul_left_injective ℤ (by norm_num)))

lemma zspan.basis_eq (i : ι) : b i = zspan.basis b i := by simp only [zspan.basis, basis.span_apply]

lemma zspan.repr_eq (m : submodule.span ℤ (set.range b)) (i : ι) :
  ((zspan.basis b).repr m i : ℝ) = b.repr m i :=
begin
  rw ← sub_eq_zero,
  revert i,
  apply fintype.linear_independent_iff.mp b.linear_independent,
  simp_rw sub_smul,
  rw finset.sum_sub_distrib,
  rw sub_eq_zero,
  rw basis.sum_repr,
  simp_rw zspan.basis_eq b,
  simp_rw ← zsmul_eq_smul_cast ℝ _ _,
  rw ← congr_arg (coe : _ → E) ((zspan.basis b).sum_repr m),
  rw submodule.coe_sum,
  simp_rw set_like.coe_smul,
end

noncomputable def zspan.floor_map : E → submodule.span ℤ (set.range b) :=
λ m, finset.univ.sum (λ i, int.floor (b.repr m i) • zspan.basis b i)

lemma zspan.floor_map_single (m : E) (i : ι) :
  b.repr (zspan.floor_map b m) i = int.floor (b.repr m i) :=
begin
  rw ← sub_eq_zero,
  revert i,
  have zz := fintype.linear_independent_iff.mp b.linear_independent,
  apply zz,
  simp_rw sub_smul,
  rw finset.sum_sub_distrib,
  rw sub_eq_zero,
  simp_rw zspan.basis_eq,
  simp_rw ← zspan.repr_eq,
  simp_rw ← zsmul_eq_smul_cast ℝ _ _,
  rw_mod_cast basis.sum_repr (zspan.basis b) (zspan.floor_map b m),
  refl,
end

noncomputable def zspan.fract_map : E → E := λ m, m - zspan.floor_map b m

lemma zspan.fract_map_single (m : E) (i : ι):
  b.repr (zspan.fract_map b m) i = int.fract (b.repr m i) :=
begin
  rw zspan.fract_map,
  rw map_sub,
  rw finsupp.coe_sub,
  rw pi.sub_apply,
  rw zspan.floor_map_single,
  refl,
end

lemma zspan.fract_map_eq_iff (m n : E) :
  zspan.fract_map b m = zspan.fract_map b n ↔ m - n ∈ submodule.span ℤ (set.range ⇑b) :=
begin
  have : zspan.fract_map b m = zspan.fract_map b n ↔ ∀ i, ∃ z : ℤ, b.repr (m - n) i = z,
  { rw basis.ext_elem_iff b,
    simp_rw zspan.fract_map_single,
    simp_rw map_sub,
    simp_rw finsupp.coe_sub,
    simp_rw pi.sub_apply,
    simp_rw int.fract_eq_fract, },
  rw this,
  split,
  { intro h,
    rw ← basis.sum_repr b (m - n),
    refine sum_mem _,
    intros i _,
    obtain ⟨z, hz⟩ := h i,
    rw_mod_cast hz,
    rw ← zsmul_eq_smul_cast ℝ _ _,
    refine zsmul_mem (submodule.subset_span (set.mem_range_self i)) _, },
  { intros h i,
    rw (zspan.basis b).mem_submodule_iff' at h,
    obtain ⟨c, hc⟩ := h,
    rw_mod_cast hc,
    use c i,
    simp_rw submodule.coe_sum,
    simp_rw set_like.coe_smul,
    simp_rw ← zspan.basis_eq b,
    simp_rw zsmul_eq_smul_cast ℝ _ _,
    exact congr_fun (basis.repr_sum_self b (λ x, (c x : ℝ))) i, },
end

example (x y : E) (L : submodule ℤ E) (h : x ∈ L) : - x ∈ L := neg_mem_iff.mpr h

-- TODO: prove that it is an add hom
noncomputable def zspan.fract_quo_map : E ⧸ submodule.span ℤ (set.range ⇑b) → E :=
begin
  intro q,
  refine quotient.lift_on' q (zspan.fract_map b) _,
  intros x y hxy,
  rw zspan.fract_map_eq_iff,
  rw ← neg_mem_iff,
  have := quotient_add_group.left_rel_apply.mp hxy,
  convert this,
  abel,
end

lemma zspan.injective_fract_quo_map : function.injective (zspan.fract_quo_map b) :=
begin
  dsimp [zspan.fract_quo_map],
  refine λ x y, quotient.induction_on₂' x y _,
  intros a1 a2 h,
  simp_rw quotient.lift_on'_mk' _ _ _ at h,
  rw zspan.fract_map_eq_iff at h,
  rw ← submodule.mem_to_add_subgroup at h,
  rw ← neg_mem_iff at h,
  rwa quotient.eq',
  rw quotient_add_group.left_rel_apply,
  convert h,
  abel,
end

lemma zspan.fract_map_le (m : E):
  ‖zspan.fract_map b m‖ ≤ finset.univ.sum (λ j, ‖b j‖) :=
begin
  calc
    ‖zspan.fract_map b m‖
        = ‖finset.univ.sum (λ i, b.repr (zspan.fract_map b m) i • b i)‖
          : by rw b.sum_repr
    ... = ‖finset.univ.sum (λ i, int.fract (b.repr m i) • b i)‖
          : by simp_rw zspan.fract_map_single
    ... ≤ finset.univ.sum (λ i, ‖int.fract (b.repr m i) • b i‖)
          : norm_sum_le _ _
    ... ≤ finset.univ.sum (λ i, |int.fract (b.repr m i)| * ‖b i‖)
          : by simp_rw [norm_smul, real.norm_eq_abs]
    ... ≤ finset.univ.sum (λ j, ‖b j‖)
          : finset.sum_le_sum _,
    intros i _,
    rw int.abs_fract,
    refine le_trans (mul_le_mul_of_nonneg_right (le_of_lt (int.fract_lt_one _)) (norm_nonneg _)) _,
    rw one_mul,
end

end zspan

section lattice_basic

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables [finite_dimensional ℝ E] (L : submodule ℤ E)

example (hd : discrete_topology L) (hs : submodule.span ℝ (L : set E) = ⊤) : submodule.fg L :=
begin
  obtain ⟨s, ⟨h1, ⟨h2, h3⟩⟩⟩ := exists_linear_independent ℝ (L : set E),
  haveI : fintype s, { sorry, },
  have b : basis s ℝ E, { sorry, },

  refine submodule.fg_of_fg_map_of_fg_inf_ker (submodule.mkq (submodule.span ℤ (set.range b))) _ _,
  { suffices : (submodule.span ℤ (set.range b)).fg,
    { refine submodule.fg.map _ _,
      
      sorry, },

    sorry,
  },
  {
    sorry,

  },
end

#exit

example (hd : discrete_topology L) (hs : submodule.span ℝ (L : set E) = ⊤) : submodule.fg L :=
begin
  obtain ⟨b0, ⟨hbL, ⟨hbsp, hblin⟩⟩⟩ := exists_linear_independent ℝ (L : set E),
  haveI : fintype b0, { sorry, },
  have b : basis b0 ℝ E, { sorry, },

  refine submodule.fg_of_fg_map_of_fg_inf_ker (submodule.mkq (submodule.span ℤ b0)) _ _,
  { suffices : (submodule.map (submodule.span ℤ b0).mkq L).carrier.finite,
    { refine ⟨_, _⟩,
      use set.finite.to_finset this,
      rw set.finite.coe_to_finset,
      change submodule.span ℤ ↑(submodule.map (submodule.span ℤ b0).mkq L) =
        submodule.map (submodule.span ℤ b0).mkq L,
      rw submodule.span_eq, },

    rw ( by sorry : submodule.span ℤ b0 = submodule.span ℤ (set.range b)),
    let f := zspan.fract_quo_map b,

--    let f : E ⧸ (submodule.span ℤ b) → E :=
--    begin
--      intro x,
--      let y := (quot.exists_rep x).some,
--      use y - gen.floor_approx this y,
--    end,
    have hi : function.injective f, { sorry, },
    refine set.finite.of_finite_image _ (hi.inj_on _),

    sorry, },
  { have : L ⊓ linear_map.ker _ = submodule.span ℤ b0,
    { rw submodule.ker_mkq (submodule.span ℤ b0),
      rw inf_eq_right,
      rwa submodule.span_le, },
    rw this,
    exact submodule.fg_span (linear_independent.finite hblin), }
end

  #exit

  -- have := b.linear_independent,
  -- have := b.mem_span _,
  -- have t1 : ∀ v ∈ L, v ∈ submodule.span ℝ (L : set E), { sorry, },

--   have t2 : ∀ v ∈ L, v ∈ (submodule.span ℝ (set.range ⇑b) : set E),
--   { intros v hv,
--     have t1 : v ∈ submodule.span ℝ (L : set E) := submodule.subset_span hv,
-- --    have t2 := b.mem_span t1,
--     sorry,
--     },
  have : L ≤ (submodule.span ℝ (L : set E)), { sorry, },
  let L0 := submodule.map _ L,
  let f : (submodule.span ℝ (L : set E)) →ₗ[ℤ] (submodule.span ℤ (L : set E)) :=
  { to_fun := sorry,
    -- begin
    --   intro v,
    --   refine floor_approx b.linear_independent _,
    --   have := b.mem_span ⟨v, (t1 v) v.prop⟩,
    --   use v,
    --   exact (t1 v) v.prop,
    --   exact this,
    -- end,
    map_add' := sorry,
    map_smul' := sorry },
  -- make L a submodule of (submodule.span ℝ (L : set E))
  refine submodule.fg_of_fg_map_of_fg_inf_ker f _ _,

  sorry,
end

end lattice_basic

#exit

-- Don't you need E without ℚ (or ℝ) torsion?


example :
  ∀ r : ℝ, ((L : set (ι → ℝ)) ∩ metric.ball (0 : ι → ℝ) r).finite
  ↔ discrete_topology L :=
begin
  sorry
end

example (h : discrete_topology L) : countable L :=
begin
  sorry,
end

example (h : discrete_topology L) : module.free ℤ L :=
begin
  rw module.free_def,
  convert module.free_of_finite_type_torsion_free',

end
