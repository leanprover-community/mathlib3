/-
 Copyright (c) 2023 Xavier Roblot. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Xavier Roblot
 -/
import analysis.normed_space.basic
import measure_theory.group.fundamental_domain

/-!
# ℤ-lattices
A ℤ-lattice is a discrete subgroup of a finite vector space `E` usually over ℚ or ℝ that spans the
full space (we consider only full lattices). See : https://en.wikipedia.org/wiki/Lattice_(group)

A ℤ-lattice `L` can be defined in two ways:
- `L : submodule.span ℤ (set.range b)` where `b` is a basis of `E`
- `L : submodule ℤ E` with the additional properties:
  `(hd : ∀ r : ℝ, (L ∩ (metric.closed_ball 0 r)).finite)`, that is `L` is discrete
  `(hs : submodule.span ℝ (L : set E) = ⊤)`, that is `L` spans `E`

## Main results
- `zspan.is_add_fundamental_domain`: the fundamental domain of a lattice
-/

open_locale classical

noncomputable theory

section zspan

-- TODO. Generalize also to floor_ring (field?)
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {ι : Type*} (b : basis ι ℝ E)

/-- The lattice defined by the basis `b`. -/
def zspan.basis : basis ι ℤ (submodule.span ℤ (set.range b)) :=
basis.span (b.linear_independent.restrict_scalars (smul_left_injective ℤ (by norm_num)))

lemma zspan.basis_eq (i : ι) : (zspan.basis b i : E) = b i :=
  by simp only [zspan.basis, basis.span_apply]

variable [fintype ι]

lemma zspan.repr_eq (m : submodule.span ℤ (set.range b)) (i : ι)  :
   b.repr m i = ((zspan.basis b).repr m i : ℝ) :=
begin
  rw ← sub_eq_zero,
  revert i,
  apply fintype.linear_independent_iff.mp b.linear_independent,
  simp_rw sub_smul,
  rw finset.sum_sub_distrib,
  rw sub_eq_zero,
  rw basis.sum_repr,
  simp_rw ← zspan.basis_eq b,
  simp_rw ← zsmul_eq_smul_cast ℝ _ _,
  rw ← congr_arg (coe : _ → E) ((zspan.basis b).sum_repr m),
  rw submodule.coe_sum,
  simp_rw set_like.coe_smul,
end

lemma zspan.mem_span_iff (m : E) :
  m ∈ submodule.span ℤ (set.range b) ↔ ∀ i, ∃ c : ℤ, b.repr m i = c :=
begin
  split,
  { intros hm i,
    use (zspan.basis b).repr ⟨m, hm⟩ i,
    convert zspan.repr_eq b ⟨m, hm⟩ i, },
  { intro h,
    rw ← b.sum_repr m,
    refine sum_mem _,
    intros i _,
    obtain ⟨c, hc⟩ := h i,
    rw hc,
    rw ← zsmul_eq_smul_cast ℝ _ _,
    refine zsmul_mem _ _,
    exact submodule.subset_span (set.mem_range_self i),  }
end

/-- The map that sends a vector of the ambiant space to the element of the lattice obtained
by round down its coordinate on the basis `b`. -/
def zspan.floor_map : E → submodule.span ℤ (set.range b) :=
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
  simp_rw ← zspan.basis_eq,
  simp_rw zspan.repr_eq,
  simp_rw ← zsmul_eq_smul_cast ℝ _ _,
  rw_mod_cast basis.sum_repr (zspan.basis b) (zspan.floor_map b m),
  refl,
end

/-- The map that sends a vector of the ambiant space to the fundamental domain of the lattice. -/
def zspan.fract_map : E → E := λ m, m - zspan.floor_map b m

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
  zspan.fract_map b m = zspan.fract_map b n ↔ m - n ∈ submodule.span ℤ (set.range b) :=
begin
  have : zspan.fract_map b m = zspan.fract_map b n ↔ ∀ i, ∃ z : ℤ, b.repr (m - n) i = z,
  { rw basis.ext_elem_iff b,
    simp_rw zspan.fract_map_single,
    simp_rw map_sub,
    simp_rw finsupp.coe_sub,
    simp_rw pi.sub_apply,
    simp_rw int.fract_eq_fract, },
  rw this,
  exact (zspan.mem_span_iff b (m - n)).symm,
end

/-- The map between `E` quotiented by the lattice and its fundamental domain. -/
def zspan.fract_quo_map : E ⧸ submodule.span ℤ (set.range b) → E :=
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

lemma zspan.fract_quo_map_eq (x : E) :
  (zspan.fract_quo_map b) (((submodule.span ℤ (set.range ⇑b)).mkq) x) = zspan.fract_map b x := rfl

lemma zspan.injective_fract_quo_map : function.injective (zspan.fract_quo_map b) :=
begin
  dsimp only [zspan.fract_quo_map],
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
        = ‖finset.univ.sum (λ i, b.repr (zspan.fract_map b m) i • b i)‖ : by rw b.sum_repr
    ... = ‖finset.univ.sum (λ i, int.fract (b.repr m i) • b i)‖ : by simp_rw zspan.fract_map_single
    ... ≤ finset.univ.sum (λ i, ‖int.fract (b.repr m i) • b i‖) : norm_sum_le _ _
    ... ≤ finset.univ.sum (λ i, |int.fract (b.repr m i)| * ‖b i‖)
        : by simp_rw [norm_smul, real.norm_eq_abs]
    ... ≤ finset.univ.sum (λ j, ‖b j‖) : finset.sum_le_sum _,
    intros i _,
    rw int.abs_fract,
    refine le_trans (mul_le_mul_of_nonneg_right (le_of_lt (int.fract_lt_one _)) (norm_nonneg _)) _,
    rw one_mul,
end

end zspan

section fundamental_domain

open measure_theory measurable_set

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {ι : Type*}  (b : basis ι ℝ E)

instance zspan.vadd : has_vadd (submodule.span ℤ (set.range b)) E := ⟨ λ s m, s + m ⟩

@[simp]
lemma zspan.vadd_eq_add (m : E) (v : submodule.span ℤ (set.range b)) :
  v +ᵥ m = v + m := rfl

/-- The fundamental domain of the lattice. -/
def zspan.fundamental_domain : set E := { m | ∀ i : ι, b.repr m i ∈ set.Ico (0 : ℝ) 1 }

variable [fintype ι]

-- TODO. use this to simplify proof of is_add_fundamental_domain
lemma zspan.mem_fundamental_domain {x : E} :
  x ∈ (zspan.fundamental_domain b) ↔ zspan.fract_map b x = x :=
begin
  rw basis.ext_elem_iff b,
  simp only [zspan.fundamental_domain, set.mem_Ico, set.mem_set_of_eq, zspan.fract_map_single,
    int.fract_eq_self],
end

lemma zspan.metric.bounded_fundamental_domain :
  metric.bounded (zspan.fundamental_domain b) :=
begin
  use 2 * finset.univ.sum (λ j, ‖b j‖),
  intros x hx y hy,
  have : ‖x‖ ≤ finset.univ.sum (λ j, ‖b j‖),
  { convert zspan.fract_map_le b x,
    exact ((zspan.mem_fundamental_domain b).mp hx).symm, },
  have : ‖y‖ ≤ finset.univ.sum (λ j, ‖b j‖),
  { convert zspan.fract_map_le b y,
    exact ((zspan.mem_fundamental_domain b).mp hy).symm, },
  refine le_trans (dist_le_norm_add_norm x y) _,
  linarith,
end

lemma zspan.is_add_fundamental_domain [measurable_space E] [opens_measurable_space E]
  (μ : measure E) :
  is_add_fundamental_domain (submodule.span ℤ (set.range b)).to_add_subgroup
    (zspan.fundamental_domain b) μ :=
{ null_measurable_set :=
  begin
    haveI : finite_dimensional ℝ E := finite_dimensional.of_fintype_basis b,
    refine null_measurable_set _,
    let D : set (ι → ℝ) := set.pi set.univ (λ i : ι, (set.Ico (0 : ℝ) (1 : ℝ))),
    have t1 : measurable_set D,
    { refine pi set.univ.to_countable (λ (i : ι) (H : i ∈ set.univ), measurable_set_Ico), },
    let f := (finsupp.linear_equiv_fun_on_finite ℝ ℝ ι).to_linear_map.comp b.repr.to_linear_map,
    have t2 : measurable f := (linear_map.continuous_of_finite_dimensional f).measurable,
    have t3 : measurable_set (f⁻¹' D) := t2 t1,
    convert t3,
    ext,
    dsimp only [zspan.fundamental_domain, f],
    simp only [set.mem_set_of_eq, set.mem_preimage, set.mem_univ_pi, linear_map.coe_comp,
      linear_equiv.coe_to_linear_map, function.comp_app, finsupp.linear_equiv_fun_on_finite_apply],
  end,
  ae_covers :=
  begin
    refine filter.eventually_of_forall _,
    intro x,
    use - zspan.floor_map b x,
    have : -zspan.floor_map b x +ᵥ x = zspan.fract_map b x,
    { simp only [zspan.fract_map, zspan.vadd_eq_add, add_subgroup_class.coe_neg],
      abel, },
    rw this,
    intro i,
    rw zspan.fract_map_single,
    simp only [int.fract_lt_one, set.mem_Ico, int.fract_nonneg, and_self],
  end,
  ae_disjoint :=
  begin
    intros v w hvw,
    refine disjoint.ae_disjoint _,
    intros s hsv hsw x hx,
    obtain ⟨a, ⟨ha1, ha2⟩⟩ := hsv hx,
    obtain ⟨c, ⟨hc1, hc2⟩⟩ := hsw hx,
    have t1 := ha2.trans hc2.symm,
    simp_rw zspan.vadd_eq_add at t1,
    have t2 : ∀ i, (b.repr a) i = (b.repr c) i,
    { intro i,
      have t4 := congr_arg (λ z, b.repr z i) t1,
      dsimp only at t4,
      rw [map_add, map_add] at t4,
      rw [finsupp.coe_add, pi.add_apply, finsupp.coe_add, pi.add_apply] at t4,
      have t5 := congr_arg int.fract t4,
      have t6 : ∃ n : ℤ, b.repr v i = n := (zspan.mem_span_iff b v).1 (set_like.coe_mem v) i,
      obtain ⟨n, hn⟩ := t6,
      rw hn at t5,
      have t7 : ∃ m : ℤ, b.repr w i = m := (zspan.mem_span_iff b w).1 (set_like.coe_mem w) i,
      obtain ⟨m, hm⟩ := t7,
      rw hm at t5,
      rw [int.fract_int_add, int.fract_int_add] at t5,
      rw int.fract_eq_self.2 (ha1 i) at t5,
      rwa int.fract_eq_self.2 (hc1 i) at t5, },
    have t3 : ∀ i, b.repr v i = b.repr w i,
    { intro i,
      have t4 := congr_arg (λ z, b.repr z i) t1,
      simp_rw map_add at t4,
      simp_rw [finsupp.coe_add, pi.add_apply] at t4,
      rw t2 i at t4,
      rwa add_left_inj at t4, },
    rw ← basis.ext_elem_iff b at t3,
    rw ← subtype.ext_iff at t3,
    exact hvw t3,
  end
}

end fundamental_domain
