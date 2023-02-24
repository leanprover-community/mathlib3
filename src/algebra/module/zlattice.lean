/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import analysis.normed_space.basic
import measure_theory.group.fundamental_domain
import measure_theory.measure.haar_of_basis

/-!
# ℤ-lattices
Let `E` be a finite dimensional real vector space. A (full) ℤ-lattice `L` of `E` is a discrete
subgroup of `E` such that `L` spans `E` over `ℝ`.

The ℤ-lattice `L` can be defined in two ways:
* For `b` a basis of `E`, then `L : submodule.span ℤ (set.range b)` is a ℤ-lattice of `E`.
* As `L : add_subgroup E` with the additional properties:
  `(hd : ∀ r : ℝ, (L ∩ (metric.closed_ball 0 r)).finite)`, that is `L` is discrete
  `(hs : submodule.span ℝ (L : set E) = ⊤)`, that is `L` spans `E`.

## Main definitions and results
* `zspan.is_add_fundamental_domain`: proves that the set defined by `zsapn.fundamental_domain` is
indeed a fundamental domain of the lattice.
-/

open_locale classical

noncomputable theory

section zspan

open measure_theory measurable_set submodule

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {ι : Type*} (b : basis ι ℝ E)

/-- The ℤ-lattice spanned by `b` admits `b` as a ℤ-basis. -/
def zspan.basis : basis ι ℤ (span ℤ (set.range b)) :=
basis.span (b.linear_independent.restrict_scalars (smul_left_injective ℤ (ne_zero.ne 1)))

@[simp]
lemma zspan.basis_apply (i : ι) : (zspan.basis b i : E) = b i :=
  by simp only [zspan.basis, basis.span_apply]

@[simp]
lemma zspan.repr_apply (m : span ℤ (set.range b)) [finite ι] (i : ι)  :
  ((zspan.basis b).repr m i : ℝ) = b.repr m i :=
begin
  casesI nonempty_fintype ι,
  rw ← congr_arg (coe : _ → E) (basis.sum_repr (zspan.basis b) m),
  simp only [coe_sum, coe_smul_of_tower, zspan.basis_apply, linear_equiv.map_sum,
    zsmul_eq_smul_cast ℝ, b.repr.map_smul, finsupp.single_apply, finset.sum_apply', basis.repr_self,
    finsupp.smul_single', mul_one, finset.sum_ite_eq', finset.mem_univ, if_true],
end

lemma zspan.mem_span_iff [finite ι] (m : E) :
  m ∈ span ℤ (set.range b) ↔ ∀ i, ∃ c : ℤ, b.repr m i = c :=
begin
  casesI nonempty_fintype ι,
  split,
  { exact λ hm i, ⟨(zspan.basis b).repr ⟨m, hm⟩ i, (zspan.repr_apply b ⟨m, hm⟩ i).symm⟩, },
  { intros h,
    rw ← b.sum_repr m,
    refine sum_mem _,
    intros i _,
    rw [(h i).some_spec, ← zsmul_eq_smul_cast ℝ],
    exact zsmul_mem (subset_span (set.mem_range_self i)) _, }
end

/-- The fundamental domain of the ℤ-lattice spanned by `b`. See `zspan.is_add_fundamental_domain`
for the proof that it is the fundamental domain. -/
def zspan.fundamental_domain : set E := { m | ∀ i : ι, b.repr m i ∈ set.Ico (0 : ℝ) 1 }

section fintype

variable [fintype ι]

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding down its coordinates on the basis `b`. -/
def zspan.floor_map : E → span ℤ (set.range b) :=
λ m, finset.univ.sum (λ i, int.floor (b.repr m i) • zspan.basis b i)

lemma zspan.floor_map_single (m : E) (i : ι) :
  b.repr (zspan.floor_map b m) i = int.floor (b.repr m i) :=
by simp only [zspan.floor_map, zsmul_eq_smul_cast ℝ, b.repr.map_smul, finsupp.single_apply,
  finset.sum_apply', basis.repr_self, finsupp.smul_single', mul_one, finset.sum_ite_eq',
  finset.mem_univ, if_true, coe_sum, coe_smul_of_tower, zspan.basis_apply, linear_equiv.map_sum]

/-- The map that sends a vector `E` to the fundamental domain of the lattice,
see `zspan.fract_mem_fundamental_domain`. -/
def zspan.fract_map : E → E := λ m, m - zspan.floor_map b m

@[simp]
lemma zspan.fract_map_single (m : E) (i : ι):
  b.repr (zspan.fract_map b m) i = int.fract (b.repr m i) :=
by rw [zspan.fract_map, map_sub, finsupp.coe_sub, pi.sub_apply, zspan.floor_map_single, int.fract]

@[simp]
lemma zspan.fract_map_zspan_add (m : E) (v : E) (h : v ∈ span ℤ (set.range b)) :
  zspan.fract_map b (v + m) = zspan.fract_map b m :=
begin
  refine (basis.ext_elem_iff b).mpr (λ i, _),
  simp_rw [zspan.fract_map_single, int.fract_eq_fract],
  use (zspan.basis b).repr ⟨v, h⟩ i,
  simp only [map_add, finsupp.coe_add, pi.add_apply, add_tsub_cancel_right, zspan.repr_apply,
    coe_mk],
end

lemma zspan.mem_fundamental_domain {x : E} :
  x ∈ (zspan.fundamental_domain b) ↔ zspan.fract_map b x = x :=
by simp only [basis.ext_elem_iff b, zspan.fundamental_domain, set.mem_Ico, set.mem_set_of_eq,
  zspan.fract_map_single, int.fract_eq_self]

lemma zspan.fract_map_mem_fundamental_domain (x : E) :
  zspan.fract_map b x ∈ zspan.fundamental_domain b :=
by simp only [zspan.mem_fundamental_domain, basis.ext_elem_iff b, zspan.fract_map_single,
  int.fract_fract, eq_self_iff_true, implies_true_iff]

lemma zspan.fract_map_eq_iff (m n : E) :
zspan.fract_map b m = zspan.fract_map b n ↔ m - n ∈ span ℤ (set.range b) :=
begin
  rw basis.ext_elem_iff b,
  simp only [int.fract_eq_fract, zspan.mem_span_iff, zspan.fract_map_single, linear_equiv.map_sub,
  finsupp.coe_sub, pi.sub_apply],
end

lemma zspan.fract_map_le (m : E) :
  ‖zspan.fract_map b m‖ ≤ finset.univ.sum (λ j, ‖b j‖) :=
begin
  calc
    ‖zspan.fract_map b m‖
        = ‖finset.univ.sum (λ i, b.repr (zspan.fract_map b m) i • b i)‖ : by rw b.sum_repr
    ... = ‖finset.univ.sum (λ i, int.fract (b.repr m i) • b i)‖ : by simp_rw zspan.fract_map_single
    ... ≤ finset.univ.sum (λ i, ‖int.fract (b.repr m i) • b i‖) : norm_sum_le _ _
    ... ≤ finset.univ.sum (λ i, ‖int.fract (b.repr m i)‖ * ‖b i‖) : by simp_rw norm_smul
    ... ≤ finset.univ.sum (λ j, ‖b j‖) : finset.sum_le_sum _,
    intros i _,
    rw [real.norm_eq_abs, int.abs_fract],
    refine le_trans (mul_le_mul_of_nonneg_right (le_of_lt (int.fract_lt_one _)) (norm_nonneg _)) _,
    rw one_mul,
end

end fintype

lemma zspan.metric.bounded_fundamental_domain [finite ι] :
  metric.bounded (zspan.fundamental_domain b) :=
begin
  casesI nonempty_fintype ι,
  use 2 * finset.univ.sum (λ j, ‖b j‖),
  intros x hx y hy,
  refine le_trans (dist_le_norm_add_norm x y) _,
  rw [← (zspan.mem_fundamental_domain b).mp hx, ← (zspan.mem_fundamental_domain b).mp hy],
  refine (add_le_add (zspan.fract_map_le b x) (zspan.fract_map_le b y)).trans _,
  linarith,
end

lemma zspan.measurable.fundamental_domain [measurable_space E] [opens_measurable_space E]
  [finite ι]:
  measurable_set (zspan.fundamental_domain b) :=
begin
  haveI : finite_dimensional ℝ E := finite_dimensional.of_fintype_basis b,
  let f := (finsupp.linear_equiv_fun_on_finite ℝ ℝ ι).to_linear_map.comp b.repr.to_linear_map,
  let D : set (ι → ℝ) := set.pi set.univ (λ i : ι, (set.Ico (0 : ℝ) 1)),
  rw ( _ : zspan.fundamental_domain b = f⁻¹' D),
  { refine measurable_set_preimage (linear_map.continuous_of_finite_dimensional f).measurable _,
    exact pi set.univ.to_countable (λ (i : ι) (H : i ∈ set.univ), measurable_set_Ico), },
  { ext,
    simp only [zspan.fundamental_domain, set.mem_set_of_eq, linear_map.coe_comp,
      linear_equiv.coe_to_linear_map, set.mem_preimage, function.comp_app, set.mem_univ_pi,
      finsupp.linear_equiv_fun_on_finite_apply], },
end

lemma zspan.is_add_fundamental_domain [finite ι] [measurable_space E] [opens_measurable_space E]
  (μ : measure E) :
  is_add_fundamental_domain (span ℤ (set.range b)).to_add_subgroup
    (zspan.fundamental_domain b) μ :=
{ null_measurable_set := null_measurable_set (zspan.measurable.fundamental_domain b),
  ae_covers :=
  begin
    casesI nonempty_fintype ι,
    refine filter.eventually_of_forall (λ x, ⟨- zspan.floor_map b x, _⟩),
    rw (_ : -zspan.floor_map b x +ᵥ x = zspan.fract_map b x),
    { exact zspan.fract_map_mem_fundamental_domain b x, },
    { simp only [vadd_def, zspan.fract_map, add_subgroup_class.coe_neg, neg_add_eq_sub,
        vadd_eq_add], },
  end,
  ae_disjoint :=
  begin
    casesI nonempty_fintype ι,
    refine λ v w hvw, disjoint.ae_disjoint (λ s hsv hsw x hx, _),
    refine hvw (subtype.ext_iff.mpr ((basis.ext_elem_iff b).mpr (λ i, _))),
    obtain ⟨a, ⟨ha1, ha2⟩⟩ := hsv hx,
    obtain ⟨c, ⟨hc1, hc2⟩⟩ := hsw hx,
    rw (by { simp only [vadd_def, ←eq_sub_iff_add_eq, vadd_eq_add] at ha2, exact ha2, } :
      (v : E) = x - a),
    rw (by { simp only [vadd_def, ←eq_sub_iff_add_eq, vadd_eq_add] at hc2, exact hc2, } :
      (w : E) = x - c),
    rw ( _ : a = zspan.fract_map b x),
    { rw ( _ : c = zspan.fract_map b x),
      convert congr_arg (zspan.fract_map b) hc2,
      simp only [vadd_def, zspan.fract_map_zspan_add b c w (set_like.coe_mem w),
        (zspan.mem_fundamental_domain b).mp hc1, vadd_eq_add], },
    { convert congr_arg (zspan.fract_map b) ha2,
      simp only [vadd_def, zspan.fract_map_zspan_add b a v (set_like.coe_mem v),
        (zspan.mem_fundamental_domain b).mp ha1, vadd_eq_add], },
  end }

end zspan
