/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import analysis.normed.order.basic
import linear_algebra.finite_dimensional
import measure_theory.group.fundamental_domain

/-!
# ℤ-lattices

Let `E` be a finite dimensional vector space over a `normed_lattice_field` `K` that is also
a `floor_ring`, e.g. `ℚ` or `ℝ`. A (full) ℤ-lattice `L` of `E` is a discrete subgroup of `E` such
that `L` spans `E` over `K`.

The ℤ-lattice `L` can be defined in two ways:
* For `b` a basis of `E`, then `L : submodule.span ℤ (set.range b)` is a ℤ-lattice of `E`.
* As `L : add_subgroup E` with the additional properties:
  `(hd : ∀ r : ℝ, (L ∩ (metric.closed_ball 0 r)).finite)`, that is `L` is discrete
  `(hs : submodule.span ℝ (L : set E) = ⊤)`, that is `L` spans `E` over `K`.

## Main result
* `zspan.is_add_fundamental_domain`: for `L : submodule.span ℤ (set.range b)` a ℤ-lattice, proves
 that the set defined by `zspan.fundamental_domain` is indeed a fundamental domain.

-/

open_locale classical

noncomputable theory

namespace zspan

open measure_theory measurable_set submodule

variables {E ι : Type*}

-- section basis

-- variables {R K : Type*} [comm_ring R] [division_ring K] [algebra R K] [add_comm_group E]
--   [module K E] [module R E] [is_scalar_tower R K E] [no_zero_smul_divisors R K]
-- variables (b : basis ι K E)

-- variable (R)

-- /-- The R-lattice spanned by `b` admits `b` as a R-basis. -/
-- protected def basis : basis ι R (span R (set.range b)) :=
-- basis.span (b.linear_independent.restrict_scalars (smul_left_injective R (ne_zero.ne 1)))

-- @[simp]
-- lemma basis_apply (i : ι) : (zspan.basis R b i : E) = b i :=
--   by simp only [zspan.basis, basis.span_apply]

-- @[simp]
-- lemma repr_apply (m : span R (set.range b)) [finite ι] (i : ι)  :
--   algebra_map R K ((zspan.basis R b).repr m i) = b.repr m i :=
-- begin
--   casesI nonempty_fintype ι,
--   rw ← congr_arg (coe : _ → E) (basis.sum_repr (zspan.basis R b) m),
--   simp_rw [coe_sum, coe_smul_of_tower, basis_apply, linear_equiv.map_sum,
--     ← is_scalar_tower.algebra_map_smul K, b.repr.map_smul, basis.repr_self, algebra_map_smul,
--     finsupp.smul_single, finset.sum_apply', algebra.algebra_map_eq_smul_one, finsupp.single_apply,
--     finset.sum_ite_eq', finset.mem_univ],
--   refl,
-- end

-- lemma mem_span_iff [finite ι] (m : E) :
--   m ∈ span R (set.range b) ↔ ∀ i, ∃ c : R, b.repr m i = algebra_map R K c :=
-- begin
--   casesI nonempty_fintype ι,
--   split,
--   { exact λ hm i, ⟨(zspan.basis R b).repr ⟨m, hm⟩ i, (repr_apply R b ⟨m, hm⟩ i).symm⟩, },
--   { intros h,
--     rw ← b.sum_repr m,
--     refine sum_mem (λ i _ , _),
--     rw [(h i).some_spec, @is_scalar_tower.algebra_map_smul R K],
--     exact smul_mem _ _ (subset_span (set.mem_range_self i)), }
-- end

-- end basis

section normed_lattice_field

variables {K : Type*} [normed_lattice_field K]
variables [normed_add_comm_group E] [normed_space K E]
variables (b : basis ι K E)

/-- The fundamental domain of the ℤ-lattice spanned by `b`. See `zspan.is_add_fundamental_domain`
for the proof that it is the fundamental domain. -/
def fundamental_domain : set E := { m | ∀ i : ι, b.repr m i ∈ set.Ico (0 : K) 1 }

variables [floor_ring K]

section fintype

variable [fintype ι]

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding down its coordinates on the basis `b`. -/
def floor : E → span ℤ (set.range b) :=
λ m, finset.univ.sum (λ i, int.floor (b.repr m i) • b.restrict_scalars ℤ i)

lemma floor_single (m : E) (i : ι) :
  b.repr (floor b m) i = int.floor (b.repr m i) :=
by simp only [floor, zsmul_eq_smul_cast K, b.repr.map_smul, finsupp.single_apply,
  finset.sum_apply', basis.repr_self, finsupp.smul_single', mul_one, finset.sum_ite_eq',
  finset.mem_univ, if_true, coe_sum, coe_smul_of_tower, basis.restrict_scalars_apply,
  linear_equiv.map_sum]

/-- The map that sends a vector `E` to the fundamental domain of the lattice,
see `zspan.fract_mem_fundamental_domain`. -/
def fract : E → E := λ m, m - floor b m

lemma fract_def (m : E) : fract b m = m - floor b m := rfl

@[simp]
lemma fract_single (m : E) (i : ι):
  b.repr (fract b m) i = int.fract (b.repr m i) :=
by rw [fract, map_sub, finsupp.coe_sub, pi.sub_apply, floor_single, int.fract]

@[simp]
lemma fract_zspan_add (m : E) {v : E} (h : v ∈ span ℤ (set.range b)) :
  fract b (v + m) = fract b m :=
begin
  refine (basis.ext_elem_iff b).mpr (λ i, _),
  simp_rw [fract_single, int.fract_eq_fract],
  use (b.restrict_scalars ℤ).repr ⟨v, h⟩ i,
  rw [map_add, finsupp.coe_add, pi.add_apply, add_tsub_cancel_right,
    ← (eq_int_cast (algebra_map ℤ K) _), basis.restrict_scalars_repr_apply, coe_mk],
end

lemma mem_fundamental_domain {x : E} :
  x ∈ (fundamental_domain b) ↔ fract b x = x :=
by simp only [basis.ext_elem_iff b, fundamental_domain, set.mem_Ico, set.mem_set_of_eq,
  fract_single, int.fract_eq_self]

lemma fract_mem_fundamental_domain (x : E) :
  fract b x ∈ fundamental_domain b :=
by simp only [mem_fundamental_domain, basis.ext_elem_iff b, fract_single, int.fract_fract,
  eq_self_iff_true, implies_true_iff]

lemma fract_eq_iff (m n : E) :
  fract b m = fract b n ↔ -m + n ∈ span ℤ (set.range b) :=
begin
  rw [eq_comm, basis.ext_elem_iff b],
  simp only [int.fract_eq_fract, fract_single],
  simp_rw [basis.restrict_scalars_mem_span_iff, sub_eq_neg_add, map_add, linear_equiv.map_neg,
    finsupp.coe_add, finsupp.coe_neg, pi.add_apply, pi.neg_apply,
    ← (eq_int_cast (algebra_map ℤ K) _)],
end

lemma fract_le (m : E) :
  ‖fract b m‖ ≤ finset.univ.sum (λ j, ‖b j‖) :=
begin
  calc
    ‖fract b m‖
        = ‖finset.univ.sum (λ i, b.repr (fract b m) i • b i)‖ : by rw b.sum_repr
    ... = ‖finset.univ.sum (λ i, int.fract (b.repr m i) • b i)‖ : by simp_rw fract_single
    ... ≤ finset.univ.sum (λ i, ‖int.fract (b.repr m i) • b i‖) : norm_sum_le _ _
    ... ≤ finset.univ.sum (λ i, ‖int.fract (b.repr m i)‖ * ‖b i‖) : by simp_rw norm_smul
    ... ≤ finset.univ.sum (λ j, ‖b j‖) : finset.sum_le_sum (λ i _, _),
    suffices : ‖int.fract (((b.repr) m) i)‖ ≤ 1,
    { convert mul_le_mul_of_nonneg_right this (norm_nonneg _ : 0 ≤ ‖b i ‖),
      exact (one_mul _).symm, },
    rw (norm_one.symm : 1 = ‖(1 : K)‖),
    apply norm_le_norm_of_abs_le_abs,
    rw [abs_one, int.abs_fract],
    exact le_of_lt (int.fract_lt_one _),
end

end fintype

lemma fundamental_domain_bounded [finite ι] :
  metric.bounded (fundamental_domain b) :=
begin
  casesI nonempty_fintype ι,
  use 2 * finset.univ.sum (λ j, ‖b j‖),
  intros x hx y hy,
  refine le_trans (dist_le_norm_add_norm x y) _,
  rw [← (mem_fundamental_domain b).mp hx, ← (mem_fundamental_domain b).mp hy],
  refine (add_le_add (fract_le b x) (fract_le b y)).trans _,
  rw ← two_mul,
end

lemma exist_unique_vadd_mem_fundamental_domain [finite ι] (x : E) :
  ∃! v : span ℤ (set.range b), v +ᵥ x ∈ fundamental_domain b :=
begin
  casesI nonempty_fintype ι,
  refine ⟨-floor b x, _, _⟩,
  { simp_rw [fundamental_domain, set.mem_Ico, vadd_def, vadd_eq_add, add_subgroup_class.coe_neg,
    neg_add_eq_sub, ← fract_def],
    simp only [fract_single, int.fract_nonneg, int.fract_lt_one, true_and, set.mem_set_of_eq,
      implies_true_iff], },
  { intros y _,
    rwa [subtype.ext_iff, ← add_right_inj x, add_subgroup_class.coe_neg, ← sub_eq_add_neg,
      ← fract_def, ← fract_zspan_add b _ (subtype.mem y), add_comm, ← vadd_eq_add, ← vadd_def,
      eq_comm, ← mem_fundamental_domain], },
end

end normed_lattice_field

section real

variables [normed_add_comm_group E] [normed_space ℝ E]
variables (b : basis ι ℝ E)

@[measurability]
lemma fundamental_domain_measurable_set [measurable_space E] [opens_measurable_space E]
  [finite ι]:
  measurable_set (fundamental_domain b) :=
begin
  haveI : finite_dimensional ℝ E := finite_dimensional.of_fintype_basis b,
  let f := (finsupp.linear_equiv_fun_on_finite ℝ ℝ ι).to_linear_map.comp b.repr.to_linear_map,
  let D : set (ι → ℝ) := set.pi set.univ (λ i : ι, (set.Ico (0 : ℝ) 1)),
  rw ( _ : fundamental_domain b = f⁻¹' D),
  { refine measurable_set_preimage (linear_map.continuous_of_finite_dimensional f).measurable _,
    exact pi set.univ.to_countable (λ (i : ι) (H : i ∈ set.univ), measurable_set_Ico), },
  { ext,
    simp only [fundamental_domain, set.mem_set_of_eq, linear_map.coe_comp,
      linear_equiv.coe_to_linear_map, set.mem_preimage, function.comp_app, set.mem_univ_pi,
      finsupp.linear_equiv_fun_on_finite_apply], },
end

protected lemma is_add_fundamental_domain [finite ι] [measurable_space E]
  [opens_measurable_space E] (μ : measure E) :
  is_add_fundamental_domain (span ℤ (set.range b)).to_add_subgroup (fundamental_domain b) μ :=
begin
  casesI nonempty_fintype ι,
  exact is_add_fundamental_domain.mk' (null_measurable_set (fundamental_domain_measurable_set b))
    (λ x, exist_unique_vadd_mem_fundamental_domain b x),
end

end real

end zspan
