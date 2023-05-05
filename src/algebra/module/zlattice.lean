/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import analysis.normed.order.basic
import analysis.normed.order.lattice
import linear_algebra.finite_dimensional
import measure_theory.group.fundamental_domain

/-!
# ℤ-lattices

Let `E` be a finite dimensional vector space over a `normed_linear_ordered_field` `K` with a solid
norm and that is also a `floor_ring`, e.g. `ℚ` or `ℝ`. A (full) ℤ-lattice `L` of `E` is a discrete
subgroup of `E` such that `L` spans `E` over `K`.

The ℤ-lattice `L` can be defined in two ways:
* For `b` a basis of `E`, then `L : submodule.span ℤ (set.range b)` is a ℤ-lattice of `E`.
* As `L : add_subgroup E` with the additional properties:
  `∀ r : ℝ, (L ∩ metric.closed_ball 0 r).finite`, that is `L` is discrete
  `submodule.span ℝ (L : set E) = ⊤`, that is `L` spans `E` over `K`.

## Main result
* `zspan.is_add_fundamental_domain`: for `L : submodule.span ℤ (set.range b)` a ℤ-lattice, proves
 that the set defined by `zspan.fundamental_domain` is indeed a fundamental domain.

-/

open_locale big_operators classical

noncomputable theory

namespace zspan

open measure_theory measurable_set submodule

variables {E ι : Type*}

section normed_lattice_field

variables {K : Type*} [normed_linear_ordered_field K] [has_solid_norm K]
variables [normed_add_comm_group E] [normed_space K E]
variables (b : basis ι K E)

/-- The fundamental domain of the ℤ-lattice spanned by `b`. See `zspan.is_add_fundamental_domain`
for the proof that it is the fundamental domain. -/
def fundamental_domain : set E := { m | ∀ i, b.repr m i ∈ set.Ico (0 : K) 1 }

@[simp]
lemma mem_fundamental_domain {m : E} :
  m ∈ fundamental_domain b ↔ ∀ i, b.repr m i ∈ set.Ico (0 : K) 1 := iff.rfl

variables [floor_ring K]

section fintype

variable [fintype ι]

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding down its coordinates on the basis `b`. -/
def floor (m : E) : span ℤ (set.range b) := ∑ i, ⌊b.repr m i⌋ • b.restrict_scalars ℤ i

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding up its coordinates on the basis `b`. -/
def ceil (m : E) : span ℤ (set.range b) := ∑ i, ⌈b.repr m i⌉ • b.restrict_scalars ℤ i

@[simp]
lemma repr_floor_apply (m : E) (i : ι) :
  b.repr (floor b m) i = ⌊b.repr m i⌋ :=
by simp only [floor, zsmul_eq_smul_cast K, b.repr.map_smul, finsupp.single_apply, finset.sum_apply',
  basis.repr_self, finsupp.smul_single', mul_one, finset.sum_ite_eq', finset.mem_univ, if_true,
  coe_sum, coe_smul_of_tower, basis.restrict_scalars_apply, linear_equiv.map_sum]

@[simp]
lemma repr_ceil_apply (m : E) (i : ι) :
  b.repr (ceil b m) i = ⌈b.repr m i⌉ :=
by simp only [ceil, zsmul_eq_smul_cast K, b.repr.map_smul, finsupp.single_apply, finset.sum_apply',
  basis.repr_self, finsupp.smul_single', mul_one, finset.sum_ite_eq', finset.mem_univ, if_true,
  coe_sum, coe_smul_of_tower, basis.restrict_scalars_apply, linear_equiv.map_sum]

/-- The map that sends a vector `E` to the fundamental domain of the lattice,
see `zspan.fract_mem_fundamental_domain`. -/
def fract (m : E) : E := m - floor b m

lemma fract_apply (m : E) : fract b m = m - floor b m := rfl

@[simp]
lemma repr_fract_apply (m : E) (i : ι):
  b.repr (fract b m) i = int.fract (b.repr m i) :=
by rw [fract, map_sub, finsupp.coe_sub, pi.sub_apply, repr_floor_apply, int.fract]

@[simp]
lemma fract_fract (m : E) : fract b (fract b m) = fract b m :=
basis.ext_elem b (λ _, by simp only [repr_fract_apply, int.fract_fract])

@[simp]
lemma fract_zspan_add (m : E) {v : E} (h : v ∈ span ℤ (set.range b)) :
  fract b (v + m) = fract b m :=
begin
  refine (basis.ext_elem_iff b).mpr (λ i, _),
  simp_rw [repr_fract_apply, int.fract_eq_fract],
  use (b.restrict_scalars ℤ).repr ⟨v, h⟩ i,
  rw [map_add, finsupp.coe_add, pi.add_apply, add_tsub_cancel_right,
    ← (eq_int_cast (algebra_map ℤ K) _), basis.restrict_scalars_repr_apply, coe_mk],
end

@[simp]
lemma fract_add_zspan (m : E) {v : E} (h : v ∈ span ℤ (set.range b)) :
  fract b (m + v) = fract b m := by { rw [add_comm, fract_zspan_add b m h] }

variable {b}

lemma fract_eq_self {x : E} :
  fract b x = x ↔ x ∈ fundamental_domain b :=
by simp only [basis.ext_elem_iff b, repr_fract_apply, int.fract_eq_self, mem_fundamental_domain,
  set.mem_Ico]

variable (b)

lemma fract_mem_fundamental_domain (x : E) :
  fract b x ∈ fundamental_domain b := fract_eq_self.mp (fract_fract b _)

lemma fract_eq_fract (m n : E) :
  fract b m = fract b n ↔ -m + n ∈ span ℤ (set.range b) :=
begin
  rw [eq_comm, basis.ext_elem_iff b],
  simp_rw [repr_fract_apply, int.fract_eq_fract, eq_comm, basis.mem_span_iff_repr_mem,
    sub_eq_neg_add, map_add, linear_equiv.map_neg, finsupp.coe_add, finsupp.coe_neg, pi.add_apply,
    pi.neg_apply, ← (eq_int_cast (algebra_map ℤ K) _), set.mem_range],
end

lemma norm_fract_le (m : E) :
  ‖fract b m‖ ≤ ∑ i, ‖b i‖ :=
begin
  calc
    ‖fract b m‖ = ‖∑ i, b.repr (fract b m) i • b i‖ : by rw b.sum_repr
            ... = ‖∑ i, int.fract (b.repr m i) • b i‖ : by simp_rw repr_fract_apply
            ... ≤ ∑ i, ‖int.fract (b.repr m i) • b i‖ : norm_sum_le _ _
            ... ≤ ∑ i, ‖int.fract (b.repr m i)‖ * ‖b i‖ : by simp_rw norm_smul
            ... ≤ ∑ i, ‖b i‖ : finset.sum_le_sum (λ i _, _),
    suffices : ‖int.fract (((b.repr) m) i)‖ ≤ 1,
    { convert mul_le_mul_of_nonneg_right this (norm_nonneg _ : 0 ≤ ‖b i ‖),
      exact (one_mul _).symm, },
    rw (norm_one.symm : 1 = ‖(1 : K)‖),
    apply norm_le_norm_of_abs_le_abs,
    rw [abs_one, int.abs_fract],
    exact le_of_lt (int.fract_lt_one _),
end

section unique

variable [unique ι]

@[simp] lemma coe_floor_self (k : K) : (floor (basis.singleton ι K) k : K) = ⌊k⌋ :=
basis.ext_elem _ (λ _, by rw [repr_floor_apply, basis.singleton_repr, basis.singleton_repr])

@[simp] lemma coe_fract_self (k : K) : (fract (basis.singleton ι K) k : K) = int.fract k :=
basis.ext_elem _ (λ _, by rw [repr_fract_apply, basis.singleton_repr, basis.singleton_repr])

end unique

end fintype

lemma fundamental_domain_bounded [finite ι] :
  metric.bounded (fundamental_domain b) :=
begin
  casesI nonempty_fintype ι,
  use 2 * ∑ j, ‖b j‖,
  intros x hx y hy,
  refine le_trans (dist_le_norm_add_norm x y) _,
  rw [← fract_eq_self.mpr hx, ← fract_eq_self.mpr hy],
  refine (add_le_add (norm_fract_le b x) (norm_fract_le b y)).trans _,
  rw ← two_mul,
end

lemma vadd_mem_fundamental_domain [fintype ι] (y : span ℤ (set.range b)) (x : E) :
  y +ᵥ x ∈ fundamental_domain b ↔ y = -floor b x :=
by rw [subtype.ext_iff, ← add_right_inj x, add_subgroup_class.coe_neg, ← sub_eq_add_neg,
    ← fract_apply, ← fract_zspan_add b _ (subtype.mem y), add_comm, ← vadd_eq_add, ← vadd_def,
    eq_comm, ← fract_eq_self]

lemma exist_unique_vadd_mem_fundamental_domain [finite ι] (x : E) :
  ∃! v : span ℤ (set.range b), v +ᵥ x ∈ fundamental_domain b :=
begin
  casesI nonempty_fintype ι,
  refine ⟨-floor b x, _, λ y h, _⟩,
  { exact (vadd_mem_fundamental_domain b (-floor b x) x).mpr rfl, },
  { exact (vadd_mem_fundamental_domain b y x).mp h, },
end

end normed_lattice_field

section real

variables [normed_add_comm_group E] [normed_space ℝ E]
variables (b : basis ι ℝ E)

@[measurability]
lemma fundamental_domain_measurable_set [measurable_space E] [opens_measurable_space E]
  [finite ι] :
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
