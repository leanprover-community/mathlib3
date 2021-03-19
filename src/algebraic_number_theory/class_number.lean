/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/
import algebra.big_operators.finsupp
import algebra.floor
import algebraic_number_theory.class_number.admissible_absolute_value
import algebraic_number_theory.function_field
import algebraic_number_theory.number_field
import data.polynomial.field_division
import group_theory.quotient_group
import linear_algebra.determinant
import linear_algebra.free_module
import linear_algebra.matrix
import ring_theory.class_group
import ring_theory.dedekind_domain
import ring_theory.fractional_ideal
import algebraic_number_theory.class_number.det
import algebraic_number_theory.class_number.integral_closure

/-!
# Class numbers of global fields

In this file, we use the notion of "admissible absolute value" to prove
finiteness of the class group for number fields and function fields,
and define `class_number` as the order of this group.

## Main definitions

 - `class_group.fintype_of_admissible`: if `R` has an admissible absolute value,
   its integral closure has a finite class group
 - `number_field.class_number`: the class number of a number field is the (finite)
   cardinality of the class group of its ring of integers
 - `function_field.class_number`: the class number of a number field is the (finite)
   cardinality of the class group of its ring of integers
-/

namespace class_group

open ring

open_locale big_operators

section euclidean_domain

variables {R K L : Type*} [euclidean_domain R] [field K] [field L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L] [is_separable f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]

variables (L)

lemma integral_closure.dim_pos : 0 < integral_closure.dim L f :=
by { rw [← fintype.card_fin (integral_closure.dim L f), fintype.card_pos_iff],
     exact is_basis.nonempty_of_nontrivial (integral_closure.is_basis L f) }

/-- If `a : integral_closure R L` has coordinates `≤ y`, `norm a ≤ norm_bound L f abs * y ^ n`. -/
noncomputable def norm_bound (abs : absolute_value R ℤ) : ℤ :=
let n := integral_closure.dim L f,
    h : 0 < integral_closure.dim L f := integral_closure.dim_pos L f,
    m : ℤ := finset.max' (finset.univ.image (λ (ijk : fin _ × fin _ × fin _),
        abs (matrix.lmul
               (integral_closure.is_basis L f)
               (integral_closure.basis L f ijk.1)
               ijk.2.1
               ijk.2.2)))
        ⟨_, finset.mem_image.mpr ⟨⟨⟨0, h⟩, ⟨0, h⟩, ⟨0, h⟩⟩, finset.mem_univ _, rfl⟩⟩
in nat.factorial n • (n • m) ^ n

lemma norm_bound_pos (abs : absolute_value R ℤ) : 0 < norm_bound L f abs :=
begin
  obtain ⟨i, j, k, hijk⟩ : ∃ i j k,
    matrix.lmul (integral_closure.is_basis L f) (integral_closure.basis L f i) j k ≠ 0,
  { by_contra h,
    push_neg at h,
    apply (integral_closure.is_basis L f).ne_zero ⟨0, integral_closure.dim_pos L f⟩,
    apply (matrix.lmul _).injective_iff.mp (matrix.lmul_injective (integral_closure.is_basis L f)),
    ext j k,
    rw [h, matrix.zero_apply] },
  simp only [norm_bound, algebra.smul_def, ring_hom.eq_nat_cast, int.nat_cast_eq_coe_nat],
  apply mul_pos (int.coe_nat_pos.mpr (nat.factorial_pos _)),
  apply pow_pos (mul_pos (int.coe_nat_pos.mpr (integral_closure.dim_pos L f)) _),
  apply lt_of_lt_of_le (abs.pos hijk) (finset.le_max' _ _ _),
  exact finset.mem_image.mpr ⟨⟨i, j, k⟩, finset.mem_univ _, rfl⟩
end

lemma norm_bound_ne_zero (abs : absolute_value R ℤ) : norm_bound L f abs ≠ 0 :=
ne_of_gt (norm_bound_pos L f abs)

lemma norm_le (a : integral_closure R L) {abs : absolute_value R ℤ}
  {y : ℤ} (hy : ∀ k, abs ((integral_closure.is_basis L f).repr a k) ≤ y) :
  abs_norm f abs a ≤ norm_bound L f abs * y ^ (integral_closure.dim L f) :=
begin
  conv_lhs { rw ← sum_repr (integral_closure.is_basis L f) a },
  unfold abs_norm algebra.norm norm_bound,
  rw [monoid_hom.coe_mk, matrix.to_matrix_lmul_eq],
  simp only [alg_hom.map_sum, alg_hom.map_smul],
  convert det_sum_le finset.univ _ hy;
    try { simp only [finset.card_univ, fintype.card_fin] },
  { rw [algebra.smul_mul_assoc, ← mul_pow _ _ (integral_closure.dim L f)],
    conv_lhs { rw algebra.smul_mul_assoc } },
  { intros i j k,
    apply finset.le_max',
    exact finset.mem_image.mpr ⟨⟨i, j, k⟩, finset.mem_univ _, rfl⟩ },
end

lemma norm_lt {S : Type*} [linear_ordered_comm_ring S]
  (a : integral_closure R L) {abs : absolute_value R ℤ}
  {y : S} (hy : ∀ k, (abs ((integral_closure.is_basis L f).repr a k) : S) < y) :
  (abs_norm f abs a : S) < norm_bound L f abs * y ^ (integral_closure.dim L f) :=
begin
  have h : 0 < integral_closure.dim L f := integral_closure.dim_pos L f,
  have him : (finset.univ.image (λ k, abs ((integral_closure.is_basis L f).repr a k))).nonempty :=
    ⟨_, finset.mem_image.mpr ⟨⟨0, h⟩, finset.mem_univ _, rfl⟩⟩,
  set y' : ℤ := finset.max' _ him with y'_def,
  have hy' : ∀ k, abs ((integral_closure.is_basis L f).repr a k) ≤ y',
  { intro k,
    exact finset.le_max' _ _ (finset.mem_image.mpr ⟨k, finset.mem_univ _, rfl⟩) },
  have : (y' : S) < y,
  { rw [y'_def, finset.map_max' (show monotone (coe : ℤ → S), from λ x y h, int.cast_le.mpr h)],
    apply finset.max'_lt _ (him.image _),
    simp only [finset.mem_image, exists_prop],
    rintros _ ⟨x, ⟨k, -, rfl⟩, rfl⟩,
    exact hy k },
  have y'_nonneg : 0 ≤ y' := le_trans (abs.nonneg _) (hy' ⟨0, h⟩),
  apply lt_of_le_of_lt (int.cast_le.mpr (norm_le L f a hy')),
  simp only [int.cast_mul, int.cast_pow],
  apply mul_lt_mul' (le_refl _),
  { exact pow_lt_pow_of_lt_left this (int.cast_nonneg.mpr y'_nonneg) h },
  { exact pow_nonneg (int.cast_nonneg.mpr y'_nonneg) _ },
  { exact int.cast_pos.mpr (norm_bound_pos L f abs) },
  { apply_instance }
end

section

variables (L)
variables (abs : admissible_absolute_value R)

open admissible_absolute_value

include L f abs

/-- The `M` from the proof of thm 5.4.

Should really be `abs.card (nat.ceil_nth_root _ _)`, but nth_root _ x ≤ x so this works too.
-/
noncomputable def cardM : ℕ :=
(abs.card (norm_bound L f abs ^ (-1 / (integral_closure.dim L f) : ℝ)))^(integral_closure.dim L f)

variables [infinite R]

/-- In the following results, we need a large set of distinct elements of `R`. -/
noncomputable def distinct_elems : fin (cardM L f abs).succ ↪ R :=
function.embedding.trans (fin.coe_embedding _).to_embedding (infinite.nat_embedding R)

/-- `finset_approx` is a finite set such that each fractional ideal in the integral closure
contains an element close to `finset_approx`. -/
noncomputable def finset_approx [decidable_eq R] : finset R :=
((finset.univ.product finset.univ)
  .image (λ (xy : fin _ × fin _), distinct_elems L f abs xy.1 - distinct_elems L f abs xy.2))
  .erase 0

lemma finset_approx.zero_not_mem [decidable_eq R] : (0 : R) ∉ finset_approx L f abs :=
finset.not_mem_erase _ _

@[simp] lemma mem_finset_approx [decidable_eq R] {x : R} :
  x ∈ finset_approx L f abs ↔
  ∃ i j, i ≠ j ∧ distinct_elems L f abs i - distinct_elems L f abs j = x :=
begin
  simp only [finset_approx, finset.mem_erase, finset.mem_image],
  split,
  { rintros ⟨hx, ⟨i, j⟩, _, rfl⟩,
    refine ⟨i, j, _, rfl⟩,
    rintro rfl,
    simpa using hx },
  { rintros ⟨i, j, hij, rfl⟩,
    refine ⟨_, ⟨i, j⟩, finset.mem_product.mpr ⟨finset.mem_univ _, finset.mem_univ _⟩, rfl⟩,
    rw [ne.def, sub_eq_zero],
    exact λ h, hij ((distinct_elems L f abs).injective h) }
end

section

open real

local attribute [-instance] real.decidable_eq

/-- We can approximate `a / b : L` with `q / r`, where `r` has finitely many options for `L`. -/
theorem exists_mem_finset_approx [decidable_eq R]
  (a : integral_closure R L) {b} (hb : b ≠ (0 : R)) :
  ∃ (q : integral_closure R L) (r ∈ finset_approx L f abs),
    abs_norm f abs (r • a - b • q) < abs_norm f abs (algebra_map R (integral_closure R L) b) :=
begin
  set ε : ℝ := norm_bound L f abs ^ (-1 / (integral_closure.dim L f) : ℝ) with ε_eq,
  have hε : 0 < ε := real.rpow_pos_of_pos (int.cast_pos.mpr (norm_bound_pos L f abs)) _,
  have ε_le : (norm_bound L f abs : ℝ) * (abs b • ε) ^ integral_closure.dim L f ≤
                (abs b ^ integral_closure.dim L f),
  { have := integral_closure.dim_pos L f,
    have := norm_bound_pos L f abs,
    have := abs.nonneg b,
    rw [ε_eq, algebra.smul_def, ring_hom.eq_int_cast, ← rpow_nat_cast, mul_rpow, ← rpow_mul,
        div_mul_cancel, rpow_neg_one, mul_left_comm, mul_inv_cancel, mul_one, rpow_nat_cast];
      try { norm_cast, linarith },
    { apply rpow_nonneg_of_nonneg,
      norm_cast,
      linarith } },
  let μ : fin (cardM L f abs).succ ↪ R := distinct_elems L f abs,
  set s := (integral_closure.is_basis L f).repr a,
  have s_eq : ∀ i, s i = (integral_closure.is_basis L f).repr a i := λ i, rfl,
  set qs := λ j i, (μ j * s i) / b,
  have q_eq : ∀ j i, qs j i = (μ j * s i) / b := λ i j, rfl,
  set rs := λ j i, (μ j * s i) % b with r_eq,
  have r_eq : ∀ j i, rs j i = (μ j * s i) % b := λ i j, rfl,
  set c := integral_closure.basis L f,
  have c_eq : ∀ i, c i = integral_closure.basis L f i := λ i, rfl,
  have μ_eq : ∀ i j, μ j * s i = b * qs j i + rs j i,
  { intros i j,
    rw [q_eq, r_eq, euclidean_domain.div_add_mod], },
  have μ_mul_a_eq : ∀ j, μ j • a = b • ∑ i, qs j i • c i + ∑ i, rs j i • c i,
  { intro j,
    rw ← sum_repr (integral_closure.is_basis L f) a,
    simp only [finset.smul_sum, ← finset.sum_add_distrib],
    refine finset.sum_congr rfl (λ i _, _),
    rw [← c_eq, ← s_eq, ← mul_smul, μ_eq, add_smul, mul_smul] },

  obtain ⟨j, k, j_ne_k, hjk⟩ :=
    abs.exists_approx (integral_closure.dim L f) hε hb (λ j i, μ j * s i),
  have hjk' : ∀ i, (abs (rs k i - rs j i) : ℝ) < abs b • ε,
  { simpa only [r_eq] using hjk },
  set q := ∑ i, (qs k i - qs j i) • c i with q_eq,
  set r := μ k - μ j with r_eq,
  refine ⟨q, r, (mem_finset_approx L f abs).mpr _, _⟩,
  { exact ⟨k, j, j_ne_k.symm, rfl⟩ },
  have : r • a - b • q = (∑ (x : fin (integral_closure.dim L f)), (rs k x • c x - rs j x • c x)),
  { simp only [r_eq, sub_smul, μ_mul_a_eq, q_eq, finset.smul_sum, ← finset.sum_add_distrib,
               ← finset.sum_sub_distrib, smul_sub],
    refine finset.sum_congr rfl (λ x _, _),
    ring },
  rw [this, abs_norm_algebra_map],

  refine int.cast_lt.mp (lt_of_lt_of_le (norm_lt L f _ (λ i, lt_of_le_of_lt _ (hjk' i))) _),
  { apply le_of_eq,
    congr,
    simp_rw [linear_map.map_sum, linear_map.map_sub, linear_map.map_smul,
             finset.sum_apply', finsupp.sub_apply, finsupp.smul_apply',
             finset.sum_sub_distrib, is_basis.repr_self_apply, smul_eq_mul, mul_boole,
             finset.sum_ite_eq', finset.mem_univ, if_true] },
  { exact_mod_cast ε_le },
end

/-- We can approximate `a / b : L` with `q / r`, where `r` has finitely many options for `L`. -/
theorem exists_mem_finset_approx' [decidable_eq R]
  (a : integral_closure R L) {b} (hb : b ≠ (0 : integral_closure R L)) :
  ∃ (q : integral_closure R L) (r ∈ finset_approx L f abs),
  abs_norm f abs (r • a - q * b) < abs_norm f abs b :=
begin
  obtain ⟨a', b', hb', h⟩ := exists_eq_mul f a b hb,
  obtain ⟨q, r, hr, hqr⟩ := exists_mem_finset_approx L f abs a' hb',
  refine ⟨q, r, hr, _⟩,
  apply lt_of_mul_lt_mul_left _
    (show 0 ≤ abs_norm f abs (algebra_map R (integral_closure R L) b'), from abs.nonneg _),
  refine lt_of_le_of_lt (le_of_eq _) (mul_lt_mul hqr (le_refl (abs_norm f abs b))
    (abs.pos ((algebra.norm_ne_zero _).mpr hb)) (abs.nonneg _)),
  rw [← abs_norm_mul, ← abs_norm_mul, ← algebra.smul_def, smul_sub b', sub_mul, smul_comm, h,
      mul_comm b a', algebra.smul_mul_assoc r a' b, algebra.smul_mul_assoc b' q b]
end

end

end

end euclidean_domain

lemma monoid_hom.range_eq_top {G H : Type*} [group G] [group H] (f : G →* H) :
  f.range = ⊤ ↔ function.surjective f :=
⟨ λ h y, show y ∈ f.range, from h.symm ▸ subgroup.mem_top y,
  λ h, subgroup.ext (λ x, by simp [h x]) ⟩

section euclidean_domain

variables {R K L : Type*} [euclidean_domain R]
variables [field K] [field L]
variables (f : fraction_map R K)
variables [algebra f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]
variables (abs : admissible_absolute_value R)

/-- A nonzero ideal has an element of minimal norm. -/
lemma exists_min [finite_dimensional f.codomain L] [is_separable f.codomain L]
  (I : nonzero_ideal (integral_closure R L)) :
  ∃ b ∈ I.1, b ≠ 0 ∧ ∀ c ∈ I.1, abs_norm f abs c < abs_norm f abs b → c = 0 :=
begin
  haveI := classical.dec_eq L,
  obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ :=
    @int.exists_least_of_bdd (λ a, ∃ b ∈ I.1, b ≠ 0 ∧ abs_norm f abs b = a) _ _,
  { use [b, b_mem, b_ne_zero],
    intros c hc lt,
    by_contra c_ne_zero,
    exact not_le_of_gt lt (min _ ⟨c, hc, c_ne_zero, rfl⟩) },
  { use 0,
    rintros _ ⟨b, b_mem, b_ne_zero, rfl⟩,
    apply abs.nonneg },
  { obtain ⟨b, b_mem, b_ne_zero⟩ := I.1.ne_bot_iff.mp I.2,
    exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩ }
end

lemma is_scalar_tower.algebra_map_injective {R S T : Type*}
  [comm_semiring R] [comm_semiring S] [comm_semiring T]
  [algebra R S] [algebra S T] [algebra R T]
  [is_scalar_tower R S T]
  (hRS : function.injective (algebra_map R S)) (hST : function.injective (algebra_map S T)) :
  function.injective (algebra_map R T) :=
by { rw is_scalar_tower.algebra_map_eq R S T, exact hST.comp hRS }

lemma subalgebra.algebra_map_injective {R S : Type*} [comm_semiring R] [comm_semiring S]
  [algebra R S] (A : subalgebra R S) (h : function.injective (algebra_map R S)) :
  function.injective (algebra_map R A) :=
begin
  intros x y hxy,
  apply h,
  simp only [is_scalar_tower.algebra_map_apply R A S],
  exact congr_arg (coe : A → S) hxy
end

lemma integral_closure.algebra_map_injective :
  function.injective (algebra_map R (integral_closure R L)) :=
(subalgebra.algebra_map_injective _
  (is_scalar_tower.algebra_map_injective
    (show function.injective (algebra_map R f.codomain), from f.injective)
    (algebra_map f.codomain L).injective))

lemma cancel_monoid_with_zero.dvd_of_mul_dvd_mul_left {G₀ : Type*} [cancel_monoid_with_zero G₀]
  {a b c : G₀} (ha : a ≠ 0) (h : a * b ∣ a * c) :
  b ∣ c :=
begin
  obtain ⟨d, hd⟩ := h,
  refine ⟨d, mul_left_cancel' ha _⟩,
  rwa mul_assoc at hd
end

lemma ideal.dvd_of_mul_dvd_mul_left {R : Type*} [integral_domain R] [is_dedekind_domain R]
  {I J K : ideal R} (hI : I ≠ ⊥)
  (h : I * J ∣ I * K) :
  J ∣ K :=
cancel_monoid_with_zero.dvd_of_mul_dvd_mul_left hI h

lemma ideal.span_singleton_ne_bot {R : Type*} [comm_ring R] {a : R} (ha : a ≠ 0) :
  ideal.span ({a} : set R) ≠ ⊥ :=
begin
  rw [ne.def, ideal.span_eq_bot],
  push_neg,
  exact ⟨a, set.mem_singleton a, ha⟩
end

lemma finset.dvd_prod {ι M : Type*} [comm_monoid M] {x : ι} {s : finset ι}
  (hx : x ∈ s) (f : ι → M) :
  f x ∣ ∏ i in s, f i :=
multiset.dvd_prod (multiset.mem_map.mpr ⟨x, hx, rfl⟩)

lemma prod_finset_approx_ne_zero
  [finite_dimensional f.codomain L] [is_separable f.codomain L] [infinite R] [decidable_eq R] :
  algebra_map R (integral_closure R L) (∏ m in finset_approx L f abs, m) ≠ 0 :=
begin
  refine mt ((algebra_map R _).injective_iff.mp (integral_closure.algebra_map_injective f) _) _,
  simp only [finset.prod_eq_zero_iff, not_exists],
  rintros x hx rfl,
  exact finset_approx.zero_not_mem L f abs hx
end

lemma ne_zero_of_dvd_prod_finset_approx
  [finite_dimensional f.codomain L] [is_separable f.codomain L] [infinite R] [decidable_eq R]
  (J : ideal (integral_closure R L))
  (h : J ∣ ideal.span {algebra_map _ _ (∏ m in finset_approx L f abs, m)}) :
  J ≠ 0 :=
begin
  simp only [ne.def, ideal.zero_eq_bot, submodule.eq_bot_iff, not_forall, not_imp],
  refine ⟨(algebra_map _ _) (∏ (m : R) in finset_approx L f abs, m), _, _⟩,
  { exact ideal.le_of_dvd h (ideal.subset_span (set.mem_singleton _)) },
  apply prod_finset_approx_ne_zero
end

/-- Each class in the class group contains an ideal `J`
such that the product of `finset_approx.prod` is in `J`. -/
theorem exists_mk0_eq_mk0 [finite_dimensional f.codomain L] [is_separable f.codomain L]
  [infinite R] [decidable_eq R] (I : nonzero_ideal (integral_closure R L))
  [is_dedekind_domain (integral_closure R L)] :
  ∃ (J : nonzero_ideal (integral_closure R L)),
  class_group.mk0 (integral_closure.fraction_map_of_finite_extension L f) I =
  class_group.mk0 (integral_closure.fraction_map_of_finite_extension L f) J ∧
    J.1 ∣ ideal.span {algebra_map _ _ (∏ m in finset_approx L f abs, m)} :=
begin
  set m := ∏ m in finset_approx L f abs, m with m_eq,
  have hm : algebra_map R (integral_closure R L) m ≠ 0 := prod_finset_approx_ne_zero f abs,
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := exists_min f abs I,
  suffices : ideal.span {b} ∣ ideal.span {algebra_map _ _ m} * I.1,
  { obtain ⟨J, hJ⟩ := this,
    refine ⟨⟨J, _⟩, _, _⟩,
    { rintro rfl,
      rw [ideal.mul_bot, ideal.mul_eq_bot] at hJ,
      exact I.2 (hJ.resolve_left (mt ideal.span_singleton_eq_bot.mp hm)) },
    { rw class_group.mk0_eq_mk0_iff,
      exact ⟨algebra_map _ _ m, b, hm, b_ne_zero, hJ⟩ },
    apply ideal.dvd_of_mul_dvd_mul_left (ideal.span_singleton_ne_bot b_ne_zero),
    rw [ideal.dvd_iff_le, ← hJ, mul_comm, m_eq],
    apply ideal.mul_mono le_rfl,
    rw [ideal.span_le, set.singleton_subset_iff],
    exact b_mem },
  rw [ideal.dvd_iff_le, ideal.mul_le],
  intros r' hr' a ha,
  rw ideal.mem_span_singleton at ⊢ hr',
  obtain ⟨q, r, r_mem, lt⟩ := exists_mem_finset_approx' L f abs a b_ne_zero,
  apply @dvd_of_mul_left_dvd _ _ q,
  simp only [algebra.smul_def] at lt,
  rw ← sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left _ ha) (I.1.mul_mem_left _ b_mem)) lt),
  refine mul_dvd_mul_right (dvd_trans (ring_hom.map_dvd _ _) hr') _,
  exact finset.dvd_prod r_mem (λ x, x)
end

variables (L)

/-- `class_group.mk_dvd` is a specialization of `class_group.mk0` to (the finite set of)
ideals that contain `∏ m in finset_approx L f abs, m` -/
noncomputable def mk_dvd [finite_dimensional f.codomain L] [is_separable f.codomain L]
  [infinite R] [decidable_eq R] [is_dedekind_domain (integral_closure R L)]
  (J : {J : ideal (integral_closure R L) // J ∣
    ideal.span {algebra_map _ _ (∏ m in finset_approx L f abs, m)}}) :
  class_group (integral_closure.fraction_map_of_finite_extension L f) :=
class_group.mk0 _ ⟨J.1, ne_zero_of_dvd_prod_finset_approx f abs J.1 J.2⟩

lemma mk_dvd_surjective
  [finite_dimensional f.codomain L] [is_separable f.codomain L]
  [infinite R] [decidable_eq R] [is_dedekind_domain (integral_closure R L)] :
  function.surjective (class_group.mk_dvd L f abs) :=
begin
  intro I',
  obtain ⟨⟨I, hI⟩, rfl⟩ := class_group.mk0_surjective _ I',
  obtain ⟨J, mk0_eq_mk0, J_dvd⟩ := exists_mk0_eq_mk0 f abs ⟨I, hI⟩,
  exact ⟨⟨J, J_dvd⟩, mk0_eq_mk0.symm⟩
end

include abs

/-- The main theorem: the class group of an integral closure is finite.

Requires you to provide an "admissible absolute value", see `admissible_absolute_value.lean`
for a few constructions of those.
-/
noncomputable def finite_of_admissible [infinite R]
  [finite_dimensional f.codomain L] [is_separable f.codomain L]
  [is_dedekind_domain (integral_closure R L)] :
  fintype (class_group (integral_closure.fraction_map_of_finite_extension L f)) :=
begin
  haveI := classical.dec_eq (class_group (integral_closure.fraction_map_of_finite_extension L f)),
  haveI := classical.dec_eq R,
  refine @fintype.of_surjective _ _ _
       (ideal.finite_divisors _ _)
       (class_group.mk_dvd L f abs)
       (class_group.mk_dvd_surjective L f abs),
  rw [ne.def, ideal.span_singleton_eq_bot],
  exact prod_finset_approx_ne_zero f abs
end

end euclidean_domain

section integral_domain

variables {R K : Type*} [integral_domain R] [field K] (f : fraction_map R K)

end integral_domain

end class_group

namespace number_field

variables (K : Type*) [field K] [is_number_field K]

namespace ring_of_integers

open fraction_map
local attribute [class] algebra.is_algebraic

noncomputable instance : fintype (class_group (ring_of_integers.fraction_map K)) :=
class_group.finite_of_admissible K int.fraction_map int.admissible_abs

end ring_of_integers

/-- The class number of a number field is the (finite) cardinality of the class group. -/
noncomputable def class_number : ℕ := fintype.card (class_group (ring_of_integers.fraction_map K))

/-- The class number of a number field is `1` iff the ring of integers is a PID. -/
theorem class_number_eq_one_iff :
  class_number K = 1 ↔ is_principal_ideal_ring (ring_of_integers K) :=
card_class_group_eq_one_iff _

end number_field

namespace function_field_over

variables {K L : Type*} [field K] [fintype K] [field L] (f : fraction_map (polynomial K) L)
variables (F : Type*) [field F] [algebra f.codomain F] [function_field_over f F]
variables [decidable_eq K] [is_separable f.codomain F]

namespace ring_of_integers

open function_field_over

noncomputable instance : fintype (class_group (ring_of_integers.fraction_map f F)) :=
class_group.finite_of_admissible F f polynomial.admissible_card_pow_degree

end ring_of_integers

/-- The class number in a function field is the (finite) cardinality of the class group. -/
noncomputable def class_number : ℕ := fintype.card (class_group (ring_of_integers.fraction_map f F))

/-- The class number of a function field is `1` iff the ring of integers is a PID. -/
theorem class_number_eq_one_iff :
  class_number f F = 1 ↔ is_principal_ideal_ring (ring_of_integers f F) :=
card_class_group_eq_one_iff _

end function_field_over
