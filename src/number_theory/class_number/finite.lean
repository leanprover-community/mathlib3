/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import linear_algebra.free_module.pid
import linear_algebra.matrix.absolute_value
import number_theory.class_number.admissible_absolute_value
import number_theory.function_field
import number_theory.number_field
import ring_theory.class_group
import ring_theory.norm

/-!
# Class numbers of global fields
In this file, we use the notion of "admissible absolute value" to prove
finiteness of the class group for number fields and function fields,
and define `class_number` as the order of this group.
## Main definitions
 - `class_group.fintype_of_admissible`: if `R` has an admissible absolute value,
   its integral closure has a finite class group
-/

open_locale big_operators
open_locale non_zero_divisors

namespace class_group

open ring

open_locale big_operators

section euclidean_domain

variables (R S K L : Type*) [euclidean_domain R] [comm_ring S] [is_domain S]
variables [field K] [field L]
variables [algebra R K] [is_fraction_ring R K]
variables [algebra K L] [finite_dimensional K L] [is_separable K L]
variables [algRL : algebra R L] [is_scalar_tower R K L]
variables [algebra R S] [algebra S L]
variables [ist : is_scalar_tower R S L] [iic : is_integral_closure S R L]

variables {R S} (abv : absolute_value R ℤ)
variables {ι : Type*} [decidable_eq ι] [fintype ι] (bS : basis ι R S)

/-- If `b` is an `R`-basis of `S` of cardinality `n`, then `norm_bound abv b` is an integer
such that for every `R`-integral element `a : S` with coordinates `≤ y`,
we have algebra.norm a ≤ norm_bound abv b * y ^ n`. (See also `norm_le` and `norm_lt`). -/
noncomputable def norm_bound : ℤ :=
let n := fintype.card ι,
    i : ι := nonempty.some bS.index_nonempty,
    m : ℤ := finset.max' (finset.univ.image (λ (ijk : ι × ι × ι),
        abv (algebra.left_mul_matrix bS (bS ijk.1) ijk.2.1 ijk.2.2)))
        ⟨_, finset.mem_image.mpr ⟨⟨i, i, i⟩, finset.mem_univ _, rfl⟩⟩
in nat.factorial n • (n • m) ^ n

lemma norm_bound_pos : 0 < norm_bound abv bS :=
begin
  obtain ⟨i, j, k, hijk⟩ : ∃ i j k,
    algebra.left_mul_matrix bS (bS i) j k ≠ 0,
  { by_contra h,
    push_neg at h,
    obtain ⟨i⟩ := bS.index_nonempty,
    apply bS.ne_zero i,
    apply (algebra.left_mul_matrix bS).injective_iff.mp (algebra.left_mul_matrix_injective bS),
    ext j k,
    simp [h, dmatrix.zero_apply] },
  simp only [norm_bound, algebra.smul_def, ring_hom.eq_nat_cast, int.nat_cast_eq_coe_nat],
  refine mul_pos (int.coe_nat_pos.mpr (nat.factorial_pos _)) _,
  refine pow_pos (mul_pos (int.coe_nat_pos.mpr (fintype.card_pos_iff.mpr ⟨i⟩)) _) _,
  refine lt_of_lt_of_le (abv.pos hijk) (finset.le_max' _ _ _),
  exact finset.mem_image.mpr ⟨⟨i, j, k⟩, finset.mem_univ _, rfl⟩
end

/-- If the `R`-integral element `a : S` has coordinates `≤ y` with respect to some basis `b`,
its norm is less than `norm_bound abv b * y ^ dim S`. -/
lemma norm_le (a : S) {y : ℤ} (hy : ∀ k, abv (bS.repr a k) ≤ y) :
  abv (algebra.norm R a) ≤ norm_bound abv bS * y ^ fintype.card ι :=
begin
  conv_lhs { rw ← bS.sum_repr a },
  rw [algebra.norm_apply, ← linear_map.det_to_matrix bS],
  simp only [algebra.norm_apply, alg_hom.map_sum, alg_hom.map_smul, linear_equiv.map_sum,
      linear_equiv.map_smul, algebra.to_matrix_lmul_eq, norm_bound, smul_mul_assoc, ← mul_pow],
  convert matrix.det_sum_smul_le finset.univ _ hy using 3,
  { rw [finset.card_univ, smul_mul_assoc, mul_comm] },
  { intros i j k,
    apply finset.le_max',
    exact finset.mem_image.mpr ⟨⟨i, j, k⟩, finset.mem_univ _, rfl⟩ },
end

/-- If the `R`-integral element `a : S` has coordinates `< y` with respect to some basis `b`,
its norm is strictly less than `norm_bound abv b * y ^ dim S`. -/
lemma norm_lt {T : Type*} [linear_ordered_comm_ring T]
  (a : S) {y : T} (hy : ∀ k, (abv (bS.repr a k) : T) < y) :
  (abv (algebra.norm R a) : T) < norm_bound abv bS * y ^ fintype.card ι :=
begin
  obtain ⟨i⟩ := bS.index_nonempty,
  have him : (finset.univ.image (λ k, abv (bS.repr a k))).nonempty :=
    ⟨_, finset.mem_image.mpr ⟨i, finset.mem_univ _, rfl⟩⟩,
  set y' : ℤ := finset.max' _ him with y'_def,
  have hy' : ∀ k, abv (bS.repr a k) ≤ y',
  { intro k,
    exact finset.le_max' _ _ (finset.mem_image.mpr ⟨k, finset.mem_univ _, rfl⟩) },
  have : (y' : T) < y,
  { rw [y'_def, ← finset.max'_image (show monotone (coe : ℤ → T), from λ x y h, int.cast_le.mpr h)],
    apply (finset.max'_lt_iff _ (him.image _)).mpr,
    simp only [finset.mem_image, exists_prop],
    rintros _ ⟨x, ⟨k, -, rfl⟩, rfl⟩,
    exact hy k },
  have y'_nonneg : 0 ≤ y' := le_trans (abv.nonneg _) (hy' i),
  apply (int.cast_le.mpr (norm_le abv bS a hy')).trans_lt,
  simp only [int.cast_mul, int.cast_pow],
  apply mul_lt_mul' (le_refl _),
  { exact pow_lt_pow_of_lt_left this
      (int.cast_nonneg.mpr y'_nonneg)
      (fintype.card_pos_iff.mpr ⟨i⟩) },
  { exact pow_nonneg (int.cast_nonneg.mpr y'_nonneg) _ },
  { exact int.cast_pos.mpr (norm_bound_pos abv bS) },
  { apply_instance }
end

/-- A nonzero ideal has an element of minimal norm. -/
lemma exists_min (I : (ideal S)⁰) :
  ∃ b ∈ (I : ideal S), b ≠ 0 ∧
  ∀ c ∈ (I : ideal S), abv (algebra.norm R c) < abv (algebra.norm R b) → c = (0 : S) :=
begin
  obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ := @int.exists_least_of_bdd
    (λ a, ∃ b ∈ (I : ideal S), b ≠ (0 : S) ∧ abv (algebra.norm R b) = a) _ _,
  { refine ⟨b, b_mem, b_ne_zero, _⟩,
    intros c hc lt,
    contrapose! lt with c_ne_zero,
    exact min _ ⟨c, hc, c_ne_zero, rfl⟩ },
  { use 0,
    rintros _ ⟨b, b_mem, b_ne_zero, rfl⟩,
    apply abv.nonneg },
  { obtain ⟨b, b_mem, b_ne_zero⟩ := (I : ideal S).ne_bot_iff.mp (non_zero_divisors.coe_ne_zero I),
    exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩ }
end

section is_admissible

variables (L) {abv} (adm : abv.is_admissible)

include adm

/-- If we have a large enough set of elements in `R^ι`, then there will be a pair
whose remainders are close together. We'll show that all sets of cardinality
at least `cardM bS adm` elements satisfy this condition.

The value of `cardM` is not at all optimal: for specific choices of `R`,
the minimum cardinality can be exponentially smaller.
-/
noncomputable def cardM : ℕ :=
adm.card (norm_bound abv bS ^ (-1 / (fintype.card ι) : ℝ)) ^ fintype.card ι

variables [infinite R]

/-- In the following results, we need a large set of distinct elements of `R`. -/
noncomputable def distinct_elems : fin (cardM bS adm).succ ↪ R :=
function.embedding.trans (fin.coe_embedding _).to_embedding (infinite.nat_embedding R)

variables [decidable_eq R]

/-- `finset_approx` is a finite set such that each fractional ideal in the integral closure
contains an element close to `finset_approx`. -/
noncomputable def finset_approx : finset R :=
((finset.univ.product finset.univ)
  .image (λ (xy : _ × _), distinct_elems bS adm xy.1 - distinct_elems bS adm xy.2))
  .erase 0

lemma finset_approx.zero_not_mem : (0 : R) ∉ finset_approx bS adm :=
finset.not_mem_erase _ _

@[simp] lemma mem_finset_approx {x : R} :
  x ∈ finset_approx bS adm ↔
  ∃ i j, i ≠ j ∧ distinct_elems bS adm i - distinct_elems bS adm j = x :=
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
    exact λ h, hij ((distinct_elems bS adm).injective h) }
end

section real

open real

local attribute [-instance] real.decidable_eq

/-- We can approximate `a / b : L` with `q / r`, where `r` has finitely many options for `L`. -/
theorem exists_mem_finset_approx (a : S) {b} (hb : b ≠ (0 : R)) :
  ∃ (q : S) (r ∈ finset_approx bS adm),
    abv (algebra.norm R (r • a - b • q)) < abv (algebra.norm R (algebra_map R S b)) :=
begin
  have dim_pos := fintype.card_pos_iff.mpr bS.index_nonempty,
  set ε : ℝ := norm_bound abv bS ^ (-1 / (fintype.card ι) : ℝ) with ε_eq,
  have hε : 0 < ε := real.rpow_pos_of_pos (int.cast_pos.mpr (norm_bound_pos abv bS)) _,
  have ε_le : (norm_bound abv bS : ℝ) * (abv b • ε) ^ fintype.card ι ≤
                (abv b ^ fintype.card ι),
  { have := norm_bound_pos abv bS,
    have := abv.nonneg b,
    rw [ε_eq, algebra.smul_def, ring_hom.eq_int_cast, ← rpow_nat_cast, mul_rpow, ← rpow_mul,
        div_mul_cancel, rpow_neg_one, mul_left_comm, mul_inv_cancel, mul_one, rpow_nat_cast];
      try { norm_cast, linarith },
    { apply rpow_nonneg_of_nonneg,
      norm_cast,
      linarith } },
  let μ : fin (cardM bS adm).succ ↪ R := distinct_elems bS adm,
  set s := bS.repr a,
  have s_eq : ∀ i, s i = bS.repr a i := λ i, rfl,
  set qs := λ j i, (μ j * s i) / b,
  have q_eq : ∀ j i, qs j i = (μ j * s i) / b := λ i j, rfl,
  set rs := λ j i, (μ j * s i) % b with r_eq,
  have r_eq : ∀ j i, rs j i = (μ j * s i) % b := λ i j, rfl,
  have μ_eq : ∀ i j, μ j * s i = b * qs j i + rs j i,
  { intros i j,
    rw [q_eq, r_eq, euclidean_domain.div_add_mod], },
  have μ_mul_a_eq : ∀ j, μ j • a = b • ∑ i, qs j i • bS i + ∑ i, rs j i • bS i,
  { intro j,
    rw ← bS.sum_repr a,
    simp only [finset.smul_sum, ← finset.sum_add_distrib],
    refine finset.sum_congr rfl (λ i _, _),
    rw [← s_eq, ← mul_smul, μ_eq, add_smul, mul_smul] },

  obtain ⟨j, k, j_ne_k, hjk⟩ := adm.exists_approx hε hb (λ j i, μ j * s i),
  have hjk' : ∀ i, (abv (rs k i - rs j i) : ℝ) < abv b • ε,
  { simpa only [r_eq] using hjk },
  set q := ∑ i, (qs k i - qs j i) • bS i with q_eq,
  set r := μ k - μ j with r_eq,
  refine ⟨q, r, (mem_finset_approx bS adm).mpr _, _⟩,
  { exact ⟨k, j, j_ne_k.symm, rfl⟩ },
  have : r • a - b • q = (∑ (x : ι), (rs k x • bS x - rs j x • bS x)),
  { simp only [r_eq, sub_smul, μ_mul_a_eq, q_eq, finset.smul_sum, ← finset.sum_add_distrib,
               ← finset.sum_sub_distrib, smul_sub],
    refine finset.sum_congr rfl (λ x _, _),
    ring },
  rw [this, algebra.norm_algebra_map_of_basis bS, abv.map_pow],

  refine int.cast_lt.mp ((norm_lt abv bS _ (λ i, lt_of_le_of_lt _ (hjk' i))).trans_le _),
  { apply le_of_eq,
    congr,
    simp_rw [linear_equiv.map_sum, linear_equiv.map_sub, linear_equiv.map_smul,
             finset.sum_apply', finsupp.sub_apply, finsupp.smul_apply,
             finset.sum_sub_distrib, basis.repr_self_apply, smul_eq_mul, mul_boole,
             finset.sum_ite_eq', finset.mem_univ, if_true] },
  { exact_mod_cast ε_le },
end

include ist iic

/-- We can approximate `a / b : L` with `q / r`, where `r` has finitely many options for `L`. -/
theorem exists_mem_finset_approx' (h : algebra.is_algebraic R L) (a : S) {b : S} (hb : b ≠ 0) :
  ∃ (q : S) (r ∈ finset_approx bS adm),
  abv (algebra.norm R (r • a - q * b)) < abv (algebra.norm R b) :=
begin
  have inj : function.injective (algebra_map R L),
  { rw is_scalar_tower.algebra_map_eq R S L,
    exact (is_integral_closure.algebra_map_injective S R L).comp bS.algebra_map_injective },
  obtain ⟨a', b', hb', h⟩ := is_integral_closure.exists_smul_eq_mul h inj a hb,
  obtain ⟨q, r, hr, hqr⟩ := exists_mem_finset_approx bS adm a' hb',
  refine ⟨q, r, hr, _⟩,
  refine lt_of_mul_lt_mul_left _
    (show 0 ≤ abv (algebra.norm R (algebra_map R S b')), from abv.nonneg _),
  refine lt_of_le_of_lt (le_of_eq _) (mul_lt_mul hqr (le_refl _)
    (abv.pos ((algebra.norm_ne_zero_iff_of_basis bS).mpr hb)) (abv.nonneg _)),
  rw [← abv.map_mul, ← monoid_hom.map_mul, ← abv.map_mul, ← monoid_hom.map_mul, ← algebra.smul_def,
      smul_sub b', sub_mul, smul_comm, h, mul_comm b a', algebra.smul_mul_assoc r a' b,
      algebra.smul_mul_assoc b' q b]
end

end real

lemma prod_finset_approx_ne_zero : algebra_map R S (∏ m in finset_approx bS adm, m) ≠ 0 :=
begin
  refine mt ((ring_hom.injective_iff _).mp bS.algebra_map_injective _) _,
  simp only [finset.prod_eq_zero_iff, not_exists],
  rintros x hx rfl,
  exact finset_approx.zero_not_mem bS adm hx
end

lemma ne_bot_of_prod_finset_approx_mem
  (J : ideal S) (h : algebra_map _ _ (∏ m in finset_approx bS adm, m) ∈ J) :
  J ≠ ⊥ :=
(submodule.ne_bot_iff _).mpr ⟨_, h, prod_finset_approx_ne_zero _ _⟩

include ist iic

/-- Each class in the class group contains an ideal `J`
such that `M := Π m ∈ finset_approx` is in `J`. -/
theorem exists_mk0_eq_mk0 [is_dedekind_domain S] [is_fraction_ring S L]
  (h : algebra.is_algebraic R L) (I : (ideal S)⁰) :
  ∃ (J : (ideal S)⁰), class_group.mk0 L I = class_group.mk0 L J ∧
    algebra_map _ _ (∏ m in finset_approx bS adm, m) ∈ (J : ideal S) :=
begin
  set M := ∏ m in finset_approx bS adm, m with M_eq,
  have hM : algebra_map R S M ≠ 0 := prod_finset_approx_ne_zero bS adm,
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := exists_min abv I,
  suffices : ideal.span {b} ∣ ideal.span {algebra_map _ _ M} * I.1,
  { obtain ⟨J, hJ⟩ := this,
    refine ⟨⟨J, _⟩, _, _⟩,
    { rw mem_non_zero_divisors_iff_ne_zero,
      rintro rfl,
      rw [ideal.zero_eq_bot, ideal.mul_bot] at hJ,
      exact hM (ideal.span_singleton_eq_bot.mp (I.2 _ hJ)) },
    { rw class_group.mk0_eq_mk0_iff,
      exact ⟨algebra_map _ _ M, b, hM, b_ne_zero, hJ⟩ },
    rw [← set_like.mem_coe, ← set.singleton_subset_iff, ← ideal.span_le, ← ideal.dvd_iff_le],
    refine (mul_dvd_mul_iff_left _).mp _,
    swap, { exact mt ideal.span_singleton_eq_bot.mp b_ne_zero },
    rw [subtype.coe_mk, ideal.dvd_iff_le, ← hJ, mul_comm],
    apply ideal.mul_mono le_rfl,
    rw [ideal.span_le, set.singleton_subset_iff],
    exact b_mem },
  rw [ideal.dvd_iff_le, ideal.mul_le],
  intros r' hr' a ha,
  rw ideal.mem_span_singleton at ⊢ hr',
  obtain ⟨q, r, r_mem, lt⟩ := exists_mem_finset_approx' L bS adm h a b_ne_zero,
  apply @dvd_of_mul_left_dvd _ _ q,
  simp only [algebra.smul_def] at lt,
  rw ← sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left _ ha) (I.1.mul_mem_left _ b_mem)) lt),
  refine mul_dvd_mul_right (dvd_trans (ring_hom.map_dvd _ _) hr') _,
  exact multiset.dvd_prod (multiset.mem_map.mpr ⟨_, r_mem, rfl⟩)
end

omit iic ist

/-- `class_group.mk_M_mem` is a specialization of `class_group.mk0` to (the finite set of)
ideals that contain `M := ∏ m in finset_approx L f abs, m`.
By showing this function is surjective, we prove that the class group is finite. -/
noncomputable def mk_M_mem [is_fraction_ring S L] [is_dedekind_domain S]
  (J : {J : ideal S // algebra_map _ _ (∏ m in finset_approx bS adm, m) ∈ J}) :
  class_group S L :=
class_group.mk0 _ ⟨J.1, mem_non_zero_divisors_iff_ne_zero.mpr
  (ne_bot_of_prod_finset_approx_mem bS adm J.1 J.2)⟩

include iic ist

lemma mk_M_mem_surjective [is_fraction_ring S L] [is_dedekind_domain S]
  (h : algebra.is_algebraic R L) :
  function.surjective (class_group.mk_M_mem L bS adm) :=
begin
  intro I',
  obtain ⟨⟨I, hI⟩, rfl⟩ := class_group.mk0_surjective I',
  obtain ⟨J, mk0_eq_mk0, J_dvd⟩ := exists_mk0_eq_mk0 L bS adm h ⟨I, hI⟩,
  exact ⟨⟨J, J_dvd⟩, mk0_eq_mk0.symm⟩
end

open_locale classical

/-- The main theorem: the class group of an integral closure `S` of `R` in an
algebraic extension `L` is finite if there is an admissible absolute value.

See also `class_group.fintype_of_admissible_of_finite` where `L` is a finite
extension of `K = Frac(R)`, supplying most of the required assumptions automatically.
-/
noncomputable def fintype_of_admissible_of_algebraic [is_fraction_ring S L] [is_dedekind_domain S]
  (h : algebra.is_algebraic R L) : fintype (class_group S L) :=
@fintype.of_surjective _ _ _
  (@fintype.of_equiv _
    {J // J ∣ ideal.span ({algebra_map R S (∏ (m : R) in finset_approx bS adm, m)} : set S)}
    (unique_factorization_monoid.fintype_subtype_dvd _
      (by { rw [ne.def, ideal.zero_eq_bot, ideal.span_singleton_eq_bot],
            exact prod_finset_approx_ne_zero bS adm }))
    ((equiv.refl _).subtype_equiv (λ I, ideal.dvd_iff_le.trans
      (by rw [equiv.refl_apply, ideal.span_le, set.singleton_subset_iff]))))
  (class_group.mk_M_mem L bS adm)
  (class_group.mk_M_mem_surjective L bS adm h)

/-- The main theorem: the class group of an integral closure `S` of `R` in a
finite extension `L` of `K = Frac(R)` is finite if there is an admissible
absolute value.

See also `class_group.fintype_of_admissible_of_algebraic` where `L` is an
algebraic extension of `R`, that includes some extra assumptions.
-/
noncomputable def fintype_of_admissible_of_finite [is_dedekind_domain R] :
  fintype (@class_group S L _ _ _
    (is_integral_closure.is_fraction_ring_of_finite_extension R K L S)) :=
begin
  letI := classical.dec_eq L,
  letI := is_integral_closure.is_fraction_ring_of_finite_extension R K L S,
  letI := is_integral_closure.is_dedekind_domain R K L S,
  choose s b hb_int using finite_dimensional.exists_is_basis_integral R K L,
  obtain ⟨n, b⟩ := submodule.basis_of_pid_of_le_span _
    (is_integral_closure.range_le_span_dual_basis S b hb_int),
  let bS := b.map ((linear_map.quot_ker_equiv_range _).symm ≪≫ₗ _),
  refine fintype_of_admissible_of_algebraic L bS adm
    (λ x, (is_fraction_ring.is_algebraic_iff R K).mpr (algebra.is_algebraic_of_finite x)),
  { rw linear_map.ker_eq_bot.mpr,
    { exact submodule.quot_equiv_of_eq_bot _ rfl },
    { exact is_integral_closure.algebra_map_injective _ R _ } },
  { refine (basis.linear_independent _).restrict_scalars _,
    simp only [algebra.smul_def, mul_one],
    apply is_fraction_ring.injective }
end

end is_admissible

end euclidean_domain

end class_group
