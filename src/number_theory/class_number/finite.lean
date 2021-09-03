/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import linear_algebra.free_module_pid
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
 - `number_field.class_number`: the class number of a number field is the (finite)
   cardinality of the class group of its ring of integers
 - `function_field.class_number`: the class number of a number field is the (finite)
   cardinality of the class group of its ring of integers
-/

open_locale big_operators
open_locale non_zero_divisors

section move_me

namespace unique_factorization_monoid

/-- If `y` is a nonzero element of a unique factorization monoid with finitely
many units (e.g. `ℤ`, `ideal R`), it has finitely many divisors. -/
noncomputable def fintype_subtype_dvd {M : Type*} [comm_cancel_monoid_with_zero M]
  [unique_factorization_monoid M] [fintype (units M)]
  (y : M) (hy : y ≠ 0) :
  fintype {x // x ∣ y} :=
begin
  haveI : nontrivial M := ⟨⟨y, 0, hy⟩⟩,
  haveI : normalization_monoid M := unique_factorization_monoid.normalization_monoid,
  haveI := classical.dec_eq M,
  haveI := classical.dec_eq (associates M),
  refine fintype.of_finset
    (((factors y).powerset.to_finset.product (finset.univ : finset (units M))).image
      (λ uf, (uf.2 : M) * uf.1.prod))
    (λ x, _),
  simp only [exists_prop, finset.mem_image, finset.mem_product, finset.mem_univ, and_true,
    multiset.mem_to_finset, multiset.mem_powerset, exists_eq_right, multiset.mem_map],
  split,
  { rintros ⟨s, hs, rfl⟩,
    have prod_s_ne : s.fst.prod ≠ 0,
    { intro hz,
      apply hy (eq_zero_of_zero_dvd _),
      have hz := (@multiset.prod_eq_zero_iff M _ _ _ s.fst).mp hz,
      rw ← (factors_prod hy).dvd_iff_dvd_right,
      exact multiset.dvd_prod (multiset.mem_of_le hs hz) },
    show (s.snd : M) * s.fst.prod ∣ y,
    rw [(unit_associated_one.mul_right s.fst.prod).dvd_iff_dvd_left, one_mul,
        ← (factors_prod hy).dvd_iff_dvd_right],
    exact multiset.prod_dvd_prod hs },
  { rintro (h : x ∣ y),
    have hx : x ≠ 0, { refine mt (λ hx, _) hy, rwa [hx, zero_dvd_iff] at h },
    obtain ⟨u, hu⟩ := factors_prod hx,
    refine ⟨⟨factors x, u⟩, _, (mul_comm _ _).trans hu⟩,
    exact (dvd_iff_factors_le_factors hx hy).mp h }
end

end unique_factorization_monoid

lemma monoid_hom.range_eq_top {G H : Type*} [group G] [group H] (f : G →* H) :
  f.range = ⊤ ↔ function.surjective f :=
⟨λ h y, show y ∈ f.range, from h.symm ▸ subgroup.mem_top y,
 λ h, subgroup.ext (λ x, by simp [h x])⟩

namespace finset

lemma map_max' {α β : Type*} [linear_order α] [linear_order β]
  {f : α → β} (hf : monotone f) (s : finset α) (h : s.nonempty) :
  f (s.max' h) = (s.image f).max' (h.image f) :=
begin
  obtain mem := finset.max'_mem s h,
  refine le_antisymm
    (finset.le_max' _ _ (finset.mem_image.mpr ⟨_, mem, rfl⟩))
    (finset.max'_le _ _ _ (λ y hy, _)),
  obtain ⟨x, hx, rfl⟩ := finset.mem_image.mp hy,
  exact hf (finset.le_max' _ _ hx)
end

lemma max'_lt {α : Type*} [linear_order α] (s : finset α) (h : s.nonempty)
  {x : α} (hx : ∀ y ∈ s, y < x) :
  s.max' h < x :=
lt_of_le_of_ne
  (finset.max'_le _ h _ (λ y hy, le_of_lt (hx y hy)))
  (ne_of_lt (hx _ (s.max'_mem h)))

end finset

lemma finset.dvd_prod {ι M : Type*} [comm_monoid M] {x : ι} {s : finset ι}
  (hx : x ∈ s) (f : ι → M) :
  f x ∣ ∏ i in s, f i :=
multiset.dvd_prod (multiset.mem_map.mpr ⟨x, hx, rfl⟩)

@[simp]
lemma absolute_value.map_pow' {R S : Type*} [comm_semiring R] [nontrivial R] [linear_ordered_comm_ring S]
  (abv : absolute_value R S) (x : R) (n : ℕ) : abv (x ^ n) = abv x ^ n :=
by { induction n; simp [pow_succ, *] }

lemma no_zero_smul_divisors.algebra_map_injective (R S : Type*) [comm_ring R] [ring S] [nontrivial S]
  [algebra R S] [no_zero_smul_divisors R S] :
  function.injective (algebra_map R S) :=
suffices function.injective (λ (c : R), c • (1 : S)),
by { convert this, ext, rw [algebra.smul_def, mul_one] },
smul_left_injective R one_ne_zero

lemma basis.algebra_map_injective {ι R S : Type*} [comm_ring R] [no_zero_divisors R]
  [ring S] [nontrivial S] [algebra R S] (b : basis ι R S) :
  function.injective (algebra_map R S) :=
have no_zero_smul_divisors R S := b.no_zero_smul_divisors,
by exactI no_zero_smul_divisors.algebra_map_injective R S

namespace is_integral_closure

/-- A fraction `a / b : L = Frac(S)` can be given as `c : S` divided by `d : R`,
if `S` is the integral closure of `R` in an algebraic extension `L` of `R`. -/
lemma exists_eq_mul {R S L : Type*} [integral_domain R] [integral_domain S] [field L]
  [algebra R S] [algebra S L] [algebra R L] [is_scalar_tower R S L] [is_integral_closure S R L]
  (h : algebra.is_algebraic R L) (inj : function.injective (algebra_map R L))
  (a : S) {b : S} (hb : b ≠ 0) : ∃ (c : S) (d ≠ (0 : R)), d • a = b * c :=
begin
  obtain ⟨c, d, d_ne, hx⟩ := exists_integral_multiple
    (h (algebra_map _ L a / algebra_map _ L b))
    ((ring_hom.injective_iff _).mp inj),
  refine ⟨mk' S (c : L) c.2, d, d_ne, is_integral_closure.algebra_map_injective S R L _⟩,
  simp only [algebra.smul_def, ring_hom.map_mul, algebra_map_mk', ← hx,
       ← is_scalar_tower.algebra_map_apply],
  rw [← mul_assoc _ (_ / _), mul_div_cancel' (algebra_map S L a), mul_comm],
  exact mt ((ring_hom.injective_iff _).mp (algebra_map_injective S R L) _) hb,
end

end is_integral_closure

lemma _root_.basis.index_nonempty {ι R M : Type*} [semiring R] [add_comm_group M] [module R M]
  (b : basis ι R M) [nontrivial M] : nonempty ι :=
begin
  obtain ⟨x, y, ne⟩ : ∃ (x y : M), x ≠ y := nontrivial.exists_pair_ne,
  obtain ⟨i, _⟩ := not_forall.mp (mt b.ext_elem ne),
  exact ⟨i⟩
end

namespace matrix

open_locale matrix

lemma dot_product_vec_mul {m n R : Type*} [fintype n] [fintype m] [non_unital_semiring R]
  (v : m → R) (A : matrix m n R) (w : n → R) :
  dot_product (vec_mul v A) w = dot_product v (mul_vec A w) :=
by simp only [dot_product, vec_mul, mul_vec, finset.mul_sum, finset.sum_mul, mul_assoc];
   exact finset.sum_comm

theorem eq_zero_of_vec_mul_eq_zero {n A : Type*} [fintype n] [decidable_eq n] [integral_domain A]
  {M : matrix n n A} (hM : M.det ≠ 0) {v : n → A} (hv : M.vec_mul v = 0) :
  v = 0 :=
nondegenerate_of_det_ne_zero hM v (λ w, by rw [← dot_product_vec_mul, hv, zero_dot_product])

theorem eq_zero_of_mul_vec_eq_zero {n A : Type*} [fintype n] [decidable_eq n] [integral_domain A]
  {M : matrix n n A} (hM : M.det ≠ 0) {v : n → A} (hv : M.mul_vec v = 0) :
  v = 0 :=
eq_zero_of_vec_mul_eq_zero (by rwa det_transpose) ((vec_mul_transpose M v).trans hv)

lemma det_ne_zero_of_left_inverse {n R : Type*} [fintype n] [decidable_eq n] [comm_ring R] [nontrivial R]
  {M N : matrix n n R} (h : N ⬝ M = 1) :
  M.det ≠ 0 :=
is_unit.ne_zero (matrix.is_unit_det_of_left_inverse h)

lemma det_ne_zero_of_right_inverse {n R : Type*} [fintype n] [decidable_eq n] [comm_ring R] [nontrivial R]
  {M N : matrix n n R} (h : M ⬝ N = 1) :
  M.det ≠ 0 :=
is_unit.ne_zero (matrix.is_unit_det_of_right_inverse h)

lemma ker_to_lin_eq_bot_iff {n R : Type*} [fintype n] [decidable_eq n] [comm_ring R]
  {M : matrix n n R} : M.to_lin'.ker = ⊥ ↔ ∀ v, M.mul_vec v = 0 → v = 0 :=
by simp only [submodule.eq_bot_iff, linear_map.mem_ker, matrix.to_lin'_apply]

lemma ring_hom.map_dot_product {n R S : Type*} [fintype n] [semiring R] [semiring S]
  (f : R →+* S) (v w : n → R) :
  f (matrix.dot_product v w) = matrix.dot_product (f ∘ v) (f ∘ w) :=
by simp only [matrix.dot_product, f.map_sum, f.map_mul]

lemma ring_hom.map_mul_vec {n R S : Type*} [fintype n] [semiring R] [semiring S]
  (f : R →+* S) (M : matrix n n R) (v : n → R) (i : n) :
  f (M.mul_vec v i) = ((M.map f).mul_vec (f ∘ v) i) :=
by simp only [mul_vec, map_apply, ring_hom.map_dot_product]

lemma mul_vec_smul {n R S : Type*} [fintype n] [comm_semiring R] [semiring S] [algebra R S]
  (M : matrix n n S) (b : R) (v : n → S)  :
  M.mul_vec (b • v) = b • M.mul_vec v :=
by { ext i, simp only [matrix.mul_vec, matrix.dot_product, finset.smul_sum, pi.smul_apply,
                       algebra.mul_smul_comm] }

/-- This holds for all integral domains (see `matrix.exists_mul_vec_eq_zero_iff`),
not just fields, but it's easier to prove it for the field of fractions first. -/
lemma exists_mul_vec_eq_zero_iff_aux {n K : Type*} [fintype n] [decidable_eq n]
  [field K] {M : matrix n n K} :
  (∃ (v ≠ 0), M.mul_vec v = 0) ↔ M.det = 0 :=
begin
  split,
  { rintros ⟨v, hv, mul_eq⟩,
    contrapose! hv,
    exact eq_zero_of_mul_vec_eq_zero hv mul_eq },
  { contrapose!,
    intros h,
    have : M.to_lin'.ker = ⊥,
    { simpa only [matrix.ker_to_lin_eq_bot_iff, not_imp_not] using h },
    have : M ⬝ linear_map.to_matrix'
      ((linear_equiv.of_injective_endo M.to_lin' this).symm : (n → K) →ₗ[K] (n → K)) = 1,
    { refine matrix.to_lin'.injective (linear_map.ext $ λ v, _),
      rw [matrix.to_lin'_mul, matrix.to_lin'_one, matrix.to_lin'_to_matrix', linear_map.comp_apply],
      exact (linear_equiv.of_injective_endo M.to_lin' this).apply_symm_apply v },
    exact matrix.det_ne_zero_of_right_inverse this }
end

lemma exists_mul_vec_eq_zero_iff {n A : Type*} [fintype n] [decidable_eq n]
  [integral_domain A] {M : matrix n n A} :
  (∃ (v ≠ 0), M.mul_vec v = 0) ↔ M.det = 0 :=
begin
  have : (∃ (v ≠ 0), mul_vec ((algebra_map A (fraction_ring A)).map_matrix M) v = 0) ↔ _ :=
    exists_mul_vec_eq_zero_iff_aux,
  rw [← ring_hom.map_det, is_fraction_ring.to_map_eq_zero_iff] at this,
  refine iff.trans _ this, split; rintro ⟨v, hv, mul_eq⟩,
  { refine ⟨λ i, algebra_map _ _ (v i), mt (λ h, funext $ λ i, _) hv, _⟩,
    { exact is_fraction_ring.injective A (fraction_ring A) (congr_fun h i) },
    { ext i,
      refine (ring_hom.map_mul_vec _ _ _ i).symm.trans _,
      rw [mul_eq, pi.zero_apply, ring_hom.map_zero, pi.zero_apply] } },
  { letI := classical.dec_eq (fraction_ring A),
    obtain ⟨⟨b, hb⟩, ba_eq⟩ := is_localization.exist_integer_multiples_of_finset
      (non_zero_divisors A) (finset.univ.image v),
    choose f hf using ba_eq,
    refine ⟨λ i, f _ (finset.mem_image.mpr ⟨i, finset.mem_univ i, rfl⟩),
            mt (λ h, funext $ λ i, _) hv, _⟩,
    { have := congr_arg (algebra_map A (fraction_ring A)) (congr_fun h i),
      rw [hf, subtype.coe_mk, pi.zero_apply, ring_hom.map_zero, algebra.smul_def,
          mul_eq_zero, is_fraction_ring.to_map_eq_zero_iff] at this,
      exact this.resolve_left (mem_non_zero_divisors_iff_ne_zero.mp hb), },
    { ext i,
      refine is_fraction_ring.injective A (fraction_ring A) _,
      calc algebra_map A (fraction_ring A) (M.mul_vec (λ (i : n), f (v i) _) i)
          = ((algebra_map A (fraction_ring A)).map_matrix M).mul_vec
              (algebra_map _ (fraction_ring A) b • v) i : _
      ... = 0 : _,
      { simp_rw [ring_hom.map_mul_vec, mul_vec, dot_product, function.comp_app, hf,
          subtype.coe_mk, ring_hom.map_matrix_apply, pi.smul_apply, smul_eq_mul,
          algebra.smul_def] },
      { rw [mul_vec_smul, mul_eq, pi.smul_apply, pi.zero_apply, smul_zero] } } },
end

end matrix

lemma algebra.norm_eq_zero_iff_of_basis {ι R S : Type*} [fintype ι]
  [integral_domain R] [integral_domain S] [algebra R S]
  (b : basis ι R S) {x : S} :
  algebra.norm R x = 0 ↔ x = 0 :=
begin
  have hι := b.index_nonempty,
  letI := classical.dec_eq ι,
  rw algebra.norm_eq_matrix_det b,
  split,
  { rw ← matrix.exists_mul_vec_eq_zero_iff,
    rintros ⟨v, v_ne, hv⟩,
    rw [← b.equiv_fun.apply_symm_apply v, b.equiv_fun_symm_apply, b.equiv_fun_apply,
        algebra.left_mul_matrix_mul_vec_repr] at hv,
    refine (mul_eq_zero.mp (b.ext_elem $ λ i, _)).resolve_right (show ∑ i, v i • b i ≠ 0, from _),
    { simpa only [linear_equiv.map_zero, pi.zero_apply] using congr_fun hv i },
    { contrapose! v_ne with sum_eq,
      apply b.equiv_fun.symm.injective,
      rw [b.equiv_fun_symm_apply, sum_eq, linear_equiv.map_zero] } },
  { rintro rfl,
    rw [alg_hom.map_zero, matrix.det_zero hι] },
end

lemma algebra.norm_ne_zero_iff_of_basis {ι R S : Type*} [fintype ι]
  [integral_domain R] [integral_domain S] [algebra R S]
  (b : basis ι R S) {x : S} :
  algebra.norm R x ≠ 0 ↔ x ≠ 0 :=
not_iff_not.mpr (algebra.norm_eq_zero_iff_of_basis b)

lemma algebra.norm_eq_zero_iff {K L : Type*} [field K] [field L] [algebra K L]
  [finite_dimensional K L] {x : L} :
  algebra.norm K x = 0 ↔ x = 0 :=
algebra.norm_eq_zero_iff_of_basis (basis.of_vector_space K L)

@[simp]
lemma algebra.norm_eq_zero_iff' {K L : Type*} [field K] [field L] [algebra K L]
  [finite_dimensional K L] {x : L} :
  linear_map.det (algebra.lmul K L x) = 0 ↔ x = 0 :=
algebra.norm_eq_zero_iff_of_basis (basis.of_vector_space K L)

lemma non_zero_divisors.ne_zero {M : Type*} [monoid_with_zero M] [nontrivial M]
  {x} (hx : x ∈ M⁰) : x ≠ 0 :=
λ h, one_ne_zero (hx _ $ (one_mul _).trans h)

lemma non_zero_divisors.coe_ne_zero {M : Type*} [monoid_with_zero M] [nontrivial M]
  (x : M⁰) : (x : M) ≠ 0 :=
non_zero_divisors.ne_zero x.2

end move_me

namespace class_group

open ring

open_locale big_operators

section euclidean_domain

variables (R S K L : Type*) [euclidean_domain R] [integral_domain S] [field K] [field L]
variables [algebra R K] [is_fraction_ring R K]
variables [algebra K L] [finite_dimensional K L] [is_separable K L]
variables [algRL : algebra R L] [is_scalar_tower R K L]
variables [algebra R S] [algebra S L]
variables [ist : is_scalar_tower R S L] [iic : is_integral_closure S R L]

variables {R S} (abv : absolute_value R ℤ)
variables {ι : Type*} [decidable_eq ι] [fintype ι] (bS : basis ι R S)

/-- If the `R`-integral element `a : S` has coordinates `≤ y`, then
`algebra.norm a ≤ norm_bound abv b * y ^ n`. (See also `norm_le` and `norm_lt`). -/
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

/-- If the `R`-integral element `a : S` has coordinates `≤ y`, its norm is less
than `norm_bound * y ^ dim S`. -/
lemma norm_le (a : S) {y : ℤ} (hy : ∀ k, abv (bS.repr a k) ≤ y) :
  abv (algebra.norm R a) ≤ norm_bound abv bS * y ^ fintype.card ι :=
begin
  conv_lhs { rw ← bS.sum_repr a },
  rw [algebra.norm_apply, ← linear_map.det_to_matrix bS],
  simp only [algebra.norm_apply, alg_hom.map_sum, alg_hom.map_smul, linear_equiv.map_sum,
      linear_equiv.map_smul, algebra.to_matrix_lmul_eq, norm_bound],
  convert matrix.det_sum_le finset.univ _ hy;
    try { simp only [finset.card_univ] },
  { rw [algebra.smul_mul_assoc, ← mul_pow _ _ (fintype.card ι)],
    conv_lhs { rw algebra.smul_mul_assoc } },
  { intros i j k,
    apply finset.le_max',
    exact finset.mem_image.mpr ⟨⟨i, j, k⟩, finset.mem_univ _, rfl⟩ },
end

/-- If the `R`-integral element `a : S` has coordinates `< y`, its norm is strictly less
than `norm_bound * y ^ dim S`. -/
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
  { rw [y'_def, finset.map_max' (show monotone (coe : ℤ → T), from λ x y h, int.cast_le.mpr h)],
    apply finset.max'_lt _ (him.image _),
    simp only [finset.mem_image, exists_prop],
    rintros _ ⟨x, ⟨k, -, rfl⟩, rfl⟩,
    exact hy k },
  have y'_nonneg : 0 ≤ y' := le_trans (abv.nonneg _) (hy' i),
  apply (int.cast_le.mpr (norm_le abv bS a hy')).trans_lt,
  simp only [int.cast_mul, int.cast_pow],
  apply mul_lt_mul' (le_refl _),
  { exact pow_lt_pow_of_lt_left this (int.cast_nonneg.mpr y'_nonneg) (fintype.card_pos_iff.mpr ⟨i⟩) },
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
whose remainders are close together. An upper bound for the number of elements
is `cardM bS adm`. -/
noncomputable def cardM : ℕ :=
adm.card (norm_bound abv bS ^ (-1 / (fintype.card ι) : ℝ)) ^ fintype.card ι

-- adm.card (nat_ceil (norm_bound abv b ^ (-1 / (fintype.card ι) : ℝ) : ℝ))

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
  rw [this, algebra.norm_algebra_map_of_basis bS, abv.map_pow'],

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
  obtain ⟨a', b', hb', h⟩ := is_integral_closure.exists_eq_mul h inj a hb,
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
  exact finset.dvd_prod r_mem (λ x, x)
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
  let bS := b.map ((linear_map.quot_ker_equiv_range _).symm.trans _),
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
