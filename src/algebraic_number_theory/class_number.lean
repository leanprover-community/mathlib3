import algebra.big_operators.finsupp
import algebra.floor
import group_theory.quotient_group
import linear_algebra.determinant
import linear_algebra.free_module
import linear_algebra.matrix
import ring_theory.class_group
import ring_theory.dedekind_domain
import ring_theory.fractional_ideal

-- These results are in separate files for faster re-compiling.
-- They should be merged with the appropriate lower-level file when development is finished.
import algebraic_number_theory.class_number.det
import algebraic_number_theory.class_number.euclidean_absolute_value
import algebraic_number_theory.class_number.ideal
import algebraic_number_theory.class_number.integral_closure
import algebraic_number_theory.class_number.subalgebra

open ring

open_locale big_operators

section euclidean_domain

variables {R K L : Type*} [euclidean_domain R] [field K] [field L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L] [is_separable f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]
variables (abs : euclidean_absolute_value R ℤ)
variables [decidable_eq L]

section

variables (L)

include L f abs

def finset_approx : finset R := sorry

end

-- Theorem 4.1
lemma finset_approx.zero_not_mem : (0 : R) ∉ finset_approx L f abs := sorry

theorem exists_mem_finset_approx (g : L) :
  ∃ (q : integral_closure R L) (r ∈ finset_approx L f abs),
    abs_frac_norm f abs (r • g - q) < 1 :=
sorry

-- Corollary 4.2
theorem exists_mem_finset_approx' (a : integral_closure R L) {b}
  (hb : b ≠ (0 : integral_closure R L)) :
  ∃ (q : integral_closure R L) (r ∈ finset_approx L f abs),
    abs_norm f abs (r • a - q * b) < abs_norm f abs b :=
begin
  obtain ⟨q, r, hr, hrgq⟩ := exists_mem_finset_approx f abs (a / b : L),
  use [q, r, hr],
  unfold abs_frac_norm abs_norm at hrgq,
  have h_coe_b : (b : L) ≠ 0,
  { rwa [ne.def, submodule.coe_eq_zero] },
  have hb' : 0 < abs_frac_norm f abs (b : L),
  { exact (abs.to_frac f).pos ((algebra.norm_ne_zero _).mpr h_coe_b) },
  rw [← mul_lt_mul_right hb', one_mul] at hrgq,
  unfold abs_frac_norm at hrgq,
  rw [← absolute_value.map_mul, ← (algebra.norm _).map_mul, sub_mul, mul_comm, ← smul_eq_mul,
      smul_comm, smul_eq_mul, ← mul_div_assoc, mul_div_cancel_left _ h_coe_b] at hrgq,
  rw [← @int.cast_lt ℚ, ← abs_frac_norm_coe, ← abs_frac_norm_coe],
  unfold abs_frac_norm,
  exact_mod_cast hrgq
end

end euclidean_domain

lemma monoid_hom.range_eq_top {G H : Type*} [group G] [group H] (f : G →* H) :
  f.range = ⊤ ↔ function.surjective f :=
⟨ λ h y, show y ∈ f.range, from h.symm ▸ subgroup.mem_top y,
  λ h, subgroup.ext (λ x, by simp [h x]) ⟩

section euclidean_domain

variables {R K L : Type*} [euclidean_domain R] [is_dedekind_domain R]
variables [field K] [field L] [decidable_eq L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L] [is_separable f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]
variables (abs : euclidean_absolute_value R ℤ)

-- Lemma 5.1
lemma exists_min (I : nonzero_ideal (integral_closure R L)) :
  ∃ b ∈ I.1, b ≠ 0 ∧ ∀ c ∈ I.1, abs_norm f abs c < abs_norm f abs b → c = 0 :=
begin
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

-- TODO: how should we make this instance? It depends on `f.codomain`.
instance : is_dedekind_domain (integral_closure R L) := sorry

-- Theorem 5.2
theorem exists_mul_eq_mul (I : nonzero_ideal (integral_closure R L)) :
  ∃ (J : nonzero_ideal (integral_closure R L)),
  class_group.mk0 (integral_closure.fraction_map_of_finite_extension L f) I =
  class_group.mk0 (integral_closure.fraction_map_of_finite_extension L f) J ∧
    J.1 ∣ ideal.span {algebra_map _ _ (∏ m in finset_approx L f abs, m)} :=
begin
  set m := ∏ m in finset_approx L f abs, m with m_eq,
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := exists_min f abs I,
  suffices : ideal.span {b} ∣ ideal.span {algebra_map _ _ m} * I.1,
  { obtain ⟨J, hJ⟩ := this,
    refine ⟨⟨J, _⟩, _, _⟩,
    { sorry },
    { rw class_group.mk0_eq_mk0_iff,
      refine ⟨algebra_map _ _ m, b, _, b_ne_zero, hJ⟩,
      refine mt ((algebra_map R _).injective_iff.mp (integral_closure.algebra_map_injective f) _) _,
      rw finset.prod_eq_zero_iff,
      push_neg,
      intros a ha a_eq,
      rw a_eq at ha,
      exact finset_approx.zero_not_mem f abs ha },
    apply ideal.dvd_of_mul_dvd_mul_left (ideal.span_singleton_ne_bot b_ne_zero),
    rw [ideal.dvd_iff_le, ← hJ, mul_comm, m_eq],
    apply ideal.mul_mono le_rfl,
    rw [ideal.span_le, set.singleton_subset_iff],
    exact b_mem },
  rw [ideal.dvd_iff_le, ideal.mul_le],
  intros r' hr' a ha,
  rw ideal.mem_span_singleton at ⊢ hr',
  obtain ⟨q, r, r_mem, lt⟩ := exists_mem_finset_approx' f abs a b_ne_zero,
  apply @dvd_of_mul_left_dvd _ _ q,
  rw algebra.smul_def at lt,
  rw ← sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left ha) (I.1.mul_mem_left b_mem)) lt),
  refine mul_dvd_mul_right (dvd_trans (ring_hom.map_dvd _ _) hr') _,
  exact finset.dvd_prod r_mem (λ x, x)
end
.

-- Theorem 5.3
instance : fintype (class_group f) :=
_

end euclidean_domain
