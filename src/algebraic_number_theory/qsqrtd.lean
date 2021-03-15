import algebraic_number_theory.class_number
import ring_theory.eisenstein_criterion
import ring_theory.polynomial.gauss_lemma

/-! In this file, we'll show that ℚ(√(-5)) has ring of integers ℤ[√(-5)] and
the class number is equal to 2 -/

open polynomial

def qsqrtd (d : ℤ) := adjoin_root (X^2 - C (d : ℚ))

notation `ℚ√` := qsqrtd

namespace polynomial

variables {R : Type*} [semiring R] (f : polynomial R)

instance [char_zero R] : char_zero (polynomial R) :=
{ cast_injective := λ a b h, char_zero.cast_injective $ show (a : R) = (b : R), from C_inj.mp $
  calc C (a : R) = a : C.map_nat_cast a
             ... = b : h
             ... = C (b : R) : (C.map_nat_cast b).symm }

end polynomial

namespace adjoin_root

variables {R : Type*} [integral_domain R] (f : polynomial R)

lemma char_zero [char_zero R] (hf : 0 < f.degree) :
  char_zero (adjoin_root f) :=
begin
  refine char_zero_of_inj_zero (λ n hn, _),
  contrapose hn,
  rw [← (ideal.quotient.mk _).map_nat_cast, ideal.quotient.eq_zero_iff_mem,
      ideal.mem_span_singleton],
  intro hdvd,
  apply (nat_degree_pos_iff_degree_pos.mpr hf).not_le,
  simpa using polynomial.nat_degree_le_of_dvd hdvd (char_zero.cast_injective.ne hn)
end

end adjoin_root

lemma x_sq_sub_ne_zero (d : ℤ) : X^2 - C (d : ℚ) ≠ 0 :=
begin
  intro h,
  apply @one_ne_zero ℚ,
  have : coeff (X^2 - C (d : ℚ)) = coeff 0 := congr_arg coeff h,
  simpa only [coeff_sub, coeff_X_pow, coeff_C] using congr_fun this 2
end

lemma degree_x_sq_sub_d_eq (d : ℤ) : (X^2 - C (d : ℚ)).degree = 2 :=
degree_X_pow_sub_C (by norm_num) _

lemma nat_degree_x_sq_sub_d_eq (d : ℤ) : (X^2 - C (d : ℚ)).nat_degree = 2 :=
by { rw [nat_degree, degree_x_sq_sub_d_eq], refl }

lemma degree_x_sq_sub_d_pos (d : ℤ) : 0 < (X^2 - C (d : ℚ)).degree :=
calc (0 : with_bot ℕ) < 2 : with_bot.coe_lt_coe.mpr (by norm_num)
                  ... = _ : (degree_x_sq_sub_d_eq d).symm

-- In principle we could replace `(x ≠ 0)` with `[nontrivial R] (¬ is_field R)`.
lemma exists_prime_dvd_of_not_is_unit {R : Type*} [comm_cancel_monoid_with_zero R]
  [unique_factorization_monoid R]
  {x : R} : x ≠ 0 → ¬ is_unit x → ∃ p, prime p ∧ p ∣ x :=
unique_factorization_monoid.induction_on_prime x
  (λ hnz _, false.elim (hnz rfl))
  (λ _ hu _ hnu, (false.elim (hnu hu)))
  (λ a p ha hp _ _ _, ⟨p, hp, ⟨a, rfl⟩⟩)

lemma exists_prime_dvd_sq_not_dvd_of_squarefree {R : Type*} [comm_cancel_monoid_with_zero R]
  [nontrivial R] [unique_factorization_monoid R]
  {x : R} (hsq : squarefree x) (hu : ¬ is_unit x) :
  ∃ p, prime p ∧ p ∣ x ∧ ¬ (p^2 ∣ x) :=
begin
  obtain ⟨p, hp, hpd⟩ := exists_prime_dvd_of_not_is_unit
    (λ h, not_squarefree_zero (show squarefree (0 : R), from h ▸ hsq))
    hu,
  refine ⟨p, hp, hpd, (λ hpsq, _)⟩,
  rw pow_two at hpsq,
  have := hsq p hpsq,
  have := hp.not_unit,
  contradiction
end

/-- If `d : ℤ` is squarefree, `X^2 - d` is an irreducible polynomial. -/
instance x_sq_sub_d_irreducible (d : ℤ) [hdsq : fact (squarefree d)] [hdu : fact (¬ is_unit d)] :
  irreducible (X^2 - C (d : ℚ)) :=
begin
  have p_monic : monic (X^2 - C d) := monic_X_pow_sub_C d (by linarith),
  have p_primitive : is_primitive (X^2 - C d) := p_monic.is_primitive,
  convert (polynomial.is_primitive.int.irreducible_iff_irreducible_map_cast p_primitive).mp _,
  { ext, simp only [map_pow, ring_hom.eq_int_cast, ring_hom.map_int_cast, map_int_cast, map_X, map_sub] },
  obtain ⟨p, hp, hpd, hpsq⟩ : ∃ p, prime p ∧ p ∣ d ∧ ¬ (p^2 ∣ d) :=
    exists_prime_dvd_sq_not_dvd_of_squarefree hdsq hdu,
  refine irreducible_of_eisenstein_criterion ((ideal.span_singleton_prime _).mpr hp) _ _ _ _ _,
  { exact hp.ne_zero },
  { rw [ideal.mem_span_singleton, p_monic.leading_coeff, ← is_unit_iff_dvd_one],
    exact hp.not_unit },
  { intros i hi,
    rw [degree_X_pow_sub_C, with_bot.coe_lt_coe] at hi,
    { rw ideal.mem_span_singleton,
      show p ∣ (X^2 - C d).coeff (⟨i, hi⟩ : fin 2),
      set i' : fin 2 := ⟨i, hi⟩,
      fin_cases i';
        simp only [h, fin.coe_zero, fin.coe_one, coeff_sub, coeff_X_pow, coeff_C];
        norm_num;
        assumption },
    { linarith } },
  { rw degree_X_pow_sub_C; try { apply with_bot.coe_lt_coe.mpr }; norm_num },
  { rw [pow_two (ideal.span _), ideal.span_singleton_mul_span_singleton,
        ideal.mem_span_singleton, ← pow_two],
    simp only [coeff_sub, coeff_X_pow, coeff_C],
    norm_num,
    assumption },
  { intros a ha,
    have ha := (C_dvd_iff_dvd_coeff _ _).mp ha 2,
    simp only [coeff_sub, coeff_X_pow_self, coeff_C, two_ne_zero, if_false, sub_zero] at ha,
    exact is_unit_iff_dvd_one.mpr ha },
end

namespace qsqrtd

variables (d : ℤ) [fact (squarefree d)] [fact (¬ is_unit d)]

noncomputable instance : field (ℚ√ d) :=
adjoin_root.field

instance : char_zero (ℚ√ d) :=
adjoin_root.char_zero _ (degree_pos_of_irreducible (x_sq_sub_d_irreducible d))

instance : is_number_field (ℚ√ d) :=
{ cz := qsqrtd.char_zero d,
  fd := power_basis.finite_dimensional
    (by { convert adjoin_root.power_basis (x_sq_sub_ne_zero d),
          exact @subsingleton.elim _ rat.algebra_rat_subsingleton _ _ }) }

section ring_of_integers

/-- `a + b √ d` is in the ring of integers of `ℚ(√ d)` for `a b : ℤ` -/
lemma int_add_root_mem_ring_of_integers (a b : ℤ) :
  (a + b • adjoin_root.root _ : ℚ√ d) ∈ number_field.ring_of_integers (ℚ√ d) :=
begin
  refine subalgebra.add_mem _ (subalgebra.coe_int_mem _ a) (subalgebra.gsmul_mem _ _ b),
  use [X^2 - C d, monic_X_pow_sub_C d (by linarith)],
  rw [is_scalar_tower.algebra_map_eq ℤ ℚ, ← eval₂_map],
  convert adjoin_root.eval₂_root _,
  simp only [map_pow, ring_hom.eq_int_cast, ring_hom.map_int_cast, map_int_cast, map_X, map_sub]
end

variables {d}

/-- `coeff x` is a vector of rational numbers such that `x = coeff x 0 + coeff x 1 • √ d` -/
noncomputable def coeff (x : ℚ√ d) : fin 2 → ℚ :=
λ i, (adjoin_root.power_basis (x_sq_sub_ne_zero _)).is_basis.repr x
  ⟨i, calc (i : ℕ) < 2 : i.2 ... = _ : (nat_degree_x_sq_sub_d_eq _).symm⟩

lemma eq_coeff_add_coeff_sqrt (x : ℚ√ d) :
  x = coeff x 0 + coeff x 1 • adjoin_root.root _ :=
begin
  rw ((adjoin_root.power_basis (x_sq_sub_ne_zero _)).is_basis.total_repr x).symm,
  sorry, -- TODO: this is "obviously" the same thing
end

@[simp] lemma trace_eq (x : ℚ√ d) : algebra.trace ℚ _ x = 2 * coeff x 0 :=
sorry

@[simp] lemma norm_eq (x : ℚ√ d) :
  algebra.norm (adjoin_root.power_basis (x_sq_sub_ne_zero _)).is_basis x =
    coeff x 0 ^ 2 - coeff x 1 ^ 2 * d :=
sorry

/-- The ring of integers of `ℚ√ d` consists of elements of the form `a + b √ d` -/
theorem mem_ring_of_integers (h : d % 4 ≠ 1) {x : ℚ√ d} :
  (x ∈ number_field.ring_of_integers (ℚ√ d)) ↔ ∃ (a b : ℤ), x = a + b • adjoin_root.root _ :=
begin
  split,
  { intro hx,
    obtain ⟨p, p_monic, eval_p⟩ := hx,
    rw eq_coeff_add_coeff_sqrt x,
    sorry },
  { rintros ⟨a, b, rfl⟩,
    apply int_add_root_mem_ring_of_integers }
end

end ring_of_integers

section class_number

@[simp]
lemma prime_neg {R : Type*} [comm_ring R] {p : R} : prime (-p) ↔ prime p :=
prime_iff_of_associated ⟨-1, by simp⟩

private lemma neg_five_prime : (prime (-5 : ℤ)) :=
prime_neg.mpr $ nat.prime_iff_prime_int.mp (show nat.prime 5, by norm_num)
instance : fact (squarefree (-5 : ℤ)) := neg_five_prime.squarefree
instance : fact (¬ is_unit (-5 : ℤ)) := neg_five_prime.not_unit

theorem class_number_eq : number_field.class_number (ℚ√ (-5)) = 2 :=
by dec_trivial

end class_number

end qsqrtd
