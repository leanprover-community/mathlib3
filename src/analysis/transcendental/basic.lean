import ring_theory.algebraic
import analysis.transcendental.small_lemmas

noncomputable theory

open small_lemmas
open_locale classical
open_locale big_operators

notation `transcendental` x := ¬(is_algebraic ℤ x)
notation `transcendental_over_ℚ` x := ¬(is_algebraic ℚ x)
notation α`[X]` := polynomial α

theorem algebraic_over_Z_then_algebraic_over_Q (x : ℝ) : is_algebraic ℤ x -> is_algebraic ℚ x :=
begin
  rintro ⟨p, p_nonzero, root⟩,
  use (p.map (algebra_map ℤ ℚ)),
  split,
  intro rid,
  apply p_nonzero,
  apply polynomial.map_injective (algebra_map ℤ ℚ) _,
  simp only [polynomial.map_zero], exact rid,

  intros x y h, simp only [ring_hom.eq_int_cast, int.cast_inj] at h ⊢, exact h,

  rw polynomial.aeval_def,
  rw polynomial.eval₂_map,
  rw polynomial.as_sum p at root ⊢,
  rw aeval_sum' at root,
  rw eval₂_sum',
  rw <-root,
  apply finset.sum_congr, refl, intros m h,
  simp only [polynomial.aeval_X, alg_hom.map_pow, polynomial.eval₂_mul, polynomial.eval₂_X_pow, alg_hom.map_mul],
  apply congr_arg2,
  rw polynomial.eval₂_C,
  rw polynomial.aeval_C,
  apply congr_fun, ext y,
  simp only [ring_hom.eq_int_cast],
  refl,
end

/--
multiply a rational number $a/b$ by an integer $m$ to get the integer (a*m)/b
-/
def rat_to_int_by_mul (r : ℚ) (m : ℕ) : ℤ := (r.num * m) / r.denom

theorem rat_to_int_by_mul_eq (r : ℚ) (m : ℕ) (h : r.denom ∣ m) : ↑(rat_to_int_by_mul r m) = r * m :=
begin
  unfold rat_to_int_by_mul,
  replace h : ∃ n, m = r.denom * n, exact exists_eq_mul_right_of_dvd h,
  rcases h with ⟨n, h⟩, conv_lhs {rw h},
  rw int.mul_div_assoc,
  push_cast,
  rw int.mul_div_cancel_left,
  rw h,
  norm_cast, push_cast, rw <-mul_assoc,
  simp only [rat.mul_denom_eq_num],
  norm_cast, intro rid,
  have H := r.pos,
  rw rid at H, linarith,

  norm_cast, exact dvd.intro n rfl,
end

theorem rat_to_int_by_mul_ne_zero (r : ℚ) (m : ℕ) (r_nonzero : r ≠ 0) (hr : r.denom ∣ m) (hm : m ≠ 0) : rat_to_int_by_mul r m ≠ 0 :=
begin
  unfold rat_to_int_by_mul,
  intro rid,
  suffices : r.num * ↑m / ↑(r.denom) < 0 ∨ 0 < r.num * ↑m / ↑(r.denom),
  {
    cases this; linarith,
  },
  by_cases (r.num > 0),
  {
    have key := (@int.lt_div_iff_mul_lt 0 (r.num * m) r.denom _ _).2 _,
    linarith,

    norm_cast, exact r.pos,
    apply dvd_mul_of_dvd_right, norm_cast, exact hr,
    simp only [zero_mul], apply mul_pos, exact h,
    norm_cast, exact nat.pos_of_ne_zero hm,
  },

  simp only [not_lt] at h,
  replace h : r.num < 0,
  {
    apply lt_of_le_of_ne, exact h, exact rat.num_ne_zero_of_ne_zero r_nonzero,
  },
  have key := ((@int.div_lt_iff_lt_mul (r.num * ↑m) 0 r.denom) _).2 _, left, exact key,
  norm_cast, exact r.pos, simp only [zero_mul],
  apply mul_neg_of_neg_of_pos h, norm_cast, exact nat.pos_of_ne_zero hm,
end

theorem rat_to_int_by_mul_ne_zero' (r : ℚ) (m : ℕ) (h : rat_to_int_by_mul r m ≠ 0) :
  r ≠ 0 :=
begin
  intro rid, rw rid at h,
  unfold rat_to_int_by_mul at h,
  simp only [zero_mul, euclidean_domain.zero_div, eq_self_iff_true, not_true, ne.def, rat.num_zero] at h,
  exact h,
end

/--
Given a polynomial $p∈ℚ[X]$, `coeffs_denom_prod p` is the product of the denominator of all coefficients
-/
def coeffs_denom_prod (p : ℚ[X]) : ℕ :=
  (finset.image (λ n, (p.coeff n).denom) p.support).prod id
lemma coeffs_denom_prod_ne_zero (p : ℚ[X]) : coeffs_denom_prod p ≠ 0 :=
begin
  unfold coeffs_denom_prod,
  rw finset.prod_ne_zero_iff, intros an han,
  simp only [exists_prop, finsupp.mem_support_iff, finset.mem_image, ne.def] at han,
  rcases han with ⟨n, nonzero, hn⟩, simp only [id.def, ne.def],
  intro rid, rw <-hn at rid,
  linarith [(p.coeff n).pos],
end

lemma denom_dvd_coeffs_denom_prod (p : ℚ[X]) (n : ℕ) : (p.coeff n).denom ∣ coeffs_denom_prod p :=
begin
  by_cases hn : n ∈ p.support,
  unfold coeffs_denom_prod,
  apply multiset.dvd_prod,
  simp only [multiset.mem_erase_dup, id.def, multiset.map_id', multiset.mem_map, finset.image_val],
  use (p.coeff n).denom, use n, split, exact hn, refl,

  have H := (p.mem_support_to_fun n).2,
  replace H := mt H hn,
  simp only [not_not] at H,
  replace H : p.coeff n = 0, rw <-H, refl,
  rw H,
  replace H : (0:ℚ).denom = 1, refl, rw H, exact one_dvd (coeffs_denom_prod p),
end


/--
for any $p∈ℚ[X]$, we multiply $p$ by the product of denominator of its coefficients to get an integer polynomial
-/
def rat_poly_to_int_poly (p : ℚ[X]) : ℤ[X] :=
{
  support := p.support,
  to_fun  := λ i, rat_to_int_by_mul (p.coeff i) (coeffs_denom_prod p),
  mem_support_to_fun :=
  begin
    intros n,
    split,
    {
      intros hn,
      apply rat_to_int_by_mul_ne_zero,
      exact (p.mem_support_to_fun n).1 hn,
      apply denom_dvd_coeffs_denom_prod,
      apply coeffs_denom_prod_ne_zero,
    },
    {
      intro h,
      have H := rat_to_int_by_mul_ne_zero' _ _ h,
      exact (p.mem_support_to_fun n).2 H,
    }
  end,
}

lemma rat_poly_to_int_poly_coeff (p : ℚ[X]) (n : ℕ) :
  (rat_poly_to_int_poly p).coeff n = rat_to_int_by_mul (p.coeff n) (coeffs_denom_prod p) :=
begin
  simp only [rat_poly_to_int_poly, polynomial.coeff_mk],
end

lemma rat_poly_to_int_coeff' (p : ℚ[X]) (n : ℕ) :
  ↑((rat_poly_to_int_poly p).coeff n) = (p.coeff n) * (coeffs_denom_prod p) :=
begin
  rw rat_poly_to_int_poly_coeff,
  rw rat_to_int_by_mul_eq,
  apply denom_dvd_coeffs_denom_prod,
end

lemma rat_poly_to_int_poly_eq (p : ℚ[X]) :
  (rat_poly_to_int_poly p).map (algebra_map ℤ ℚ) = ((polynomial.C (coeffs_denom_prod p : ℚ)) * p) :=
begin
  ext,
  simp only [rat_poly_to_int_coeff', ring_hom.eq_int_cast, polynomial.coeff_map],
  rw polynomial.coeff_C_mul, rw mul_comm,
end

theorem rat_poly_to_int_poly_p_ne_zero (p : ℚ[X]) (hp : p ≠ 0) : rat_poly_to_int_poly p ≠ 0 :=
begin
  intro rid,
  rw polynomial.ext_iff at rid,
  simp only [polynomial.coeff_zero] at rid,

  replace hp : ∃ n : ℕ, p.coeff n ≠ 0,
  {
    by_contra absurd,
    simp only [not_exists_not] at absurd,
    apply hp, ext, simp only [polynomial.coeff_zero], exact absurd n,
  },
  rcases hp with ⟨n, hn⟩,
  replace rid := rid n,
  simp only [rat_poly_to_int_poly_coeff] at rid,
  apply rat_to_int_by_mul_ne_zero (p.coeff n) (coeffs_denom_prod p) hn _ _,
  exact rid,
  apply denom_dvd_coeffs_denom_prod,
  apply coeffs_denom_prod_ne_zero,
end

theorem algebraic_over_Q_then_algebraic_over_Z (x : ℝ) : is_algebraic ℚ x -> is_algebraic ℤ x :=
begin
  rintro ⟨p, p_nonzero, root⟩,
  use rat_poly_to_int_poly p,

  split,
  apply rat_poly_to_int_poly_p_ne_zero, exact p_nonzero,
  have p_eq := rat_poly_to_int_poly_eq p,
  suffices :  polynomial.aeval x (polynomial.map (algebra_map ℤ ℚ) (rat_poly_to_int_poly p)) = 0,
  {
    simp only [polynomial.aeval_def] at this ⊢,
    rw polynomial.eval₂_map at this,
    have eq : (algebra_map ℚ ℝ).comp (algebra_map ℤ ℚ) = algebra_map ℤ ℝ,
    {
      ext y, simp only [ring_hom.eq_int_cast],
    }, rw eq at this, exact this,
  },
  rw p_eq,
  simp only [alg_hom.map_nat_cast, polynomial.C_eq_nat_cast, nat.cast_eq_zero, alg_hom.map_mul, mul_eq_zero],
  right, exact root,
end


theorem transcendental_iff_transcendental_over_ℚ (x : ℝ) : (transcendental x) <-> (transcendental_over_ℚ x) :=
begin
  split;
  intro h;
  contrapose h;
  rw not_not at h ⊢,
  apply algebraic_over_Q_then_algebraic_over_Z _ h,
  apply algebraic_over_Z_then_algebraic_over_Q _ h,
end

-- #lint
