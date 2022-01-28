import field_theory.is_alg_closed.basic
import field_theory.perfect_closure
import ring_theory.witt_vector.domain
import ring_theory.witt_vector.truncated

noncomputable theory

variables (p : ℕ) [hp : fact p.prime]
variables (k : Type*) [field k] [char_p k p] [is_alg_closed k]
include hp

/-- A field is perfect if Frobenius is surjective -/
def perfect_ring.of_surjective (k : Type*) [field k] [char_p k p]
  (h : function.surjective $ frobenius k p) :
  perfect_ring k p :=
{ pth_root' := function.surj_inv h,
  frobenius_pth_root' := function.surj_inv_eq h,
  pth_root_frobenius' := λ x, (frobenius k p).injective $ function.surj_inv_eq h _ }

-- an algebraically closed field is perfect, many google hits, maybe somewhere in mathlib?
instance is_alg_closed.perfect_ring : perfect_ring k p :=
perfect_ring.of_surjective p k $ λ x, is_alg_closed.exists_pow_nat_eq _ $ fact.out _

local notation `𝕎` := witt_vector p
local notation `K` := fraction_ring (𝕎 k)

lemma witt_vector.frobenius_bijective (R : Type*) [comm_ring R] [char_p R p] [perfect_ring R p] :
  function.bijective (@witt_vector.frobenius p R _ _) :=
begin
  rw witt_vector.frobenius_eq_map_frobenius,
  exact ⟨witt_vector.map_injective _ (frobenius_equiv R p).injective,
    witt_vector.map_surjective _ (frobenius_equiv R p).surjective⟩,
end

local notation `φ` := is_fraction_ring.field_equiv_of_ring_equiv
  (ring_equiv.of_bijective _ (witt_vector.frobenius_bijective p k))

/-- Johan: this is basically the same as `𝕎 k` being a DVR. -/
lemma split (a : 𝕎 k) (ha : a ≠ 0) :
  ∃ (m : ℕ) (b : 𝕎 k), b.coeff 0 ≠ 0 ∧ a = p ^ m * b :=
begin
  obtain ⟨m, c, hc, hcm⟩ := witt_vector.verschiebung_nonzero ha,
  obtain ⟨b, rfl⟩ := (witt_vector.frobenius_bijective p k).surjective.iterate m c,
  rw witt_vector.iterate_frobenius_coeff at hc,
  have := congr_fun (witt_vector.verschiebung_frobenius_comm.comp_iterate m) b,
  simp at this,
  rw ← this at hcm,
  refine ⟨m, b, _, _⟩,
  { contrapose! hc,
    have : 0 < p ^ m := pow_pos (nat.prime.pos (fact.out _)) _,
    simp [hc, this] },
  { rw ← mul_left_iterate (p : 𝕎 k) m,
    convert hcm,
    ext1 x,
    rw [mul_comm, ← witt_vector.verschiebung_frobenius x] },
end

-- lemma witt_vector.is_Hausdorff : is_Hausdorff (𝕎 k)


variable {k}

section heathers_approach
open witt_vector finset
open_locale big_operators

-- -- maybe it's easier to start here, maybe not?
-- lemma nth_mul_coeff_ignoring_charp (x y : 𝕎 k) (n : ℕ) :
--   ∃ f : ((fin n → k) → (fin n → k) → k),
--   (x * y).coeff n =
--     x.coeff n * (∑ i in range n, p^i*(y.coeff i)^(p^n-i)) +
--     y.coeff n * (∑ i in range n, p^i*(x.coeff i)^(p^n-i)) +
--     p^n * x.coeff n * y.coeff n + f (truncate_fun n x) (truncate_fun n y) :=
-- sorry

lemma nth_mul_coeff_aux1 (n : ℕ) (x y : 𝕎 k) :
  ∑ i in range (n+1), ((x * y).coeff i)^(p^(n-i)) * p^i =
  (∑ i in range (n+1), (x.coeff i)^(p^(n-i)) * p^i)*(∑ i in range (n+1), (y.coeff i)^(p^(n-i)) * p^i) :=
begin
  have := witt_structure_prop p ((mv_polynomial.X 0 * mv_polynomial.X 1) : mv_polynomial (fin 2) ℤ) n,
  replace this := congr_arg (λ z, witt_vector.peval z ![λ i, x.coeff i, λ i, y.coeff i]) this,
  have mvpz : (p : mv_polynomial ℕ ℤ) = mv_polynomial.C ↑p := by rw [ring_hom.eq_int_cast, int.cast_coe_nat ],
  have mvp : (p : mv_polynomial (fin 2 × ℕ) ℤ) = mv_polynomial.C ↑p := by rw [ring_hom.eq_int_cast, int.cast_coe_nat ],
  simp only [int.cast_coe_nat, ring_hom.eq_int_cast, mv_polynomial.eval₂_mul, witt_vector.peval,
    ring_hom.to_fun_eq_coe, mv_polynomial.coe_eval₂_hom, mv_polynomial.C_pow, mv_polynomial.aeval,
    mv_polynomial.eval₂_map, witt_polynomial_eq_sum_C_mul_X_pow, int.nat_cast_eq_coe_nat,
    alg_hom.coe_mk, mv_polynomial.eval₂_sum, mv_polynomial.eval₂_X, finset.sum_congr,
    mv_polynomial.eval₂_pow] at this,
  rw [mvpz, mv_polynomial.eval₂_C, ring_hom.eq_int_cast, int.cast_coe_nat,
      mvp, mv_polynomial.eval₂_C, ring_hom.eq_int_cast, int.cast_coe_nat] at this,
  simp only [mul_coeff],
  convert this using 2; clear this,
  { ext,
    rw mul_comm,
    simp only [peval, mv_polynomial.aeval, ring_hom.to_fun_eq_coe, mv_polynomial.coe_eval₂_hom, alg_hom.coe_mk],
    congr },
  all_goals
  { simp only [mv_polynomial.eval₂_rename, int.cast_coe_nat, ring_hom.eq_int_cast, mv_polynomial.eval₂_mul,
    function.uncurry_apply_pair, function.comp_app, mv_polynomial.eval₂_sum, mv_polynomial.eval₂_X,
    matrix.cons_val_zero, mv_polynomial.eval₂_pow],
    congr' 1 with z,
    rw [mvpz, mv_polynomial.eval₂_C, mul_comm],
    refl },
end

#check finset.sum

def trunc_sub_prod_coeff (n : ℕ) (x y : truncated_witt_vector p n k) : k :=
∑ (i : fin n), (x * y).coeff i ^ p ^ (n - i) * ↑p ^ i.val

lemma nth_mul_coeff_aux2 (n : ℕ) : ∃ f : ((fin n → k) → (fin n → k) → k), ∀ (x y : 𝕎 k),
  (x * y).coeff n * p^n + f (truncate_fun n x) (truncate_fun n y) =
  (∑ i in range (n+1), (x.coeff i)^(p^(n-i)) * p^i)*(∑ i in range (n+1), (y.coeff i)^(p^(n-i)) * p^i) :=
begin
  refine ⟨trunc_sub_prod_coeff p (n), λ x y, _⟩,
  rw [← nth_mul_coeff_aux1, finset.sum_range_succ, add_comm, nat.sub_self, pow_zero, pow_one],
  congr' 1,
  simp only [trunc_sub_prod_coeff, fin.val_eq_coe, ← truncate_fun_mul, coeff_truncate_fun],
  sorry
end

#exit
-- this is the version we think is true in char p
lemma nth_mul_coeff (n : ℕ) : ∃ f : ((fin (n+1) → k) → (fin (n+1) → k) → k), ∀ (x y : 𝕎 k),
  (x * y).coeff (n+1) = x.coeff (n+1) * y.coeff 0 ^ (p^(n+1)) + y.coeff (n+1) * x.coeff 0 ^ (p^(n+1))
    + f (truncate_fun (n+1) x) (truncate_fun (n+1) y) :=
sorry

def nth_remainder (n : ℕ) : (fin (n+1) → k) → (fin (n+1) → k) → k :=
classical.some (nth_mul_coeff p n)

lemma nth_remainder_spec (n : ℕ) (x y : 𝕎 k) :
  (x * y).coeff (n+1) = x.coeff (n+1) * y.coeff 0 ^ (p^(n+1)) + y.coeff (n+1) * x.coeff 0 ^ (p^(n+1))
    + nth_remainder p n (truncate_fun (n+1) x) (truncate_fun (n+1) y) :=
classical.some_spec (nth_mul_coeff p n) _ _


open polynomial

def succ_nth_defining_poly (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k) : polynomial k :=
X^p * C (a₁.coeff 0 ^ (p^(n+1))) - X * C (a₂.coeff 0 ^ (p^(n+1)))
  + C (a₁.coeff (n+1) * ((bs 0)^p)^(p^(n+1)) + nth_remainder p n (λ v, (bs v)^p) (truncate_fun (n+1) a₁)
       - a₂.coeff (n+1) * (bs 0)^p^(n+1) - nth_remainder p n bs (truncate_fun (n+1) a₂))

lemma succ_nth_defining_poly_degree (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (succ_nth_defining_poly p n a₁ a₂ bs).degree = p :=
begin
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1))).degree = p,
  { rw [degree_mul, degree_C],
    { simp only [nat.cast_with_bot, add_zero, degree_X, degree_pow, nat.smul_one_eq_coe] },
    { exact pow_ne_zero _ ha₁ } },
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1)) - X * C (a₂.coeff 0 ^ p ^ (n + 1))).degree = p,
  { rw [degree_sub_eq_left_of_degree_lt, this],
    rw [this, degree_mul, degree_C, degree_X, add_zero],
    { exact_mod_cast hp.out.one_lt },
    { exact pow_ne_zero _ ha₂ } },
  rw [succ_nth_defining_poly, degree_add_eq_left_of_degree_lt, this],
  apply lt_of_le_of_lt (degree_C_le),
  rw [this],
  exact_mod_cast hp.out.pos
end

def root_exists (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  ∃ b : k, (succ_nth_defining_poly p n a₁ a₂ bs).is_root b :=
is_alg_closed.exists_root _ $
  by simp [(succ_nth_defining_poly_degree p n a₁ a₂ bs ha₁ ha₂), hp.out.ne_zero]

def succ_nth_val (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : k :=
classical.some (root_exists p n a₁ a₂ bs ha₁ ha₂)

lemma succ_nth_val_spec (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (succ_nth_defining_poly p n a₁ a₂ bs).is_root (succ_nth_val p n a₁ a₂ bs ha₁ ha₂) :=
classical.some_spec (root_exists p n a₁ a₂ bs ha₁ ha₂)

lemma succ_nth_val_spec' (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (succ_nth_val p n a₁ a₂ bs ha₁ ha₂)^p * a₁.coeff 0 ^ (p^(n+1))
  + a₁.coeff (n+1) * ((bs 0)^p)^(p^(n+1)) + nth_remainder p n (λ v, (bs v)^p) (truncate_fun (n+1) a₁)
   = (succ_nth_val p n a₁ a₂ bs ha₁ ha₂) * a₂.coeff 0 ^ (p^(n+1))
     + a₂.coeff (n+1) * (bs 0)^p^(n+1) + nth_remainder p n bs (truncate_fun (n+1) a₂) :=
begin
  rw ← sub_eq_zero,
  have := succ_nth_val_spec p n a₁ a₂ bs ha₁ ha₂,
  simp only [polynomial.map_add, polynomial.eval_X, polynomial.map_pow, polynomial.eval_C,
    polynomial.eval_pow, succ_nth_defining_poly, polynomial.eval_mul, polynomial.eval_add,
    polynomial.eval_sub, polynomial.map_mul, polynomial.map_sub, polynomial.is_root.def] at this,
  convert this using 1,
  ring
end

end heathers_approach

section base_case

def solution_pow {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  ∃ x : k, x^(p-1) = a₂.coeff 0 / a₁.coeff 0 :=
is_alg_closed.exists_pow_nat_eq _ $ by linarith [hp.out.one_lt, le_of_lt hp.out.one_lt]

def solution {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : k :=
classical.some $ solution_pow p ha₁ ha₂

lemma solution_spec {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (solution p ha₁ ha₂)^(p-1) = a₂.coeff 0 / a₁.coeff 0 :=
classical.some_spec $ solution_pow p ha₁ ha₂

lemma solution_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  solution p ha₁ ha₂ ≠ 0 :=
begin
  intro h,
  have := solution_spec p ha₁ ha₂,
  rw [h, zero_pow] at this,
  { simpa [ha₁, ha₂] using _root_.div_eq_zero_iff.mp this.symm },
  { linarith [hp.out.one_lt, le_of_lt hp.out.one_lt] }
end

lemma solution_spec' {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (solution p ha₁ ha₂)^p * a₁.coeff 0 = (solution p ha₁ ha₂) * a₂.coeff 0 :=
begin
  have := solution_spec p ha₁ ha₂,
  cases nat.exists_eq_succ_of_ne_zero hp.out.ne_zero with q hq,
  have hq' : q = p - 1 := by simp only [hq, tsub_zero, nat.succ_sub_succ_eq_sub],
  conv_lhs {congr, congr, skip, rw hq},
  rw [pow_succ', hq', this],
  field_simp [ha₁, mul_comm],
end


end base_case

noncomputable def find_important {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : ℕ → k
| 0       := solution p ha₁ ha₂ -- solve for `x` in
                   --  `(witt_vector.witt_mul 0).eval (![x ^ p, 0, ...], a₁)`
                   --        `= (witt_vector.witt_mul 0).eval (![x, 0, ...], a₂)`
| (n + 1) := succ_nth_val p n a₁ a₂ (λ i, find_important i.val) ha₁ ha₂
using_well_founded { dec_tac := `[apply fin.is_lt] }

-- solve for `x` in
                   --  `(witt_vector.witt_mul (n + 1)).eval (![(b 0) ^ p, ..., (b n) ^ p, x ^ p, 0, ...], a₁)`
                   --        `= (witt_vector.witt_mul (n + 1)) (![b 0, ... b n, x, 0, ...], a₂)`


lemma find_important_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  witt_vector.mk p (find_important p ha₁ ha₂) ≠ 0 :=
begin
  intro h,
  apply solution_nonzero p ha₁ ha₂,
  simpa [← h, find_important] using witt_vector.zero_coeff p k 0
end

variable (k)

lemma important_aux {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  ∃ (b : 𝕎 k) (hb : b ≠ 0), witt_vector.frobenius b * a₁ = b * a₂ :=
begin
  refine ⟨witt_vector.mk p (find_important p ha₁ ha₂), find_important_nonzero p ha₁ ha₂, _⟩,
  ext n,
  induction n with n ih,
  { simp only [witt_vector.mul_coeff_zero, witt_vector.coeff_frobenius_char_p, find_important],
    apply solution_spec' },
  { simp only [nth_remainder_spec, witt_vector.coeff_frobenius_char_p, ih, find_important],
    have := succ_nth_val_spec' p (n) a₁ a₂ (λ (i : fin (n + 1)), find_important p ha₁ ha₂ i.val) ha₁ ha₂,
    simp only [find_important, fin.val_zero] at this,
    convert this using 3,
    apply truncated_witt_vector.ext,
    intro i,
    simp only [fin.val_eq_coe, witt_vector.coeff_truncate_fun, witt_vector.coeff_frobenius_char_p],
    refl }
end

lemma important {a : fraction_ring (𝕎 k)} (ha : a ≠ 0) :
  ∃ (b : fraction_ring (𝕎 k)) (hb : b ≠ 0) (m : ℤ), φ b * a = p ^ m * b :=
begin
  revert ha,
  refine localization.induction_on a _,
  rintros ⟨r, q, hq⟩ hrq,
  rw mem_non_zero_divisors_iff_ne_zero at hq,
  have : r ≠ 0 := λ h, hrq (by simp [h]),
  obtain ⟨m, r', hr', rfl⟩ := split p k r this,
  obtain ⟨n, q', hq', rfl⟩ := split p k q hq,
  obtain ⟨b, hb, hbrq⟩ := important_aux p k hr' hq',
  refine ⟨algebra_map (𝕎 k) _ b, _, m - n, _⟩,
  { simpa using (is_fraction_ring.injective (𝕎 k) (fraction_ring (𝕎 k))).ne hb },
  have key : witt_vector.frobenius b * p ^ m * r' * p ^ n = p ^ m * b * (p ^ n * q'),
  { have H := congr_arg (λ x : 𝕎 k, x * p ^ m * p ^ n) hbrq,
    dsimp at H,
    refine (eq.trans _ H).trans _; ring },
  have hp : (p : 𝕎 k) ≠ 0,
  -- a better way here would be that the Witt vectors have characteristic 0, does mathlib know it?
  { have : (p : 𝕎 k).coeff 1 = 1 := by simpa using witt_vector.coeff_p_pow 1,
    intros h,
    simpa [h] using this },
  have hp' : (p : fraction_ring (𝕎 k)) ≠ 0,
  { simpa using (is_fraction_ring.injective (𝕎 k) (fraction_ring (𝕎 k))).ne hp },
  have hq'' : algebra_map (𝕎 k) (fraction_ring (𝕎 k)) q' ≠ 0,
  { have hq''' : q' ≠ 0 := λ h, hq' (by simp [h]),
    simpa using (is_fraction_ring.injective (𝕎 k) (fraction_ring (𝕎 k))).ne hq''' },
  rw zpow_sub₀ hp',
  field_simp,
  simp [is_fraction_ring.field_equiv_of_ring_equiv],
  convert congr_arg (λ x, algebra_map (𝕎 k) (fraction_ring (𝕎 k)) x) key using 1,
  { simp only [ring_hom.map_mul, ring_hom.map_pow, map_nat_cast],
    ring },
  { simp only [ring_hom.map_mul, ring_hom.map_pow, map_nat_cast] }
end
