import field_theory.is_alg_closed.basic
import field_theory.perfect_closure
import ring_theory.witt_vector.domain

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

#check mv_polynomial.bind₁
#check mv_polynomial.eval
#check λ f, mv_polynomial.eval f (witt_vector.witt_mul p 0)
open polynomial

variable {k}

section base_case

def pow_p_poly (a₁ : 𝕎 k) : polynomial k :=
witt_vector.peval (witt_vector.witt_mul p 0) ![λ n, if n = 0 then X^p else 0, λ n, C (a₁.coeff n)]

lemma pow_p_poly_degree {a₁ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) : (pow_p_poly p a₁).degree = p :=
by simp only [matrix.head_cons, nat.cast_with_bot, add_zero, mv_polynomial.aeval_X, if_true,
    witt_vector.peval, polynomial.degree_mul, function.uncurry_apply_pair, eq_self_iff_true,
    witt_vector.witt_mul_zero, pow_p_poly, matrix.cons_val_one, _root_.map_mul, degree_C ha₁,
    polynomial.degree_pow, polynomial.degree_X, matrix.cons_val_zero, nat.smul_one_eq_coe]

def pow_one_poly (a₂ : 𝕎 k) : polynomial k :=
witt_vector.peval (witt_vector.witt_mul p 0) ![λ n, if n = 0 then X else 0, λ n, C (a₂.coeff n)]

lemma pow_one_poly_degree {a₂ : 𝕎 k} (ha₂ : a₂.coeff 0 ≠ 0) : (pow_one_poly p a₂).degree = 1 :=
by simp only [matrix.head_cons, add_zero, mv_polynomial.aeval_X, if_true, witt_vector.peval,
    polynomial.degree_mul, function.uncurry_apply_pair, eq_self_iff_true, witt_vector.witt_mul_zero,
    pow_one_poly, matrix.cons_val_one, _root_.map_mul, polynomial.degree_X, matrix.cons_val_zero,
    degree_C ha₂]

lemma pow_one_poly_degree_lt {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (pow_one_poly p a₂).degree < (pow_p_poly p a₁).degree :=
begin
  rw [pow_p_poly_degree p ha₁, pow_one_poly_degree p ha₂],
  exact_mod_cast hp.out.one_lt
end

def base_poly (a₁ a₂ : 𝕎 k) : polynomial k :=
pow_p_poly p a₁ - pow_one_poly p a₂

lemma base_poly_degree {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (base_poly p a₁ a₂).degree ≠ 0 :=
begin
  rw [base_poly, degree_sub_eq_left_of_degree_lt, pow_p_poly_degree p ha₁],
  { exact_mod_cast hp.out.ne_zero },
  { exact pow_one_poly_degree_lt p ha₁ ha₂ }
end

lemma solution_exists {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  ∃ (x : k), (pow_p_poly p a₁ - pow_one_poly p a₂).is_root x :=
is_alg_closed.exists_root (pow_p_poly p a₁ - pow_one_poly p a₂) (base_poly_degree p ha₁ ha₂)

def solution {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : k :=
classical.some (solution_exists p ha₁ ha₂)

lemma solution_spec {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (pow_p_poly p a₁ - pow_one_poly p a₂).is_root (solution p ha₁ ha₂) :=
classical.some_spec (solution_exists p ha₁ ha₂)

lemma solution_spec' {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (solution p ha₁ ha₂)^p * a₁.coeff 0 = (solution p ha₁ ha₂) * a₂.coeff 0 :=
begin
  rw ← sub_eq_zero,
  simpa only [matrix.head_cons, polynomial.eval_X, polynomial.eval_C, mv_polynomial.aeval_X,
    if_true, witt_vector.peval, polynomial.eval_pow, function.uncurry_apply_pair, eq_self_iff_true,
    polynomial.eval_mul, witt_vector.witt_mul_zero, pow_p_poly, pow_one_poly, polynomial.eval_sub,
    matrix.cons_val_one, _root_.map_mul, matrix.cons_val_zero, polynomial.is_root.def]
    using solution_spec p ha₁ ha₂,
end

end base_case

section inductive_case

variables (n : ℕ) (prev_coeffs : fin n → k) (a₁ a₂ : 𝕎 k)
--(ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0)

def lhs_poly : polynomial k :=
witt_vector.peval (witt_vector.witt_mul p (n+1))
  ![λ k, if h : k < n then C (prev_coeffs ⟨k, h⟩)^p else if k = n then X^p else 0,
    λ n, C (a₁.coeff n)]

lemma degree_lhs_poly : (lhs_poly p n prev_coeffs a₁).degree = p :=
sorry

def rhs_poly : polynomial k :=
witt_vector.peval (witt_vector.witt_mul p (n+1))
  ![λ k, if h : k < n then C (prev_coeffs ⟨k, h⟩) else if k = n then X else 0,
    λ n, C (a₂.coeff n)]

def ind_poly : polynomial k :=
lhs_poly p n prev_coeffs a₁ - rhs_poly p n prev_coeffs a₂

lemma ind_poly_degree : (ind_poly p n prev_coeffs a₁ a₂).degree ≠ 0 :=
begin
  rw [ind_poly, degree_sub_eq_left_of_degree_lt]; sorry
end

end inductive_case

def find_important {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : ℕ → k
| 0       := solution p ha₁ ha₂ -- solve for `x` in
                   --  `(witt_vector.witt_mul 0).eval (![x ^ p, 0, ...], a₁)`
                   --        `= (witt_vector.witt_mul 0).eval (![x, 0, ...], a₂)`
| (n + 1) := sorry -- solve for `x` in
                   --  `(witt_vector.witt_mul (n + 1)).eval (![(b 0) ^ p, ..., (b n) ^ p, x ^ p, 0, ...], a₁)`
                   --        `= (witt_vector.witt_mul (n + 1)) (![b 0, ... b n, x, 0, ...], a₂)`

variable (k)

lemma important_aux {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  ∃ (b : 𝕎 k) (hb : b ≠ 0), witt_vector.frobenius b * a₁ = b * a₂ :=
sorry

lemma important {a : fraction_ring (𝕎 k)} (ha : a ≠ 0) :
  ∃ (b : fraction_ring (𝕎 k)) (hb : b ≠ 0) (m : ℤ), φ b * a = p ^ m * b :=
begin
  refine localization.induction_on a _,
  rintros ⟨r, q, hq⟩,
  rw mem_non_zero_divisors_iff_ne_zero at hq,
  have : r ≠ 0 := sorry,
  obtain ⟨m, r', hr', rfl⟩ := split p k r this,
  obtain ⟨n, q', hq', rfl⟩ := split p k q hq,
  obtain ⟨b, hb, hb⟩ := important_aux p k hr' hq',
  refine ⟨algebra_map (𝕎 k) _ b, _, m - n, _⟩,
  { sorry },
  simp [is_fraction_ring.field_equiv_of_ring_equiv],
  suffices :
  witt_vector.frobenius b * p ^ m * r' * p ^ n = p ^ m * b * (p ^ n * q') ,
  { -- apply `algebra_map` to both sides and divide
    sorry },
  have H := congr_arg (λ x : 𝕎 k, x * p ^ m * p ^ n) hb,
  dsimp at H,
  refine (eq.trans _ H).trans _; ring
end
