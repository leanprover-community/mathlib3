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

open polynomial

variable {k}

section heathers_approach
open witt_vector finset
open_locale big_operators

-- maybe it's easier to start here, maybe not?
lemma nth_mul_coeff_ignoring_charp (x y : 𝕎 k) (n : ℕ) :
  ∃ f : ((fin n → k) → (fin n → k) → k),
  (x * y).coeff n =
    x.coeff n * (∑ i in range n, p^i*(y.coeff i)^(p^n-i)) +
    y.coeff n * (∑ i in range n, p^i*(x.coeff i)^(p^n-i)) +
    p^n * x.coeff n * y.coeff n + f (truncate_fun n x) (truncate_fun n y) :=
sorry

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
sorry

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
