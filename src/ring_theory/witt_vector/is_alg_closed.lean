import field_theory.is_alg_closed.basic
import field_theory.perfect_closure
import ring_theory.witt_vector.domain
import ring_theory.witt_vector.truncated
import data.mv_polynomial.supported

noncomputable theory

section
open finset
open_locale big_operators
variables {α β : Type*} [comm_semiring β]

lemma finset.prod_sum_succ (n k : ℕ) (f g : ℕ → β) :
  (∑ i in range (n+1), f i) * (∑ i in range (k+1), g i) =
    (∑ i in range n, f i) * (∑ i in range k, g i) +
    f n * (∑ i in range k, g i) +
    g k * (∑ i in range n, f i) +
    f n * g k :=
by rw [finset.sum_range_succ, finset.sum_range_succ]; ring

end

section
open finset
open_locale big_operators

lemma monoid_hom.map_sum (M N : Type*) [semiring M] --[add_comm_monoid M] [add_comm_monoid N]
  [semiring N] {T : Type*} [add_monoid_hom_class T M N] (f : T)
  {ι : Type} (s : finset ι) (g : ι → M) :
  f (∑ i in s, g i) = ∑ i in s, f (g i) :=
begin
  classical,
  apply finset.induction_on s,
  { simp },
  { intros a s has hf,
    simp [has, hf, map_add] }
end

end

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

section recursive_case_poly

-- this section is the attempt to define a `polynomial k` with positive degree.
-- the solution to this poly will be the `n+1`st entry of our desired Witt vector.

open witt_vector finset
open_locale big_operators


section
open mv_polynomial

/--
(∑ i : fin n, (y.coeff i)^(p^(n-i)) * p^i.val) * (∑ i : fin n, (y.coeff i)^(p^(n-i)) * p^i.val)
-/
def witt_poly_prod (n : ℕ) : mv_polynomial (fin 2 × ℕ) ℤ :=
rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ n) *
  rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ n)


lemma witt_poly_prod_vars (n : ℕ) :
  (witt_poly_prod p n).vars ⊆ finset.univ.product (finset.range (n + 1)) :=
begin
  rw [witt_poly_prod],
  apply subset.trans (vars_mul _ _),
  apply union_subset;
  { apply subset.trans (vars_rename _ _),
    simp [witt_polynomial_vars,image_subset_iff] }
end

lemma sum_ident_1 (n : ℕ) :
  (∑ i in range (n+1), p^i * (witt_mul p i)^(p^(n-i)) : mv_polynomial (fin 2 × ℕ) ℤ) =
    witt_poly_prod p n :=
begin
  simp only [witt_poly_prod],
  convert witt_structure_int_prop p (X (0 : fin 2) * X 1) n using 1,
  { simp only [witt_polynomial, witt_mul, int.nat_cast_eq_coe_nat],
    rw monoid_hom.map_sum,
    congr' 1 with i,
    congr' 1,
    have hsupp : (finsupp.single i (p ^ (n - i))).support = {i},
    { rw finsupp.support_eq_singleton,
      simp only [and_true, finsupp.single_eq_same, eq_self_iff_true, ne.def],
      exact pow_ne_zero _ hp.out.ne_zero,
       },
    simp only [bind₁_monomial, hsupp, int.cast_coe_nat, prod_singleton, ring_hom.eq_int_cast,
      finsupp.single_eq_same, C_pow, mul_eq_mul_left_iff, true_or, eq_self_iff_true], },
  { simp only [map_mul, bind₁_X_right] }
end

def extra_poly (n : ℕ) : mv_polynomial (fin 2 × ℕ) ℤ :=
∑ i in range n, p^i * (witt_mul p i)^(p^(n-i))

lemma extra_poly_vars (n : ℕ) : (extra_poly p n).vars ⊆ finset.univ.product (finset.range n) :=
begin
  rw [extra_poly],
  apply subset.trans (vars_sum_subset _ _),
  rw bUnion_subset,
  intros x hx,
  apply subset.trans (vars_mul _ _),
  apply union_subset,
  { apply subset.trans (vars_pow _ _),
    have : (p : mv_polynomial (fin 2 × ℕ) ℤ) = (C (p : ℤ)),
    { simp only [int.cast_coe_nat, ring_hom.eq_int_cast] },
    rw [this, vars_C],
    apply empty_subset },
  { apply subset.trans (vars_pow _ _),
    apply subset.trans (witt_mul_vars _ _),
    apply product_subset_product (subset.refl _),
    simp only [mem_range, range_subset] at hx ⊢,
    exact hx }
end

lemma sum_ident_2 (n : ℕ) :
  (p ^ n * witt_mul p n : mv_polynomial (fin 2 × ℕ) ℤ) + extra_poly p n = witt_poly_prod p n :=
begin
  convert sum_ident_1 p n,
  rw [sum_range_succ, add_comm, nat.sub_self, pow_zero, pow_one],
  refl
end


-- this is the remainder from sum_ident_3
def diff (n : ℕ) : mv_polynomial (fin 2 × ℕ) ℤ :=
sorry

lemma diff_vars (n : ℕ) : (diff p n).vars ⊆ univ.product (range (n+1)) :=
sorry


lemma sum_ident_3 (n : ℕ) :
  witt_poly_prod p (n+1) =
  (p^(n+1) * X (0, n+1)) * (p^(n+1) * X (1, n+1)) +
  (p^(n+1) * X (0, n+1)) * rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ n) +
  (p^(n+1) * X (1, n+1)) * rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ n) +
  diff p n :=
begin
  sorry
end

lemma sum_ident_4 (n : ℕ) :
  (p ^ (n + 1) * witt_mul p (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) =
  (p^(n+1) * X (0, n+1)) * (p^(n+1) * X (1, n+1)) +
  (p^(n+1) * X (0, n+1)) * rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ n) +
  (p^(n+1) * X (1, n+1)) * rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ n) +
  (diff p n - extra_poly p (n + 1)) :=
begin
  rw [← add_sub_assoc, eq_sub_iff_add_eq, sum_ident_2],
  exact sum_ident_3 _ _
end


/-- this is the guy from above -/
def poly_of_interest (n : ℕ) : mv_polynomial (fin 2 × ℕ) ℤ :=
witt_mul p (n + 1) - p^(n+1) * X (0, n+1) * X (1, n+1) -
  (X (0, n+1)) * rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ n) -
  (X (1, n+1)) * rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ n)

lemma sum_ident_5 (n : ℕ) :
  (p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) *
    poly_of_interest p n =
  (diff p n - extra_poly p (n + 1)) :=
begin
  simp only [poly_of_interest, mul_sub, mul_add, sub_eq_iff_eq_add'],
  rw sum_ident_4 p n,
  ring,
end

lemma prod_vars_subset (n : ℕ) :
  ((p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) * poly_of_interest p n).vars ⊆
  univ.product (range (n+1)) :=
begin
  rw sum_ident_5,
  apply subset.trans (vars_sub_subset _ _),
  apply union_subset,
  { apply diff_vars },
  { apply extra_poly_vars }
end

lemma poly_of_interest_vars_eq (n : ℕ) :
  ((p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) * (witt_mul p (n + 1) - p^(n+1) * X (0, n+1) * X (1, n+1) -
    (X (0, n+1)) * rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ n) -
    (X (1, n+1)) * rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ n))).vars =
  (poly_of_interest p n).vars :=
begin
  have : (p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) = C (p ^ (n + 1) : ℤ),
  { simp only [int.cast_coe_nat, ring_hom.eq_int_cast, C_pow, eq_self_iff_true] },
  rw [poly_of_interest, this, vars_C_mul],
  apply pow_ne_zero,
  exact_mod_cast hp.out.ne_zero
end

lemma poly_of_interest_vars (n : ℕ) : (poly_of_interest p n).vars ⊆ univ.product (range (n+1)) :=
by rw ← poly_of_interest_vars_eq; apply prod_vars_subset


lemma peval_poly_of_interest (n : ℕ) (x y : 𝕎 k) :
  peval (poly_of_interest p n) ![λ i, x.coeff i, λ i, y.coeff i] =
  (x * y).coeff (n + 1) - p^(n+1) * x.coeff (n+1) * y.coeff (n+1)
    - y.coeff (n+1) * ∑ i in range (n+1), p^i * x.coeff i ^ (p^(n-i))
    - x.coeff (n+1) * ∑ i in range (n+1), p^i * y.coeff i ^ (p^(n-i)) :=
begin
  simp only [poly_of_interest, peval, map_nat_cast, matrix.head_cons, map_pow, function.uncurry_apply_pair, aeval_X,
  matrix.cons_val_one, map_mul, matrix.cons_val_zero, map_sub],
  rw [sub_sub, add_comm (_ * _), ← sub_sub],
  have mvpz : (p : mv_polynomial ℕ ℤ) = mv_polynomial.C ↑p := by rw [ring_hom.eq_int_cast, int.cast_coe_nat ],
  congr' 3,
  { simp only [mul_coeff, peval] },
  all_goals
  { simp only [witt_polynomial_eq_sum_C_mul_X_pow, aeval, eval₂_rename, int.cast_coe_nat, ring_hom.eq_int_cast, eval₂_mul,
  function.uncurry_apply_pair, function.comp_app, eval₂_sum, eval₂_X, matrix.cons_val_zero, eval₂_pow,
  int.cast_pow, ring_hom.to_fun_eq_coe, coe_eval₂_hom, int.nat_cast_eq_coe_nat, alg_hom.coe_mk],
  congr' 1 with z,
  rw [mvpz, mv_polynomial.eval₂_C],
  refl }
end

/- characteristic `p` version -/
lemma peval_poly_of_interest' (n : ℕ) (x y : 𝕎 k) :
  peval (poly_of_interest p n) ![λ i, x.coeff i, λ i, y.coeff i] =
  (x * y).coeff (n + 1) - y.coeff (n+1) * x.coeff 0 ^ (p^n)
    - x.coeff (n+1) * y.coeff 0 ^ (p^n) :=
begin
  rw peval_poly_of_interest,
  have : (p : k) = 0 := char_p.cast_eq_zero (k) p,
  simp [this],
  congr; -- same proof both times, factor it out
  { rw finset.sum_eq_single_of_mem 0,
    { simp },
    { simp },
    { intros j _ hj,
      simp [zero_pow (zero_lt_iff.mpr hj)] } },
end

omit hp

lemma restrict_to_vars {σ : Type*} {s : set σ} (R : Type*) [comm_ring R] {F : mv_polynomial σ ℤ}
  (hF : ↑F.vars ⊆ s) :
  ∃ f : (s → R) → R, ∀ x : σ → R, f (x ∘ coe : s → R) = aeval x F :=
begin
  classical,
  rw [← mem_supported, supported_eq_range_rename, alg_hom.mem_range] at hF,
  cases hF with F' hF',
  use λ z, aeval z F',
  intro x,
  simp only [←hF', aeval_rename],
end

include hp

lemma nth_mul_coeff' (n : ℕ) :
  ∃ f : (truncated_witt_vector p (n+1) k → truncated_witt_vector p (n+1) k → k),
  ∀ (x y : 𝕎 k),
  f (truncate_fun (n+1) x) (truncate_fun (n+1) y)
  = (x * y).coeff (n+1) - y.coeff (n+1) * x.coeff 0 ^ (p^n)
    - x.coeff (n+1) * y.coeff 0 ^ (p^n) :=
begin
  simp [← peval_poly_of_interest'],
  obtain ⟨f₀, hf₀⟩ := restrict_to_vars k (poly_of_interest_vars p n),
  let f : truncated_witt_vector p (n+1) k → truncated_witt_vector p (n+1) k → k,
  { intros x y,
    apply f₀,
    rintros ⟨a, ha⟩,
    apply function.uncurry (![x, y]),
    simp only [true_and, multiset.mem_cons, range_coe, product_val, multiset.mem_range,
       multiset.mem_product, multiset.range_succ, mem_univ_val] at ha,
    refine ⟨a.fst, ⟨a.snd, _⟩⟩,
    cases ha with ha ha; linarith only [ha] },
  use f,
  intros x y,
  dsimp [peval],
  rw ← hf₀,
  simp [f],
  congr,
  ext a,
  cases a with a ha,
  cases a with i m,
  simp only [true_and, multiset.mem_cons, range_coe, product_val, multiset.mem_range,
    multiset.mem_product, multiset.range_succ, mem_univ_val] at ha,
  have ha' : m < n + 1 := by cases ha with ha ha; linarith only [ha],
  fin_cases i, -- surely this case split is not necessary
  { simpa using coeff_truncate_fun x ⟨m, ha'⟩ },
  { simpa using coeff_truncate_fun x ⟨m, ha'⟩ }
end

end

variable (n : ℕ)

-- this is the version we think is true in char p
lemma nth_mul_coeff (n : ℕ) : ∃ f : (truncated_witt_vector p (n+1) k → truncated_witt_vector p (n+1) k → k), ∀ (x y : 𝕎 k),
  (x * y).coeff (n+1) = x.coeff (n+1) * y.coeff 0 ^ (p^n) + y.coeff (n+1) * x.coeff 0 ^ (p^n)
    + f (truncate_fun (n+1) x) (truncate_fun (n+1) y) :=
begin
  obtain ⟨f, hf⟩ := nth_mul_coeff' p n,
  { use f,
    intros x y,
    rw hf x y,
    ring },
  { apply_instance },
  { apply_instance },
  { apply_instance },
end

def nth_remainder (n : ℕ) : (fin (n+1) → k) → (fin (n+1) → k) → k :=
classical.some (nth_mul_coeff p n)

lemma nth_remainder_spec (n : ℕ) (x y : 𝕎 k) :
  (x * y).coeff (n+1) = x.coeff (n+1) * y.coeff 0 ^ (p^n) + y.coeff (n+1) * x.coeff 0 ^ (p^n)
    + nth_remainder p n (truncate_fun (n+1) x) (truncate_fun (n+1) y) :=
classical.some_spec (nth_mul_coeff p n) _ _


open polynomial

def succ_nth_defining_poly (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k) : polynomial k :=
X^p * C (a₁.coeff 0 ^ (p^n)) - X * C (a₂.coeff 0 ^ (p^n))
  + C (a₁.coeff (n+1) * ((bs 0)^p)^(p^n) + nth_remainder p n (λ v, (bs v)^p) (truncate_fun (n+1) a₁)
       - a₂.coeff (n+1) * (bs 0)^p^n - nth_remainder p n bs (truncate_fun (n+1) a₂))

lemma succ_nth_defining_poly_degree (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (succ_nth_defining_poly p n a₁ a₂ bs).degree = p :=
begin
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ n)).degree = p,
  { rw [degree_mul, degree_C],
    { simp only [nat.cast_with_bot, add_zero, degree_X, degree_pow, nat.smul_one_eq_coe] },
    { exact pow_ne_zero _ ha₁ } },
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ n) - X * C (a₂.coeff 0 ^ p ^ n)).degree = p,
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
  (succ_nth_val p n a₁ a₂ bs ha₁ ha₂)^p * a₁.coeff 0 ^ (p^n)
  + a₁.coeff (n+1) * ((bs 0)^p)^(p^n) + nth_remainder p n (λ v, (bs v)^p) (truncate_fun (n+1) a₁)
   = (succ_nth_val p n a₁ a₂ bs ha₁ ha₂) * a₂.coeff 0 ^ (p^n)
     + a₂.coeff (n+1) * (bs 0)^(p^n) + nth_remainder p n bs (truncate_fun (n+1) a₂) :=
begin
  rw ← sub_eq_zero,
  have := succ_nth_val_spec p n a₁ a₂ bs ha₁ ha₂,
  simp only [polynomial.map_add, polynomial.eval_X, polynomial.map_pow, polynomial.eval_C,
    polynomial.eval_pow, succ_nth_defining_poly, polynomial.eval_mul, polynomial.eval_add,
    polynomial.eval_sub, polynomial.map_mul, polynomial.map_sub, polynomial.is_root.def] at this,
  convert this using 1,
  ring
end

end recursive_case_poly

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


-- what follows below is the previous attempt to do this directly in k.
-- a bit of the code may still be salvageable.

-- #check witt_structure_int_prop p (witt_mul p n) n

-- #check witt_polynomial


-- lemma nth_mul_coeff_aux1 (n : ℕ) (x y : 𝕎 k) :
--   ∑ i in range (n+1), ((x * y).coeff i)^(p^(n-i)) * p^i =
--   (∑ i in range (n+1), (x.coeff i)^(p^(n-i)) * p^i)*(∑ i in range (n+1), (y.coeff i)^(p^(n-i)) * p^i) :=
-- begin
--   have := witt_structure_prop p ((mv_polynomial.X 0 * mv_polynomial.X 1) : mv_polynomial (fin 2) ℤ) n,
--   replace this := congr_arg (λ z, witt_vector.peval z ![λ i, x.coeff i, λ i, y.coeff i]) this,
--   have mvpz : (p : mv_polynomial ℕ ℤ) = mv_polynomial.C ↑p := by rw [ring_hom.eq_int_cast, int.cast_coe_nat ],
--   have mvp : (p : mv_polynomial (fin 2 × ℕ) ℤ) = mv_polynomial.C ↑p := by rw [ring_hom.eq_int_cast, int.cast_coe_nat ],
--   simp only [int.cast_coe_nat, ring_hom.eq_int_cast, mv_polynomial.eval₂_mul, witt_vector.peval,
--     ring_hom.to_fun_eq_coe, mv_polynomial.coe_eval₂_hom, mv_polynomial.C_pow, mv_polynomial.aeval,
--     mv_polynomial.eval₂_map, witt_polynomial_eq_sum_C_mul_X_pow, int.nat_cast_eq_coe_nat,
--     alg_hom.coe_mk, mv_polynomial.eval₂_sum, mv_polynomial.eval₂_X, finset.sum_congr,
--     mv_polynomial.eval₂_pow] at this,
--   rw [mvpz, mv_polynomial.eval₂_C, ring_hom.eq_int_cast, int.cast_coe_nat,
--       mvp, mv_polynomial.eval₂_C, ring_hom.eq_int_cast, int.cast_coe_nat] at this,
--   simp only [mul_coeff],
--   convert this using 2; clear this,
--   { ext,
--     rw mul_comm,
--     simp only [peval, mv_polynomial.aeval, ring_hom.to_fun_eq_coe, mv_polynomial.coe_eval₂_hom, alg_hom.coe_mk],
--     congr },
--   all_goals
--   { simp only [mv_polynomial.eval₂_rename, int.cast_coe_nat, ring_hom.eq_int_cast, mv_polynomial.eval₂_mul,
--     function.uncurry_apply_pair, function.comp_app, mv_polynomial.eval₂_sum, mv_polynomial.eval₂_X,
--     matrix.cons_val_zero, mv_polynomial.eval₂_pow],
--     congr' 1 with z,
--     rw [mvpz, mv_polynomial.eval₂_C, mul_comm],
--     refl },
-- end

-- #exit
-- def trunc_sub_prod_coeff (n : ℕ) (x y : truncated_witt_vector p n k) : k :=
-- ∑ (i : fin n), (x * y).coeff i ^ p ^ (n - i) * ↑p ^ i.val

-- lemma nth_mul_coeff_aux2 (n : ℕ) (x y : 𝕎 k) :
--   (x * y).coeff n * p^n + trunc_sub_prod_coeff _ _ (truncate_fun n x) (truncate_fun n y) =
--   (∑ i in range (n+1), (x.coeff i)^(p^(n-i)) * p^i)*(∑ i in range (n+1), (y.coeff i)^(p^(n-i)) * p^i) :=
-- begin
--   rw [← nth_mul_coeff_aux1, finset.sum_range_succ, add_comm, nat.sub_self, pow_zero, pow_one],
--   congr' 1,
--   simp only [trunc_sub_prod_coeff, fin.val_eq_coe, ← truncate_fun_mul, coeff_truncate_fun],
--   sorry -- sum over fin vs sum over range
-- end

-- def trunc_sum_prod (n : ℕ) (x y : truncated_witt_vector p n k) : k :=
-- (∑ i : fin n, (y.coeff i)^(p^(n-i)) * p^i.val) * (∑ i : fin n, (y.coeff i)^(p^(n-i)) * p^i.val)

-- lemma nth_mul_coeff_aux3 (n : ℕ) (x y : 𝕎 k) :
--   (x * y).coeff n * p^n + trunc_sub_prod_coeff _ _ (truncate_fun n x) (truncate_fun n y) =
--     trunc_sum_prod _ _ (truncate_fun n x) (truncate_fun n y) +
--     x.coeff n * p^n * (∑ i in range n, (y.coeff i)^(p^(n-i)) * p^i) +
--     y.coeff n * p^n * (∑ i in range n, (x.coeff i)^(p^(n-i)) * p^i) +
--     x.coeff n * p^n * y.coeff n * p^n :=
-- begin
--   simp only [nth_mul_coeff_aux2, finset.prod_sum_succ, pow_one, tsub_self, pow_zero],
--   congr' 1,
--   { simp only [trunc_sum_prod, ← truncate_fun_mul, coeff_truncate_fun],
--     congr' 2,
--     sorry }, -- sum over fin vs sum over range
--   { simp only [mul_assoc] }
-- end

-- lemma nth_mul_coeff_aux4 (n : ℕ) (x y : 𝕎 k) :
--   (x * y).coeff n =
--     (x.coeff n * p^n * (∑ i in range n, (y.coeff i)^(p^(n-i)) * p^i) +
--     y.coeff n * p^n * (∑ i in range n, (x.coeff i)^(p^(n-i)) * p^i) +
--     x.coeff n * p^n * y.coeff n * p^n +
--     (trunc_sum_prod _ _ (truncate_fun n x) (truncate_fun n y) -
--       trunc_sub_prod_coeff _ _ (truncate_fun n x) (truncate_fun n y))) / p^n :=
-- begin
--   rw [eq_div_iff, add_sub, eq_sub_iff_add_eq, nth_mul_coeff_aux3],
--   { ring },
--   {  -- uh oh
--     sorry }
-- end
