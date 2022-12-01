/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/

import data.mv_polynomial.rename
import data.polynomial.algebra_map
import data.mv_polynomial.variables
import data.finsupp.fin
import logic.equiv.fin
import algebra.big_operators.fin


/-!
# Equivalences between polynomial rings

This file establishes a number of equivalences between polynomial rings,
based on equivalences between the underlying types.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

## Tags

equivalence, isomorphism, morphism, ring hom, hom

-/

noncomputable theory

open_locale classical big_operators polynomial

open set function finsupp add_monoid_algebra

universes u v w x
variables {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

section equiv

variables (R) [comm_semiring R]

/--
The ring isomorphism between multivariable polynomials in a single variable and
polynomials over the ground ring.
-/
@[simps]
def punit_alg_equiv : mv_polynomial punit R ≃ₐ[R] R[X] :=
{ to_fun    := eval₂ polynomial.C (λu:punit, polynomial.X),
  inv_fun   := polynomial.eval₂ mv_polynomial.C (X punit.star),
  left_inv  :=
    begin
      let f : R[X] →+* mv_polynomial punit R :=
        (polynomial.eval₂_ring_hom mv_polynomial.C (X punit.star)),
      let g : mv_polynomial punit R →+* R[X] :=
        (eval₂_hom polynomial.C (λu:punit, polynomial.X)),
      show ∀ p, f.comp g p = p,
      apply is_id,
      { ext a, dsimp, rw [eval₂_C, polynomial.eval₂_C] },
      { rintros ⟨⟩, dsimp, rw [eval₂_X, polynomial.eval₂_X] }
    end,
  right_inv := assume p, polynomial.induction_on p
    (assume a, by rw [polynomial.eval₂_C, mv_polynomial.eval₂_C])
    (assume p q hp hq, by rw [polynomial.eval₂_add, mv_polynomial.eval₂_add, hp, hq])
    (assume p n hp,
      by rw [polynomial.eval₂_mul, polynomial.eval₂_pow, polynomial.eval₂_X, polynomial.eval₂_C,
        eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]),
  map_mul'  := λ _ _, eval₂_mul _ _,
  map_add'  := λ _ _, eval₂_add _ _,
  commutes' := λ _, eval₂_C _ _ _}

section map
variables {R} (σ)

/-- If `e : A ≃+* B` is an isomorphism of rings, then so is `map e`. -/
@[simps apply]
def map_equiv [comm_semiring S₁] [comm_semiring S₂] (e : S₁ ≃+* S₂) :
  mv_polynomial σ S₁ ≃+* mv_polynomial σ S₂ :=
{ to_fun    := map (e : S₁ →+* S₂),
  inv_fun   := map (e.symm : S₂ →+* S₁),
  left_inv  := map_left_inverse e.left_inv,
  right_inv := map_right_inverse e.right_inv,
  ..map (e : S₁ →+* S₂) }

@[simp] lemma map_equiv_refl :
  map_equiv σ (ring_equiv.refl R) = ring_equiv.refl _ :=
ring_equiv.ext map_id

@[simp] lemma map_equiv_symm [comm_semiring S₁] [comm_semiring S₂] (e : S₁ ≃+* S₂) :
  (map_equiv σ e).symm = map_equiv σ e.symm := rfl

@[simp] lemma map_equiv_trans [comm_semiring S₁] [comm_semiring S₂] [comm_semiring S₃]
  (e : S₁ ≃+* S₂) (f : S₂ ≃+* S₃) :
  (map_equiv σ e).trans (map_equiv σ f) = map_equiv σ (e.trans f) :=
ring_equiv.ext (map_map e f)

variables {A₁ A₂ A₃ : Type*} [comm_semiring A₁] [comm_semiring A₂] [comm_semiring A₃]
variables [algebra R A₁] [algebra R A₂] [algebra R A₃]

/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `map e`. -/
@[simps apply]
def map_alg_equiv (e : A₁ ≃ₐ[R] A₂) :
  mv_polynomial σ A₁ ≃ₐ[R] mv_polynomial σ A₂ :=
{ to_fun := map (e : A₁ →+* A₂),
  ..map_alg_hom (e : A₁ →ₐ[R] A₂),
  ..map_equiv σ (e : A₁ ≃+* A₂) }

@[simp] lemma map_alg_equiv_refl :
  map_alg_equiv σ (alg_equiv.refl : A₁ ≃ₐ[R] A₁) = alg_equiv.refl :=
alg_equiv.ext map_id

@[simp] lemma map_alg_equiv_symm (e : A₁ ≃ₐ[R] A₂) :
  (map_alg_equiv σ e).symm = map_alg_equiv σ e.symm := rfl

@[simp] lemma map_alg_equiv_trans (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃) :
  (map_alg_equiv σ e).trans (map_alg_equiv σ f) = map_alg_equiv σ (e.trans f) :=
alg_equiv.ext (map_map e f)

end map

section
variables (S₁ S₂ S₃)

/--
The function from multivariable polynomials in a sum of two types,
to multivariable polynomials in one of the types,
with coefficents in multivariable polynomials in the other type.

See `sum_ring_equiv` for the ring isomorphism.
-/
def sum_to_iter : mv_polynomial (S₁ ⊕ S₂) R →+* mv_polynomial S₁ (mv_polynomial S₂ R) :=
eval₂_hom (C.comp C) (λbc, sum.rec_on bc X (C ∘ X))

@[simp]
lemma sum_to_iter_C (a : R) : sum_to_iter R S₁ S₂ (C a) = C (C a) :=
eval₂_C _ _ a

@[simp]
lemma sum_to_iter_Xl (b : S₁) : sum_to_iter R S₁ S₂ (X (sum.inl b)) = X b :=
eval₂_X _ _ (sum.inl b)

@[simp]
lemma sum_to_iter_Xr (c : S₂) : sum_to_iter R S₁ S₂ (X (sum.inr c)) = C (X c) :=
eval₂_X _ _ (sum.inr c)

/--
The function from multivariable polynomials in one type,
with coefficents in multivariable polynomials in another type,
to multivariable polynomials in the sum of the two types.

See `sum_ring_equiv` for the ring isomorphism.
-/
def iter_to_sum : mv_polynomial S₁ (mv_polynomial S₂ R) →+* mv_polynomial (S₁ ⊕ S₂) R :=
eval₂_hom (eval₂_hom C (X ∘ sum.inr)) (X ∘ sum.inl)

lemma iter_to_sum_C_C (a : R) : iter_to_sum R S₁ S₂ (C (C a)) = C a :=
eq.trans (eval₂_C _ _ (C a)) (eval₂_C _ _ _)

lemma iter_to_sum_X (b : S₁) : iter_to_sum R S₁ S₂ (X b) = X (sum.inl b) :=
eval₂_X _ _ _

lemma iter_to_sum_C_X (c : S₂) : iter_to_sum R S₁ S₂ (C (X c)) = X (sum.inr c) :=
eq.trans (eval₂_C _ _ (X c)) (eval₂_X _ _ _)

variable (σ)

/-- The algebra isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps] def is_empty_alg_equiv [he : is_empty σ] : mv_polynomial σ R ≃ₐ[R] R :=
alg_equiv.of_alg_hom
  (aeval (is_empty.elim he))
  (algebra.of_id _ _)
  (by { ext, simp [algebra.of_id_apply, algebra_map_eq] })
  (by { ext i m, exact is_empty.elim' he i })

/-- The ring isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps] def is_empty_ring_equiv [he : is_empty σ] : mv_polynomial σ R ≃+* R :=
(is_empty_alg_equiv R σ).to_ring_equiv

variable {σ}

/-- A helper function for `sum_ring_equiv`. -/
@[simps]
def mv_polynomial_equiv_mv_polynomial [comm_semiring S₃]
  (f : mv_polynomial S₁ R →+* mv_polynomial S₂ S₃)
  (g : mv_polynomial S₂ S₃ →+* mv_polynomial S₁ R)
  (hfgC : (f.comp g).comp C = C)
  (hfgX : ∀n, f (g (X n)) = X n)
  (hgfC : (g.comp f).comp C = C)
  (hgfX : ∀n, g (f (X n)) = X n) :
  mv_polynomial S₁ R ≃+* mv_polynomial S₂ S₃ :=
{ to_fun    := f, inv_fun := g,
  left_inv  := is_id (ring_hom.comp _ _) hgfC hgfX,
  right_inv := is_id (ring_hom.comp _ _) hfgC hfgX,
  map_mul'  := f.map_mul,
  map_add'  := f.map_add }

/--
The ring isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficents in multivariable polynomials in the other type.
-/
def sum_ring_equiv : mv_polynomial (S₁ ⊕ S₂) R ≃+* mv_polynomial S₁ (mv_polynomial S₂ R) :=
begin
  apply @mv_polynomial_equiv_mv_polynomial R (S₁ ⊕ S₂) _ _ _ _
    (sum_to_iter R S₁ S₂) (iter_to_sum R S₁ S₂),
  { refine ring_hom.ext (λ p, _),
    rw [ring_hom.comp_apply],
    convert hom_eq_hom ((sum_to_iter R S₁ S₂).comp ((iter_to_sum R S₁ S₂).comp C)) C _ _ p,
    { ext1 a, dsimp, rw [iter_to_sum_C_C R S₁ S₂, sum_to_iter_C R S₁ S₂] },
    { assume c, dsimp, rw [iter_to_sum_C_X R S₁ S₂, sum_to_iter_Xr R S₁ S₂] } },
  { assume b, rw [iter_to_sum_X R S₁ S₂, sum_to_iter_Xl R S₁ S₂] },
  { ext1 a, rw [ring_hom.comp_apply, ring_hom.comp_apply,
      sum_to_iter_C R S₁ S₂, iter_to_sum_C_C R S₁ S₂] },
  { assume n, cases n with b c,
    { rw [sum_to_iter_Xl, iter_to_sum_X] },
    { rw [sum_to_iter_Xr, iter_to_sum_C_X] } },
end

/--
The algebra isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficents in multivariable polynomials in the other type.
-/
def sum_alg_equiv : mv_polynomial (S₁ ⊕ S₂) R ≃ₐ[R]
  mv_polynomial S₁ (mv_polynomial S₂ R) :=
{ commutes' := begin
    intro r,
    have A : algebra_map R (mv_polynomial S₁ (mv_polynomial S₂ R)) r = (C (C r) : _), by refl,
    have B : algebra_map R (mv_polynomial (S₁ ⊕ S₂) R) r = C r, by refl,
    simp only [sum_ring_equiv, sum_to_iter_C, mv_polynomial_equiv_mv_polynomial_apply,
      ring_equiv.to_fun_eq_coe, A, B],
  end,
  ..sum_ring_equiv R S₁ S₂ }

section

-- this speeds up typeclass search in the lemma below
local attribute [instance, priority 2000] is_scalar_tower.right

/--
The algebra isomorphism between multivariable polynomials in `option S₁` and
polynomials with coefficients in `mv_polynomial S₁ R`.
-/
@[simps] def option_equiv_left :
  mv_polynomial (option S₁) R ≃ₐ[R] polynomial (mv_polynomial S₁ R) :=
alg_equiv.of_alg_hom
  (mv_polynomial.aeval (λ o, o.elim polynomial.X (λ s, polynomial.C (X s))))
  (polynomial.aeval_tower (mv_polynomial.rename some) (X none))
  (by ext : 2; simp [← polynomial.C_eq_algebra_map])
  (by ext i : 2; cases i; simp)

end

/--
The algebra isomorphism between multivariable polynomials in `option S₁` and
multivariable polynomials with coefficients in polynomials.
-/
def option_equiv_right : mv_polynomial (option S₁) R ≃ₐ[R] mv_polynomial S₁ R[X] :=
alg_equiv.of_alg_hom
  (mv_polynomial.aeval (λ o, o.elim (C polynomial.X) X))
  (mv_polynomial.aeval_tower (polynomial.aeval (X none)) (λ i, X (option.some i)))
  begin
    ext : 2;
    simp only [mv_polynomial.algebra_map_eq, option.elim, alg_hom.coe_comp, alg_hom.id_comp,
      is_scalar_tower.coe_to_alg_hom', comp_app, aeval_tower_C, polynomial.aeval_X, aeval_X,
      option.elim, aeval_tower_X, alg_hom.coe_id, id.def, eq_self_iff_true, implies_true_iff],
  end
  begin
    ext ⟨i⟩ : 2;
    simp only [option.elim, alg_hom.coe_comp, comp_app, aeval_X, aeval_tower_C,
      polynomial.aeval_X, alg_hom.coe_id, id.def, aeval_tower_X],
  end

variables (n : ℕ)

/--
The algebra isomorphism between multivariable polynomials in `fin (n + 1)` and
polynomials over multivariable polynomials in `fin n`.
-/
def fin_succ_equiv :
  mv_polynomial (fin (n + 1)) R ≃ₐ[R] polynomial (mv_polynomial (fin n) R) :=
(rename_equiv R (fin_succ_equiv n)).trans
  (option_equiv_left R (fin n))

lemma fin_succ_equiv_eq :
  (fin_succ_equiv R n : mv_polynomial (fin (n + 1)) R →+* polynomial (mv_polynomial (fin n) R)) =
  eval₂_hom (polynomial.C.comp (C : R →+* mv_polynomial (fin n) R))
    (λ i : fin (n+1), fin.cases polynomial.X (λ k, polynomial.C (X k)) i) :=
begin
  ext : 2,
  { simp only [fin_succ_equiv, option_equiv_left_apply, aeval_C, alg_equiv.coe_trans,
      ring_hom.coe_coe, coe_eval₂_hom, comp_app, rename_equiv_apply, eval₂_C, ring_hom.coe_comp,
      rename_C],
    refl },
  { intro i,
    refine fin.cases _ _ i;
    simp [fin_succ_equiv] }
end

@[simp] lemma fin_succ_equiv_apply (p : mv_polynomial (fin (n + 1)) R) :
  fin_succ_equiv R n p =
  eval₂_hom (polynomial.C.comp (C : R →+* mv_polynomial (fin n) R))
    (λ i : fin (n+1), fin.cases polynomial.X (λ k, polynomial.C (X k)) i) p :=
by { rw ← fin_succ_equiv_eq, refl }

lemma fin_succ_equiv_comp_C_eq_C {R : Type u} [comm_semiring R] (n : ℕ) :
  (↑(mv_polynomial.fin_succ_equiv R n).symm : polynomial (mv_polynomial (fin n) R) →+* _).comp
    ((polynomial.C).comp (mv_polynomial.C))
    = (mv_polynomial.C : R →+* mv_polynomial (fin n.succ) R) :=
begin
  refine ring_hom.ext (λ x, _),
  rw ring_hom.comp_apply,
  refine (mv_polynomial.fin_succ_equiv R n).injective
    (trans ((mv_polynomial.fin_succ_equiv R n).apply_symm_apply _) _),
  simp only [mv_polynomial.fin_succ_equiv_apply, mv_polynomial.eval₂_hom_C],
end

variables {n} {R}

lemma fin_succ_equiv_X_zero :
  fin_succ_equiv R n (X 0) = polynomial.X := by simp

lemma fin_succ_equiv_X_succ {j : fin n} :
  fin_succ_equiv R n (X j.succ) = polynomial.C (X j) := by simp

/-- The coefficient of `m` in the `i`-th coefficient of `fin_succ_equiv R n f` equals the
    coefficient of `finsupp.cons i m` in `f`. -/
lemma fin_succ_equiv_coeff_coeff (m : fin n →₀ ℕ)
  (f : mv_polynomial (fin (n + 1)) R) (i : ℕ) :
  coeff m (polynomial.coeff (fin_succ_equiv R n f) i) = coeff (m.cons i) f :=
begin
  induction f using mv_polynomial.induction_on' with j r p q hp hq generalizing i m,
  swap,
  { simp only [(fin_succ_equiv R n).map_add, polynomial.coeff_add, coeff_add, hp, hq] },
  simp only [fin_succ_equiv_apply, coe_eval₂_hom, eval₂_monomial, ring_hom.coe_comp, prod_pow,
    polynomial.coeff_C_mul, coeff_C_mul, coeff_monomial,
    fin.prod_univ_succ, fin.cases_zero, fin.cases_succ, ← ring_hom.map_prod, ← ring_hom.map_pow],
  rw [← mul_boole, mul_comm (polynomial.X ^ j 0), polynomial.coeff_C_mul_X_pow], congr' 1,
  obtain rfl | hjmi := eq_or_ne j (m.cons i),
  { simpa only [cons_zero, cons_succ, if_pos rfl, monomial_eq, C_1, one_mul, prod_pow]
      using coeff_monomial m m (1:R), },
  { simp only [hjmi, if_false],
    obtain hij | rfl := ne_or_eq i (j 0),
    { simp only [hij, if_false, coeff_zero] },
    simp only [eq_self_iff_true, if_true],
    have hmj : m ≠ j.tail, { rintro rfl, rw [cons_tail] at hjmi, contradiction },
    simpa only [monomial_eq, C_1, one_mul, prod_pow, finsupp.tail_apply, if_neg hmj.symm]
      using coeff_monomial m j.tail (1:R), }
end

lemma eval_eq_eval_mv_eval' (s : fin n → R) (y : R) (f : mv_polynomial (fin (n + 1)) R) :
  eval (fin.cons y s : fin (n + 1) → R) f =
    polynomial.eval y (polynomial.map (eval s) (fin_succ_equiv R n f)) :=
begin
  -- turn this into a def `polynomial.map_alg_hom`
  let φ : (mv_polynomial (fin n) R)[X] →ₐ[R] R[X] :=
  { commutes' := λ r, by { convert polynomial.map_C _, exact (eval_C _).symm },
    .. polynomial.map_ring_hom (eval s) },
  show aeval (fin.cons y s : fin (n + 1) → R) f =
    (polynomial.aeval y).comp (φ.comp (fin_succ_equiv R n).to_alg_hom) f,
  congr' 2,
  apply mv_polynomial.alg_hom_ext,
  rw fin.forall_fin_succ,
  simp only [aeval_X, fin.cons_zero, alg_equiv.to_alg_hom_eq_coe, alg_hom.coe_comp,
    polynomial.coe_aeval_eq_eval, polynomial.map_C, alg_hom.coe_mk, ring_hom.to_fun_eq_coe,
    polynomial.coe_map_ring_hom, alg_equiv.coe_alg_hom, comp_app, fin_succ_equiv_apply,
    eval₂_hom_X', fin.cases_zero, polynomial.map_X, polynomial.eval_X, eq_self_iff_true,
  fin.cons_succ, fin.cases_succ, eval_X, polynomial.eval_C, implies_true_iff, and_self],
end

lemma coeff_eval_eq_eval_coeff (s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R))
  (i : ℕ) : polynomial.coeff (polynomial.map (eval s') f) i = eval s' (polynomial.coeff f i) :=
by simp only [polynomial.coeff_map]

lemma support_coeff_fin_succ_equiv {f : mv_polynomial (fin (n + 1)) R} {i : ℕ}
  {m : fin n →₀ ℕ } : m ∈ (polynomial.coeff ((fin_succ_equiv R n) f) i).support
   ↔ (finsupp.cons i m) ∈ f.support :=
begin
  apply iff.intro,
  { intro h,
    simpa [←fin_succ_equiv_coeff_coeff] using h },
  { intro h,
    simpa [mem_support_iff, ←fin_succ_equiv_coeff_coeff m f i] using h },
end

lemma fin_succ_equiv_support (f : mv_polynomial (fin (n + 1)) R) :
  (fin_succ_equiv R n f).support = finset.image (λ m : fin (n + 1)→₀ ℕ, m 0) f.support :=
begin
  ext i,
  rw [polynomial.mem_support_iff, finset.mem_image, nonzero_iff_exists],
  split,
  { rintro ⟨m, hm⟩,
    refine ⟨cons i m, _, cons_zero _ _⟩,
    rw ← support_coeff_fin_succ_equiv,
    simpa using hm, },
  { rintro ⟨m, h, rfl⟩,
    refine ⟨tail m, _⟩,
    rwa [← coeff, ← mem_support_iff, support_coeff_fin_succ_equiv, cons_tail] },
end

lemma fin_succ_equiv_support' {f : mv_polynomial (fin (n + 1)) R} {i : ℕ} :
  finset.image (finsupp.cons i) (polynomial.coeff ((fin_succ_equiv R n) f) i).support
   = f.support.filter(λ m, m 0 = i) :=
begin
  ext m,
  rw [finset.mem_filter, finset.mem_image, mem_support_iff],
  conv_lhs
  { congr,
    funext,
    rw [mem_support_iff, fin_succ_equiv_coeff_coeff, ne.def] },
  split,
  { rintros ⟨m',⟨h, hm'⟩⟩,
    simp only [←hm'],
    exact ⟨h, by rw cons_zero⟩ },
  { intro h,
    use tail m,
    rw [← h.2, cons_tail],
    simp [h.1] }
end

lemma support_fin_succ_equiv_nonempty {f : mv_polynomial (fin (n + 1)) R} (h : f ≠ 0) :
  (fin_succ_equiv R n f).support.nonempty :=
begin
  by_contradiction c,
  simp only [finset.not_nonempty_iff_eq_empty, polynomial.support_eq_empty] at c,
  have t'' : (fin_succ_equiv R n f) ≠ 0,
  { let ii := (fin_succ_equiv R n).symm,
    have h' : f = 0 :=
      calc f = ii (fin_succ_equiv R n f) : by simpa only [ii, ←alg_equiv.inv_fun_eq_symm]
                                             using ((fin_succ_equiv R n).left_inv f).symm
      ...    = ii 0 : by rw c
      ...    = 0 : by simp,
    simpa [h'] using h },
  simpa [c] using h,
end

lemma degree_fin_succ_equiv {f : mv_polynomial (fin (n + 1)) R} (h : f ≠ 0) :
  (fin_succ_equiv R n f).degree = degree_of 0 f :=
begin
  have h' : (fin_succ_equiv R n f).support.sup (λ x , x)  = degree_of 0 f,
  { rw [degree_of_eq_sup, fin_succ_equiv_support f, finset.sup_image] },
  rw [polynomial.degree, ← h', finset.coe_sup_of_nonempty (support_fin_succ_equiv_nonempty h),
    finset.max_eq_sup_coe],
end

lemma nat_degree_fin_succ_equiv (f : mv_polynomial (fin (n + 1)) R) :
  (fin_succ_equiv R n f).nat_degree = degree_of 0 f :=
begin
  by_cases c : f = 0,
  { rw [c, (fin_succ_equiv R n).map_zero, polynomial.nat_degree_zero, degree_of_zero] },
  { rw [polynomial.nat_degree, degree_fin_succ_equiv (by simpa only [ne.def]) ],
    simp },
end

lemma degree_of_coeff_fin_succ_equiv (p : mv_polynomial (fin (n + 1)) R) (j : fin n)
  (i : ℕ) : degree_of j (polynomial.coeff (fin_succ_equiv R n p) i) ≤ degree_of j.succ p :=
begin
  rw [degree_of_eq_sup, degree_of_eq_sup, finset.sup_le_iff],
  intros m hm,
  rw ← finsupp.cons_succ j i m,
  convert finset.le_sup (support_coeff_fin_succ_equiv.1 hm),
  refl,
end

end

end equiv

end mv_polynomial
