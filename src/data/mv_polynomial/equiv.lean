/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/

import data.mv_polynomial.rename
import data.equiv.fin
import data.polynomial.algebra_map

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

open_locale classical big_operators

open set function finsupp add_monoid_algebra

universes u v w x
variables {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section equiv

variables (R) [comm_semiring R]

/--
The ring isomorphism between multivariable polynomials in a single variable and
polynomials over the ground ring.
-/
@[simps]
def punit_alg_equiv : mv_polynomial punit R ≃ₐ[R] polynomial R :=
{ to_fun    := eval₂ polynomial.C (λu:punit, polynomial.X),
  inv_fun   := polynomial.eval₂ mv_polynomial.C (X punit.star),
  left_inv  :=
    begin
      let f : polynomial R →+* mv_polynomial punit R :=
        (polynomial.eval₂_ring_hom mv_polynomial.C (X punit.star)),
      let g : mv_polynomial punit R →+* polynomial R :=
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
def option_equiv_right : mv_polynomial (option S₁) R ≃ₐ[R] mv_polynomial S₁ (polynomial R) :=
alg_equiv.of_alg_hom
  (mv_polynomial.aeval (λ o, o.elim (C polynomial.X) X))
  (mv_polynomial.aeval_tower (polynomial.aeval (X none)) (λ i, X (option.some i)))
  (by ext : 2; simp [mv_polynomial.algebra_map_eq])
  (by ext i : 2; cases i; simp)

/--
The algebra isomorphism between multivariable polynomials in `fin (n + 1)` and
polynomials over multivariable polynomials in `fin n`.
-/
def fin_succ_equiv (n : ℕ) :
  mv_polynomial (fin (n + 1)) R ≃ₐ[R] polynomial (mv_polynomial (fin n) R) :=
(rename_equiv R (fin_succ_equiv n)).trans
  (option_equiv_left R (fin n))

lemma fin_succ_equiv_eq (n : ℕ) :
  (fin_succ_equiv R n : mv_polynomial (fin (n + 1)) R →+* polynomial (mv_polynomial (fin n) R)) =
  eval₂_hom (polynomial.C.comp (C : R →+* mv_polynomial (fin n) R))
    (λ i : fin (n+1), fin.cases polynomial.X (λ k, polynomial.C (X k)) i) :=
begin
  ext : 2,
  { simp only [fin_succ_equiv, option_equiv_left_apply, aeval_C, alg_equiv.coe_trans,
      alg_equiv.coe_alg_hom, coe_eval₂_hom, alg_hom.coe_to_ring_hom, comp_app, rename_equiv_apply,
      eval₂_C, ring_hom.coe_comp, coe_coe, rename_C],
    refl },
  { intro i,
    refine fin.cases _ _ i;
    simp [fin_succ_equiv] }
end

@[simp] lemma fin_succ_equiv_apply (n : ℕ) (p : mv_polynomial (fin (n + 1)) R) :
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

end

end equiv

end mv_polynomial
