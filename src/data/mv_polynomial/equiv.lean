/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/

import data.mv_polynomial.rename
import data.equiv.fin

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

/-- The ring isomorphism between multivariable polynomials in no variables and the ground ring. -/
@[simps]
def pempty_ring_equiv : mv_polynomial pempty R ≃+* R :=
{ to_fun    := mv_polynomial.eval₂ (ring_hom.id _) $ pempty.elim,
  inv_fun   := C,
  left_inv  := is_id (C.comp (eval₂_hom (ring_hom.id _) pempty.elim))
    (assume a : R, by { dsimp, rw [eval₂_C], refl }) (assume a, a.elim),
  right_inv := λ r, eval₂_C _ _ _,
  map_mul'  := λ _ _, eval₂_mul _ _,
  map_add'  := λ _ _, eval₂_add _ _ }

/-- The algebra isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps]
def pempty_alg_equiv : mv_polynomial pempty R ≃ₐ[R] R :=
{ to_fun    := mv_polynomial.eval₂ (ring_hom.id _) $ pempty.elim,
  inv_fun   := C,
  left_inv  := is_id (C.comp (eval₂_hom (ring_hom.id _) pempty.elim))
    (assume a : R, by { dsimp, rw [eval₂_C], refl }) (assume a, a.elim),
  right_inv := λ r, eval₂_C _ _ _,
  map_mul'  := λ _ _, eval₂_mul _ _,
  map_add'  := λ _ _, eval₂_add _ _,
  commutes' := λ _, by rw [mv_polynomial.algebra_map_eq]; simp }

/--
The ring isomorphism between multivariable polynomials in a single variable and
polynomials over the ground ring.
-/
@[simps]
def punit_ring_equiv : mv_polynomial punit R ≃+* polynomial R :=
{ to_fun    := eval₂ polynomial.C (λu:punit, polynomial.X),
  inv_fun   := polynomial.eval₂ mv_polynomial.C (X punit.star),
  left_inv  :=
    begin
      let f : polynomial R →+* mv_polynomial punit R :=
      ring_hom.of (polynomial.eval₂ mv_polynomial.C (X punit.star)),
      let g : mv_polynomial punit R →+* polynomial R :=
      ring_hom.of (eval₂ polynomial.C (λu:punit, polynomial.X)),
      show ∀ p, f.comp g p = p,
      apply is_id,
      { assume a, dsimp, rw [eval₂_C, polynomial.eval₂_C] },
      { rintros ⟨⟩, dsimp, rw [eval₂_X, polynomial.eval₂_X] }
    end,
  right_inv := assume p, polynomial.induction_on p
    (assume a, by rw [polynomial.eval₂_C, mv_polynomial.eval₂_C])
    (assume p q hp hq, by rw [polynomial.eval₂_add, mv_polynomial.eval₂_add, hp, hq])
    (assume p n hp,
      by rw [polynomial.eval₂_mul, polynomial.eval₂_pow, polynomial.eval₂_X, polynomial.eval₂_C,
        eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]),
  map_mul'  := λ _ _, eval₂_mul _ _,
  map_add'  := λ _ _, eval₂_add _ _ }

/-- The ring isomorphism between multivariable polynomials induced by an equivalence
of the variables.  -/
@[simps]
def ring_equiv_of_equiv (e : S₁ ≃ S₂) : mv_polynomial S₁ R ≃+* mv_polynomial S₂ R :=
{ to_fun    := rename e,
  inv_fun   := rename e.symm,
  left_inv  := λ p, by simp only [rename_rename, (∘), e.symm_apply_apply]; exact rename_id p,
  right_inv := λ p, by simp only [rename_rename, (∘), e.apply_symm_apply]; exact rename_id p,
  map_mul'  := (rename e).map_mul,
  map_add'  := (rename e).map_add }

/-- The ring isomorphism between multivariable polynomials induced by a ring isomorphism
of the ground ring. -/
@[simps]
def ring_equiv_congr [comm_semiring S₂] (e : R ≃+* S₂) :
  mv_polynomial S₁ R ≃+* mv_polynomial S₁ S₂ :=
{ to_fun    := map (e : R →+* S₂),
  inv_fun   := map (e.symm : S₂ →+* R),
  left_inv  := assume p,
    have (e.symm : S₂ →+* R).comp (e : R →+* S₂) = ring_hom.id _,
    { ext a, exact e.symm_apply_apply a },
    by simp only [map_map, this, map_id],
  right_inv := assume p,
    have (e : R →+* S₂).comp (e.symm : S₂ →+* R) = ring_hom.id _,
    { ext a, exact e.apply_symm_apply a },
    by simp only [map_map, this, map_id],
  map_mul'  := ring_hom.map_mul _,
  map_add'  := ring_hom.map_add _ }

/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebas and `e_var : S₁ ≃ S₂` is an isomorphism of
types, the induced isomorphism `mv_polynomial S₁ A ≃ₐ[R] mv_polynomial S₂ B`. -/
def alg_equiv_congr {A B : Type*} [comm_semiring A] [comm_semiring B] [algebra R A] [algebra R B]
  (e : A ≃ₐ[R] B) (e_var : S₁ ≃ S₂) :
  algebra.comap R A (mv_polynomial S₁ A) ≃ₐ[R] algebra.comap R B (mv_polynomial S₂ B) :=
{ commutes' := begin
  intro r,
  dsimp,
  have h₁ : algebra_map R (algebra.comap R A (mv_polynomial S₁ A)) r =
    C (algebra_map R A r) := rfl,
  have h₂ : algebra_map R (algebra.comap R B (mv_polynomial S₂ B)) r =
    C (algebra_map R B r) := rfl,
  have h : (↑(e.to_ring_equiv) : A →+* B) ((algebra_map R A) r) = e ((algebra_map R A) r) := rfl,
  rw [h₁, h₂, map, rename_C, eval₂_hom_C, ring_hom.comp_apply, h, alg_equiv.commutes],
  end,
  .. (ring_equiv_of_equiv A e_var).trans (ring_equiv_congr A e.to_ring_equiv)
}

/-- The algebra isomorphism between multivariable polynomials induced by an equivalence
of the variables.  -/
@[simps]
def alg_equiv_congr_left (e : S₁ ≃ S₂) : mv_polynomial S₁ R ≃ₐ[R] mv_polynomial S₂ R :=
alg_equiv_congr R alg_equiv.refl e

/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebas, the induced isomorphism
`mv_polynomial S₁ A ≃ₐ[R] mv_polynomial S₁ B`. -/
def alg_equiv_congr_right {A B : Type*} [comm_semiring A] [comm_semiring B] [algebra R A]
  [algebra R B] (e : A ≃ₐ[R] B) :
  algebra.comap R A (mv_polynomial S₁ A) ≃ₐ[R] algebra.comap R B (mv_polynomial S₁ B) :=
alg_equiv_congr R e (equiv.cast rfl)

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

instance is_semiring_hom_sum_to_iter : is_semiring_hom (sum_to_iter R S₁ S₂) :=
eval₂.is_semiring_hom _ _

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
eval₂_hom (ring_hom.of (eval₂ C (X ∘ sum.inr))) (X ∘ sum.inl)

lemma iter_to_sum_C_C (a : R) : iter_to_sum R S₁ S₂ (C (C a)) = C a :=
eq.trans (eval₂_C _ _ (C a)) (eval₂_C _ _ _)

lemma iter_to_sum_X (b : S₁) : iter_to_sum R S₁ S₂ (X b) = X (sum.inl b) :=
eval₂_X _ _ _

lemma iter_to_sum_C_X (c : S₂) : iter_to_sum R S₁ S₂ (C (X c)) = X (sum.inr c) :=
eq.trans (eval₂_C _ _ (X c)) (eval₂_X _ _ _)

/-- A helper function for `sum_ring_equiv`. -/
@[simps]
def mv_polynomial_equiv_mv_polynomial [comm_semiring S₃]
  (f : mv_polynomial S₁ R →+* mv_polynomial S₂ S₃)
  (g : mv_polynomial S₂ S₃ →+* mv_polynomial S₁ R)
  (hfgC : ∀a, f (g (C a)) = C a)
  (hfgX : ∀n, f (g (X n)) = X n)
  (hgfC : ∀a, g (f (C a)) = C a)
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
  { assume p,
    convert hom_eq_hom ((sum_to_iter R S₁ S₂).comp ((iter_to_sum R S₁ S₂).comp C)) C _ _ p,
    { assume a, dsimp, rw [iter_to_sum_C_C R S₁ S₂, sum_to_iter_C R S₁ S₂] },
    { assume c, dsimp, rw [iter_to_sum_C_X R S₁ S₂, sum_to_iter_Xr R S₁ S₂] } },
  { assume b, rw [iter_to_sum_X R S₁ S₂, sum_to_iter_Xl R S₁ S₂] },
  { assume a, rw [sum_to_iter_C R S₁ S₂, iter_to_sum_C_C R S₁ S₂] },
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
  algebra.comap R (mv_polynomial S₂ R) (mv_polynomial S₁ (mv_polynomial S₂ R)) :=
{ commutes' := begin
    intro r,
    change algebra_map R (algebra.comap R (mv_polynomial S₂ R)
      (mv_polynomial S₁ (mv_polynomial S₂ R))) r with C (C r),
    change algebra_map R (mv_polynomial (S₁ ⊕ S₂) R) r with C r,
    simp only [sum_ring_equiv, sum_to_iter_C, mv_polynomial_equiv_mv_polynomial_apply,
      ring_equiv.to_fun_eq_coe]
  end,
  ..sum_ring_equiv R S₁ S₂
}

/--
The ring isomorphism between multivariable polynomials in `option S₁` and
polynomials with coefficients in `mv_polynomial S₁ R`.
-/
def option_equiv_left : mv_polynomial (option S₁) R ≃+* polynomial (mv_polynomial S₁ R) :=
(ring_equiv_of_equiv R $ (equiv.option_equiv_sum_punit.{0} S₁).trans (equiv.sum_comm _ _)).trans $
(sum_ring_equiv R _ _).trans $
punit_ring_equiv _

/--
The ring isomorphism between multivariable polynomials in `option S₁` and
multivariable polynomials with coefficients in polynomials.
-/
def option_equiv_right : mv_polynomial (option S₁) R ≃+* mv_polynomial S₁ (polynomial R) :=
(ring_equiv_of_equiv R $ equiv.option_equiv_sum_punit.{0} S₁).trans $
(sum_ring_equiv R S₁ unit).trans $
ring_equiv_congr (mv_polynomial unit R) (punit_ring_equiv R)

/--
The ring isomorphism between multivariable polynomials in `fin (n + 1)` and
polynomials over multivariable polynomials in `fin n`.
-/
def fin_succ_equiv (n : ℕ) :
  mv_polynomial (fin (n + 1)) R ≃+* polynomial (mv_polynomial (fin n) R) :=
(ring_equiv_of_equiv R (fin_succ_equiv n)).trans
  (option_equiv_left R (fin n))

lemma fin_succ_equiv_eq (n : ℕ) :
  (fin_succ_equiv R n : mv_polynomial (fin (n + 1)) R →+* polynomial (mv_polynomial (fin n) R)) =
  eval₂_hom (polynomial.C.comp (C : R →+* mv_polynomial (fin n) R))
    (λ i : fin (n+1), fin.cases polynomial.X (λ k, polynomial.C (X k)) i) :=
begin
  apply ring_hom_ext,
  { intro r,
    dsimp [ring_equiv.coe_to_ring_hom, fin_succ_equiv, option_equiv_left, sum_ring_equiv],
    simp only [sum_to_iter_C, eval₂_C, rename_C, ring_hom.coe_comp] },
  { intro i,
    dsimp [ring_equiv.coe_to_ring_hom, fin_succ_equiv, option_equiv_left, sum_ring_equiv,
      _root_.fin_succ_equiv],
    by_cases hi : i = 0,
    { simp only [hi, fin.cases_zero, sum.swap, rename_X, equiv.option_equiv_sum_punit_none,
        equiv.sum_comm_apply, comp_app, sum_to_iter_Xl, eval₂_X] },
    { rw [← fin.succ_pred i hi],
      simp only [rename_X, equiv.sum_comm_apply, comp_app, eval₂_X,
        equiv.option_equiv_sum_punit_some, sum.swap, fin.cases_succ, sum_to_iter_Xr, eval₂_C] } }
end

@[simp] lemma fin_succ_equiv_apply (n : ℕ) (p : mv_polynomial (fin (n + 1)) R) :
  fin_succ_equiv R n p =
  eval₂_hom (polynomial.C.comp (C : R →+* mv_polynomial (fin n) R))
    (λ i : fin (n+1), fin.cases polynomial.X (λ k, polynomial.C (X k)) i) p :=
by { rw ← fin_succ_equiv_eq, refl }

lemma fin_succ_equiv_comp_C_eq_C {R : Type u} [comm_semiring R] (n : ℕ) :
  ((mv_polynomial.fin_succ_equiv R n).symm.to_ring_hom).comp
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
