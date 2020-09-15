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

As in other polynomial files we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `α : Type*` `[comm_semiring α]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : α`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ α`

## Tags

equivalence, isomorphism, morphism, ring hom, hom

-/

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : α} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section equiv

variables (α) [comm_semiring α]

/-- The ring isomorphism between multivariable polynomials in no variables and the ground ring. -/
def pempty_ring_equiv : mv_polynomial pempty α ≃+* α :=
{ to_fun    := mv_polynomial.eval₂ (ring_hom.id _) $ pempty.elim,
  inv_fun   := C,
  left_inv  := is_id (C.comp (eval₂_hom (ring_hom.id _) pempty.elim))
    (assume a : α, by { dsimp, rw [eval₂_C], refl }) (assume a, a.elim),
  right_inv := λ r, eval₂_C _ _ _,
  map_mul'  := λ _ _, eval₂_mul _ _,
  map_add'  := λ _ _, eval₂_add _ _ }

/--
The ring isomorphism between multivariable polynomials in a single variable and
polynomials over the ground ring.
-/
def punit_ring_equiv : mv_polynomial punit α ≃+* polynomial α :=
{ to_fun    := eval₂ polynomial.C (λu:punit, polynomial.X),
  inv_fun   := polynomial.eval₂ mv_polynomial.C (X punit.star),
  left_inv  :=
    begin
      let f : polynomial α →+* mv_polynomial punit α :=
      ring_hom.of (polynomial.eval₂ mv_polynomial.C (X punit.star)),
      let g : mv_polynomial punit α →+* polynomial α :=
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

/-- The ring isomorphism between multivariable polynomials induced by an equivalence of the variables.  -/
def ring_equiv_of_equiv (e : β ≃ γ) : mv_polynomial β α ≃+* mv_polynomial γ α :=
{ to_fun    := rename e,
  inv_fun   := rename e.symm,
  left_inv  := λ p, by simp only [rename_rename, (∘), e.symm_apply_apply]; exact rename_id p,
  right_inv := λ p, by simp only [rename_rename, (∘), e.apply_symm_apply]; exact rename_id p,
  map_mul'  := (rename e).map_mul,
  map_add'  := (rename e).map_add }

/-- The ring isomorphism between multivariable polynomials induced by a ring isomorphism of the ground ring. -/
def ring_equiv_congr [comm_semiring γ] (e : α ≃+* γ) : mv_polynomial β α ≃+* mv_polynomial β γ :=
{ to_fun    := map (e : α →+* γ),
  inv_fun   := map (e.symm : γ →+* α),
  left_inv  := assume p,
    have (e.symm : γ →+* α).comp (e : α →+* γ) = ring_hom.id _,
    { ext a, exact e.symm_apply_apply a },
    by simp only [map_map, this, map_id],
  right_inv := assume p,
    have (e : α →+* γ).comp (e.symm : γ →+* α) = ring_hom.id _,
    { ext a, exact e.apply_symm_apply a },
    by simp only [map_map, this, map_id],
  map_mul'  := ring_hom.map_mul _,
  map_add'  := ring_hom.map_add _ }

section
variables (β γ δ)

/--
The function from multivariable polynomials in a sum of two types,
to multivariable polynomials in one of the types,
with coefficents in multivariable polynomials in the other type.

See `sum_ring_equiv` for the ring isomorphism.
-/
def sum_to_iter : mv_polynomial (β ⊕ γ) α →+* mv_polynomial β (mv_polynomial γ α) :=
eval₂_hom (C.comp C) (λbc, sum.rec_on bc X (C ∘ X))

instance is_semiring_hom_sum_to_iter : is_semiring_hom (sum_to_iter α β γ) :=
eval₂.is_semiring_hom _ _

lemma sum_to_iter_C (a : α) : sum_to_iter α β γ (C a) = C (C a) :=
eval₂_C _ _ a

lemma sum_to_iter_Xl (b : β) : sum_to_iter α β γ (X (sum.inl b)) = X b :=
eval₂_X _ _ (sum.inl b)

lemma sum_to_iter_Xr (c : γ) : sum_to_iter α β γ (X (sum.inr c)) = C (X c) :=
eval₂_X _ _ (sum.inr c)

/--
The function from multivariable polynomials in one type,
with coefficents in multivariable polynomials in another type,
to multivariable polynomials in the sum of the two types.

See `sum_ring_equiv` for the ring isomorphism.
-/
def iter_to_sum : mv_polynomial β (mv_polynomial γ α) →+* mv_polynomial (β ⊕ γ) α :=
eval₂_hom (ring_hom.of (eval₂ C (X ∘ sum.inr))) (X ∘ sum.inl)

lemma iter_to_sum_C_C (a : α) : iter_to_sum α β γ (C (C a)) = C a :=
eq.trans (eval₂_C _ _ (C a)) (eval₂_C _ _ _)

lemma iter_to_sum_X (b : β) : iter_to_sum α β γ (X b) = X (sum.inl b) :=
eval₂_X _ _ _

lemma iter_to_sum_C_X (c : γ) : iter_to_sum α β γ (C (X c)) = X (sum.inr c) :=
eq.trans (eval₂_C _ _ (X c)) (eval₂_X _ _ _)

/-- A helper function for `sum_ring_equiv`. -/
def mv_polynomial_equiv_mv_polynomial [comm_semiring δ]
  (f : mv_polynomial β α →+* mv_polynomial γ δ)
  (g : mv_polynomial γ δ →+* mv_polynomial β α)
  (hfgC : ∀a, f (g (C a)) = C a)
  (hfgX : ∀n, f (g (X n)) = X n)
  (hgfC : ∀a, g (f (C a)) = C a)
  (hgfX : ∀n, g (f (X n)) = X n) :
  mv_polynomial β α ≃+* mv_polynomial γ δ :=
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
def sum_ring_equiv : mv_polynomial (β ⊕ γ) α ≃+* mv_polynomial β (mv_polynomial γ α) :=
begin
  apply @mv_polynomial_equiv_mv_polynomial α (β ⊕ γ) _ _ _ _
    (sum_to_iter α β γ) (iter_to_sum α β γ),
  { assume p,
    convert hom_eq_hom ((sum_to_iter α β γ).comp ((iter_to_sum α β γ).comp C)) C _ _ p,
    { assume a, dsimp, rw [iter_to_sum_C_C α β γ, sum_to_iter_C α β γ] },
    { assume c, dsimp, rw [iter_to_sum_C_X α β γ, sum_to_iter_Xr α β γ] } },
  { assume b, rw [iter_to_sum_X α β γ, sum_to_iter_Xl α β γ] },
  { assume a, rw [sum_to_iter_C α β γ, iter_to_sum_C_C α β γ] },
  { assume n, cases n with b c,
    { rw [sum_to_iter_Xl, iter_to_sum_X] },
    { rw [sum_to_iter_Xr, iter_to_sum_C_X] } },
end

/--
The ring isomorphism between multivariable polynomials in `option β` and
polynomials with coefficients in `mv_polynomial β α`.
-/
def option_equiv_left : mv_polynomial (option β) α ≃+* polynomial (mv_polynomial β α) :=
(ring_equiv_of_equiv α $ (equiv.option_equiv_sum_punit β).trans (equiv.sum_comm _ _)).trans $
(sum_ring_equiv α _ _).trans $
punit_ring_equiv _

/--
The ring isomorphism between multivariable polynomials in `option β` and
multivariable polynomials with coefficients in polynomials.
-/
def option_equiv_right : mv_polynomial (option β) α ≃+* mv_polynomial β (polynomial α) :=
(ring_equiv_of_equiv α $ equiv.option_equiv_sum_punit.{0} β).trans $
(sum_ring_equiv α β unit).trans $
ring_equiv_congr (mv_polynomial unit α) (punit_ring_equiv α)

/--
The ring isomorphism between multivariable polynomials in `fin (n + 1)` and
polynomials over multivariable polynomials in `fin n`.
-/
def fin_succ_equiv (n : ℕ) :
  mv_polynomial (fin (n + 1)) α ≃+* polynomial (mv_polynomial (fin n) α) :=
(ring_equiv_of_equiv α (fin_succ_equiv n)).trans
  (option_equiv_left α (fin n))

end

end equiv

end mv_polynomial
