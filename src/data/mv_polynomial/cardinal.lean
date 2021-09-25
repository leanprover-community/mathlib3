/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.W.cardinal
import data.mv_polynomial.basic
/-!
# Cardinality of Polynomial Ring

The main result in this file is `mv_polynomial.cardinal_mk_le_max`, which says that
the cardinality of `mv_polynomial σ R` is bounded above by the maximum of `#R`, `#σ`
and `ω`.

-/
universes u
/-
The definitions `mv_polynomial_fun` and `arity` are motivated by defining the following
inductive type as a `W_type` in order to be able to use theorems about the cardinality
of `W_type`.

inductive mv_polynomial_term (σ R : Type u) : Type u
| of_ring : R → mv_polynomial_term
| X : σ → mv_polynomial_term
| add : mv_polynomial_term → mv_polynomial_term → mv_polynomial_term
| mul : mv_polynomial_term → mv_polynomial_term → mv_polynomial_term

`W_type (arity σ R)` is isomorphic to the above type.
-/
open cardinal
open_locale cardinal

/-- A type used to prove theorems about the cardinality of `mv_polynomial σ R`. The
`W_type (arity σ R)` has a constant for every element of `R` and `σ` and two binary functions. -/
private def mv_polynomial_fun (σ R : Type u) : Type u :=
R ⊕ σ ⊕ ulift.{u} bool

variables (σ R : Type u)
/-- A function used to prove theorems about the cardinality of `mv_polynomial σ R`.
  The type ``W_type (arity σ R)` has a constant for every element of `R` and `σ` and two binary
  functions. -/
private def arity : mv_polynomial_fun σ R → Type u
| (sum.inl _)              := pempty
| (sum.inr (sum.inl _))    := pempty
| (sum.inr (sum.inr ⟨ff⟩)) := ulift bool
| (sum.inr (sum.inr ⟨tt⟩)) := ulift bool

private def arity_fintype (x : mv_polynomial_fun σ R) : fintype (arity σ R x) :=
by rcases x with x | x | ⟨_ | _⟩; dsimp [arity]; apply_instance

local attribute [instance] arity_fintype

variables {σ R}

variables [comm_semiring R]

/-- The surjection from `W_type (arity σ R)` into `mv_polynomial σ R`. -/
private noncomputable def to_mv_polynomial :
  W_type (arity σ R) → mv_polynomial σ R
| ⟨sum.inl r, _⟩              := mv_polynomial.C r
| ⟨sum.inr (sum.inl i), _⟩    := mv_polynomial.X i
| ⟨sum.inr (sum.inr ⟨ff⟩), f⟩ :=
  to_mv_polynomial (f (ulift.up tt)) * to_mv_polynomial (f (ulift.up ff))
| ⟨sum.inr (sum.inr ⟨tt⟩), f⟩ :=
  to_mv_polynomial (f (ulift.up tt)) + to_mv_polynomial (f (ulift.up ff))

private lemma to_mv_polynomial_surjective : function.surjective (@to_mv_polynomial σ R _) :=
begin
  intro p,
  induction p using mv_polynomial.induction_on with x p₁ p₂ ih₁ ih₂ p i ih,
  { exact ⟨W_type.mk (sum.inl x) pempty.elim, rfl⟩ },
  { rcases ih₁ with ⟨w₁, rfl⟩,
    rcases ih₂ with ⟨w₂, rfl⟩,
    exact ⟨W_type.mk (sum.inr (sum.inr ⟨tt⟩)) (λ x, cond x.down w₁ w₂),
      by simp [to_mv_polynomial]⟩ },
  { rcases ih with ⟨w, rfl⟩,
    exact ⟨W_type.mk (sum.inr (sum.inr ⟨ff⟩)) (λ x, cond x.down w (W_type.mk
      (sum.inr (sum.inl i)) pempty.elim)), by simp [to_mv_polynomial]⟩ }
end

private lemma cardinal_mv_polynomial_fun_le : #(mv_polynomial_fun σ R) ≤ max (max (#R) (#σ)) ω :=
calc #(mv_polynomial_fun σ R) = #R + #σ + #(ulift bool) :
  by dsimp [mv_polynomial_fun]; simp only [← add_def, add_assoc]
... ≤ max (max (#R + #σ) (#(ulift bool))) ω : add_le_max _ _
... ≤ max (max (max (max (#R) (#σ)) ω) (#(ulift bool))) ω :
  max_le_max (max_le_max (add_le_max _ _) (le_refl _)) (le_refl _)
... ≤ _ : begin
  have : #(ulift.{u} bool) ≤ ω,
    from le_of_lt (lt_omega_iff_fintype.2 ⟨infer_instance⟩),
  simp only [max_comm omega.{u}, max_assoc, max_left_comm omega.{u}, max_self, max_eq_left this],
end

namespace mv_polynomial

/-- The cardinality of the multivariate polynomial ring, `mv_polynomial σ R` is at most the maximum
of `#R`, `#σ` and `ω` -/
lemma cardinal_mk_le_max {σ R : Type u} [comm_semiring R] :
  #(mv_polynomial σ R) ≤ max (max (#R) (#σ)) ω :=
calc #(mv_polynomial σ R) ≤ #(W_type (arity σ R)) :
  cardinal.mk_le_of_surjective to_mv_polynomial_surjective
... ≤ max (#(mv_polynomial_fun σ R)) ω : W_type.cardinal_mk_le_max_omega_of_fintype
... ≤ _ : max_le_max cardinal_mv_polynomial_fun_le (le_refl _)
... ≤ _ : by simp only [max_assoc, max_self]

end mv_polynomial
