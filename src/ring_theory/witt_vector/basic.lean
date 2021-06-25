/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import data.mv_polynomial.counit
import data.mv_polynomial.invertible
import ring_theory.witt_vector.defs

/-!
# Witt vectors

This file verifies that the ring operations on `witt_vector p R`
satisfy the axioms of a commutative ring.

## Main definitions

* `witt_vector.map`: lifts a ring homomorphism `R →+* S` to a ring homomorphism `𝕎 R →+* 𝕎 S`.
* `witt_vector.ghost_component n x`: evaluates the `n`th Witt polynomial
  on the first `n` coefficients of `x`, producing a value in `R`.
  This is a ring homomorphism.
* `witt_vector.ghost_map`: a ring homomorphism `𝕎 R →+* (ℕ → R)`, obtained by packaging
  all the ghost components together.
  If `p` is invertible in `R`, then the ghost map is an equivalence,
  which we use to define the ring operations on `𝕎 R`.
* `witt_vector.comm_ring`: the ring structure induced by the ghost components.

## Notation

We use notation `𝕎 R`, entered `\bbW`, for the Witt vectors over `R`.

## Implementation details

As we prove that the ghost components respect the ring operations, we face a number of repetitive
proofs. To avoid duplicating code we factor these proofs into a custom tactic, only slightly more
powerful than a tactic macro. This tactic is not particularly useful outside of its applications
in this file.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]

-/

noncomputable theory

open mv_polynomial function

open_locale big_operators

variables {p : ℕ} {R S T : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S] [comm_ring T]
variables {α : Type*} {β : Type*}

local notation `𝕎` := witt_vector p -- type as `\bbW`
open_locale witt

namespace witt_vector

/-- `f : α → β` induces a map from `𝕎 α` to `𝕎 β` by applying `f` componentwise.
If `f` is a ring homomorphism, then so is `f`, see `witt_vector.map f`. -/
def map_fun (f : α → β) : 𝕎 α → 𝕎 β :=
λ x, mk _ (f ∘ x.coeff)

namespace map_fun

lemma injective (f : α → β) (hf : injective f) : injective (map_fun f : 𝕎 α → 𝕎 β) :=
λ x y h, ext $ λ n, hf (congr_arg (λ x, coeff x n) h : _)

lemma surjective (f : α → β) (hf : surjective f) : surjective (map_fun f : 𝕎 α → 𝕎 β) :=
λ x, ⟨mk _ (λ n, classical.some $ hf $ x.coeff n),
by { ext n, dsimp [map_fun], rw classical.some_spec (hf (x.coeff n)) }⟩

variables (f : R →+* S) (x y : 𝕎 R)

/-- Auxiliary tactic for showing that `map_fun` respects the ring operations. -/
meta def map_fun_tac : tactic unit :=
`[ext n,
  show f (aeval _ _) = aeval _ _,
  rw map_aeval,
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
  ext ⟨i, k⟩,
  fin_cases i; refl]

include hp

/- We do not tag these lemmas as `@[simp]` because they will be bundled in `map` later on. -/

lemma zero : map_fun f (0 : 𝕎 R) = 0 := by map_fun_tac

lemma one : map_fun f (1 : 𝕎 R) = 1 := by map_fun_tac

lemma add : map_fun f (x + y) = map_fun f x + map_fun f y := by map_fun_tac

lemma sub : map_fun f (x - y) = map_fun f x - map_fun f y := by map_fun_tac

lemma mul : map_fun f (x * y) = map_fun f x * map_fun f y := by map_fun_tac

lemma neg : map_fun f (-x) = -map_fun f x := by map_fun_tac

end map_fun

end witt_vector

section tactic
setup_tactic_parser
open tactic

/-- An auxiliary tactic for proving that `ghost_fun` respects the ring operations. -/
meta def tactic.interactive.ghost_fun_tac (φ fn : parse parser.pexpr) : tactic unit := do
fn ← to_expr ```(%%fn : fin _ → ℕ → R),
`(fin %%k → _ → _) ← infer_type fn,
`[ext n],
`[dunfold
  witt_vector.has_zero witt_zero
  witt_vector.has_one witt_one
  witt_vector.has_neg witt_neg
  witt_vector.has_mul witt_mul
  witt_vector.has_sub witt_sub
  witt_vector.has_add witt_add
  ],
to_expr ```(congr_fun (congr_arg (@peval R _ %%k) (witt_structure_int_prop p %%φ n)) %%fn) >>=
  note `this none,
`[simpa [ghost_fun, aeval_rename, aeval_bind₁, (∘), uncurry, peval, eval] using this]

end tactic

namespace witt_vector

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`.
This function will be bundled as the ring homomorphism `witt_vector.ghost_map`
once the ring structure is available,
but we rely on it to set up the ring structure in the first place. -/
private def ghost_fun : 𝕎 R → (ℕ → R) := λ x n, aeval x.coeff (W_ ℤ n)

section ghost_fun
include hp

/- The following lemmas are not `@[simp]` because they will be bundled in `ghost_map` later on. -/

variables (x y : 𝕎 R)

omit hp
local attribute [simp]
lemma matrix_vec_empty_coeff {R} (i j) :
  @coeff p R (matrix.vec_empty i) j = (matrix.vec_empty i : ℕ → R) j :=
by rcases i with ⟨_ | _ | _ | _ | i_val, ⟨⟩⟩
include hp

private lemma ghost_fun_zero : ghost_fun (0 : 𝕎 R) = 0 := by ghost_fun_tac 0 ![]

private lemma ghost_fun_one : ghost_fun (1 : 𝕎 R) = 1 := by ghost_fun_tac 1 ![]

private lemma ghost_fun_add : ghost_fun (x + y) = ghost_fun x + ghost_fun y :=
by ghost_fun_tac (X 0 + X 1) ![x.coeff, y.coeff]

private lemma ghost_fun_sub : ghost_fun (x - y) = ghost_fun x - ghost_fun y :=
by ghost_fun_tac (X 0 - X 1) ![x.coeff, y.coeff]

private lemma ghost_fun_mul : ghost_fun (x * y) = ghost_fun x * ghost_fun y :=
by ghost_fun_tac (X 0 * X 1) ![x.coeff, y.coeff]

private lemma ghost_fun_neg : ghost_fun (-x) = - ghost_fun x :=
by ghost_fun_tac (-X 0) ![x.coeff]

end ghost_fun

variables (p) (R)

/-- The bijection between `𝕎 R` and `ℕ → R`, under the assumption that `p` is invertible in `R`.
In `witt_vector.ghost_equiv` we upgrade this to an isomorphism of rings. -/
private def ghost_equiv' [invertible (p : R)] : 𝕎 R ≃ (ℕ → R) :=
{ to_fun := ghost_fun,
  inv_fun := λ x, mk p $ λ n, aeval x (X_in_terms_of_W p R n),
  left_inv :=
  begin
    intro x,
    ext n,
    have := bind₁_witt_polynomial_X_in_terms_of_W p R n,
    apply_fun (aeval x.coeff) at this,
    simpa only [aeval_bind₁, aeval_X, ghost_fun, aeval_witt_polynomial]
  end,
  right_inv :=
  begin
    intro x,
    ext n,
    have := bind₁_X_in_terms_of_W_witt_polynomial p R n,
    apply_fun (aeval x) at this,
    simpa only [aeval_bind₁, aeval_X, ghost_fun, aeval_witt_polynomial]
  end }

include hp

local attribute [instance]
private def comm_ring_aux₁ : comm_ring (𝕎 (mv_polynomial R ℚ)) :=
(ghost_equiv' p (mv_polynomial R ℚ)).injective.comm_ring (ghost_fun)
  ghost_fun_zero ghost_fun_one ghost_fun_add ghost_fun_mul ghost_fun_neg ghost_fun_sub

local attribute [instance]
private def comm_ring_aux₂ : comm_ring (𝕎 (mv_polynomial R ℤ)) :=
(map_fun.injective _ $ map_injective (int.cast_ring_hom ℚ) int.cast_injective).comm_ring _
  (map_fun.zero _) (map_fun.one _) (map_fun.add _) (map_fun.mul _) (map_fun.neg _) (map_fun.sub _)

/-- The commutative ring structure on `𝕎 R`. -/
instance : comm_ring (𝕎 R) :=
(map_fun.surjective _ $ counit_surjective _).comm_ring (map_fun $ mv_polynomial.counit _)
  (map_fun.zero _) (map_fun.one _) (map_fun.add _) (map_fun.mul _) (map_fun.neg _) (map_fun.sub _)

variables {p R}

/-- `witt_vector.map f` is the ring homomorphism `𝕎 R →+* 𝕎 S` naturally induced
by a ring homomorphism `f : R →+* S`. It acts coefficientwise. -/
def map (f : R →+* S) : 𝕎 R →+* 𝕎 S :=
{ to_fun := map_fun f,
  map_zero' := map_fun.zero f,
  map_one' := map_fun.one f,
  map_add' := map_fun.add f,
  map_mul' := map_fun.mul f }

lemma map_injective (f : R →+* S) (hf : injective f) : injective (map f : 𝕎 R → 𝕎 S) :=
map_fun.injective f hf

lemma map_surjective (f : R →+* S) (hf : surjective f) : surjective (map f : 𝕎 R → 𝕎 S) :=
map_fun.surjective f hf

@[simp] lemma map_coeff (f : R →+* S) (x : 𝕎 R) (n : ℕ) :
  (map f x).coeff n = f (x.coeff n) := rfl

/-- `witt_vector.ghost_map` is a ring homomorphism that maps each Witt vector
to the sequence of its ghost components. -/
def ghost_map : 𝕎 R →+* ℕ → R :=
{ to_fun := ghost_fun,
  map_zero' := ghost_fun_zero,
  map_one' := ghost_fun_one,
  map_add' := ghost_fun_add,
  map_mul' := ghost_fun_mul }

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`. -/
def ghost_component (n : ℕ) : 𝕎 R →+* R := (pi.eval_ring_hom _ n).comp ghost_map

lemma ghost_component_apply (n : ℕ) (x : 𝕎 R) : ghost_component n x = aeval x.coeff (W_ ℤ n) := rfl

@[simp] lemma ghost_map_apply (x : 𝕎 R) (n : ℕ) : ghost_map x n = ghost_component n x := rfl

variables (p R) [invertible (p : R)]

/-- `witt_vector.ghost_map` is a ring isomorphism when `p` is invertible in `R`. -/
def ghost_equiv : 𝕎 R ≃+* (ℕ → R) :=
{ .. (ghost_map : 𝕎 R →+* (ℕ → R)), .. (ghost_equiv' p R) }

@[simp] lemma ghost_equiv_coe : (ghost_equiv p R : 𝕎 R →+* (ℕ → R)) = ghost_map := rfl

lemma ghost_map.bijective_of_invertible : function.bijective (ghost_map : 𝕎 R → ℕ → R) :=
(ghost_equiv p R).bijective

end witt_vector
