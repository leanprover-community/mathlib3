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

In this file we verify that the ring operations on `witt_vector p R`
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

-/

noncomputable theory

universes u v w u₁
open mv_polynomial
open set
open finset (range)
open finsupp (single)

open_locale big_operators

local attribute [-simp] coe_eval₂_hom
local attribute [semireducible] witt_vector

variables {p : ℕ} {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]

local notation `𝕎` := witt_vector p -- type as `\bbW`
open_locale witt

namespace witt_vector

variables {p} {R}

section map
open function
variables {α : Type*} {β : Type*}

/-- `f : α → β` induces a map from `𝕎 α` to `𝕎 β` in the obvious way. -/
def map_fun (f : α → β) : 𝕎 α → 𝕎 β := λ x, f ∘ x

lemma map_fun_injective (f : α → β) (hf : injective f) :
  injective (map_fun f : 𝕎 α → 𝕎 β) :=
λ x y h, funext $ λ n, hf $ by exact congr_fun h n

lemma map_fun_surjective (f : α → β) (hf : surjective f) :
  surjective (map_fun f : 𝕎 α → 𝕎 β) :=
λ x, ⟨λ n, classical.some $ hf $ x n,
by { funext n, dsimp [map_fun], rw classical.some_spec (hf (x n)) }⟩

variables (f : R →+* S)

/-- Auxiliary tactic for showing that `map_fun` respects the ring operations. -/
meta def witt_map : tactic unit :=
`[funext n,
  show f (aeval _ _) = aeval _ _,
  rw map_aeval,
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
  ext ⟨i, k⟩,
  fin_cases i; refl]

variable [fact p.prime]

/- We do not tag these lemmas as `@[simp]` because the will be bundled in `map` later on. -/
lemma map_fun_zero : map_fun f (0 : 𝕎 R) = 0 := by witt_map

lemma map_fun_one : map_fun f (1 : 𝕎 R) = 1 := by witt_map

lemma map_fun_add (x y : 𝕎 R) : map_fun f (x + y) = map_fun f x + map_fun f y := by witt_map

lemma map_fun_mul (x y : 𝕎 R) : map_fun f (x * y) = map_fun f x * map_fun f y := by witt_map

lemma map_fun_neg (x : 𝕎 R) : map_fun f (-x) = -map_fun f x := by witt_map

end map

end witt_vector

section tactic
setup_tactic_parser
open tactic

/-- An auxiliary tactic for proving that `ghost_component_fun` respects the ring operations. -/
meta def tactic.interactive.ghost_component (φ fn : parse parser.pexpr) : tactic unit :=
do fn ← to_expr ```(%%fn : fin _ → ℕ → R),
  `(fin %%k → _ → _) ← infer_type fn,
  to_expr ```(witt_structure_int_prop p (%%φ : mv_polynomial (fin %%k) ℤ) n) >>= note `aux none >>=
     apply_fun_to_hyp ```(aeval (function.uncurry %%fn)) none,
`[simp only [aeval_bind₁] at aux,
  simp only [ghost_component_fun_apply],
  convert aux using 1; clear aux;
  simp only [alg_hom.map_zero, alg_hom.map_one, alg_hom.map_add, alg_hom.map_mul, alg_hom.map_neg,
    aeval_X];
  simp only [aeval_eq_eval₂_hom, eval₂_hom_rename]; refl]
end tactic

namespace witt_vector

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`. This is bundled as a ring hom in `ghost_component`
once the ring structure is available. -/
private def ghost_component_fun (n : ℕ) (x : 𝕎 R) : R :=
aeval x.coeff (W_ ℤ n)

lemma ghost_component_fun_apply (n : ℕ) (x : 𝕎 R) :
  ghost_component_fun n x = aeval x.coeff (W_ ℤ n) := rfl

lemma ghost_component_fun_apply' (n : ℕ) (x : 𝕎 R) :
  ghost_component_fun n x = aeval x.coeff (W_ R n) :=
begin
  simp only [ghost_component_fun_apply, aeval_eq_eval₂_hom,
    ← map_witt_polynomial p (int.cast_ring_hom R), eval₂_hom_map_hom],
  exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl,
end

/-- Reorders the arguments of `ghost_component_fun`.
This function will be bundled as the ring homomorphism `witt_vector.ghost_map`
once the ring structure is available,
but we rely on it to set up the ring structure in the first place. -/
private def ghost_map_fun : 𝕎 R → (ℕ → R) := λ w n, ghost_component_fun n w

section p_prime
open finset mv_polynomial function set

variable {p}

/- The following lemmas are not `@[simp]` because we will bundle these functions later on. -/

lemma ghost_map_fun_apply (x : 𝕎 R) (n : ℕ) :
  ghost_map_fun x n = ghost_component_fun n x := rfl

variable [hp : fact p.prime]
include hp

lemma ghost_component_fun_zero (n : ℕ) :
  ghost_component_fun n (0 : 𝕎 R) = 0 :=
by ghost_component 0 ![]

lemma ghost_component_fun_one (n : ℕ) :
  ghost_component_fun n (1 : 𝕎 R) = 1 :=
by ghost_component 1 ![]

variable {R}

lemma ghost_component_fun_add (n : ℕ) (x y : 𝕎 R) :
  ghost_component_fun n (x + y) = ghost_component_fun n x + ghost_component_fun n y :=
by ghost_component (X 0 + X 1) ![x.coeff, y.coeff]

lemma ghost_component_fun_mul (n : ℕ) (x y : 𝕎 R) :
  ghost_component_fun n (x * y) = ghost_component_fun n x * ghost_component_fun n y :=
by ghost_component (X 0 * X 1) ![x.coeff, y.coeff]

lemma ghost_component_fun_neg (n : ℕ) (x : 𝕎 R) :
  ghost_component_fun n (-x) = - ghost_component_fun n x :=
by ghost_component (-X 0) ![x.coeff]

variables (R)

lemma ghost_map_fun.zero : ghost_map_fun (0 : 𝕎 R) = 0 :=
by { ext n, simp only [pi.zero_apply, ghost_map_fun_apply, ghost_component_fun_zero], }

lemma ghost_map_fun.one : ghost_map_fun (1 : 𝕎 R) = 1 :=
by { ext n, simp only [pi.one_apply, ghost_map_fun_apply, ghost_component_fun_one], }

variable {R}

lemma ghost_map_fun.add (x y : 𝕎 R) :
  ghost_map_fun (x + y) = ghost_map_fun x + ghost_map_fun y :=
by { ext n, simp only [ghost_component_fun_add, pi.add_apply, ghost_map_fun_apply], }

lemma ghost_map_fun.mul (x y : 𝕎 R) :
  ghost_map_fun (x * y) = ghost_map_fun x * ghost_map_fun y :=
by { ext n, simp only [ghost_component_fun_mul, pi.mul_apply, ghost_map_fun_apply], }

lemma ghost_map_fun.neg (x : 𝕎 R) :
  ghost_map_fun (-x) = - ghost_map_fun x :=
by { ext n, simp only [ghost_component_fun_neg, pi.neg_apply, ghost_map_fun_apply], }

end p_prime

variables (p) (R)

/-- The bijection between `𝕎 R` and `ℕ → R`,
under the assumption that `p` is invertible in `R`. -/
def ghost_map_fun.equiv_of_invertible [invertible (p : R)] :
  𝕎 R ≃ (ℕ → R) :=
{ to_fun := ghost_map_fun,
  inv_fun := λ x, mk p $ λ n, aeval x (X_in_terms_of_W p R n),
  left_inv :=
  begin
    intro x,
    ext n,
    have := bind₁_witt_polynomial_X_in_terms_of_W p R n,
    apply_fun (aeval x.coeff) at this,
    simpa only [aeval_bind₁, aeval_X, ghost_map_fun, ghost_component_fun, aeval_witt_polynomial]
  end,
  right_inv :=
  begin
    intro x,
    ext n,
    have := bind₁_X_in_terms_of_W_witt_polynomial p R n,
    apply_fun (aeval x) at this,
    simpa only [aeval_bind₁, aeval_X, ghost_map_fun, ghost_component_fun, aeval_witt_polynomial]
  end }

lemma ghost_map_fun_eq [invertible (p : R)] :
  (ghost_map_fun : 𝕎 R → ℕ → R) = ghost_map_fun.equiv_of_invertible p R :=
rfl

lemma ghost_map_fun.bijective_of_invertible [invertible (p : R)] :
  function.bijective (ghost_map_fun : 𝕎 R → ℕ → R) :=
by { rw ghost_map_fun_eq, exact (ghost_map_fun.equiv_of_invertible p R).bijective }

local attribute [instance] mv_polynomial.invertible_coe_nat

variable (R)

variable [hp : fact p.prime]
include hp

private def comm_ring_aux₁ : comm_ring (𝕎 (mv_polynomial R ℚ)) :=
function.injective.comm_ring (ghost_map_fun)
  (ghost_map_fun.bijective_of_invertible p (mv_polynomial R ℚ)).1
  (ghost_map_fun.zero _) (ghost_map_fun.one _)
  (ghost_map_fun.add) (ghost_map_fun.mul) (ghost_map_fun.neg)

local attribute [instance] comm_ring_aux₁

private def comm_ring_aux₂ : comm_ring (𝕎 (mv_polynomial R ℤ)) :=
function.injective.comm_ring (map_fun $ mv_polynomial.map (int.cast_ring_hom ℚ))
  (map_fun_injective _ $ mv_polynomial.map_injective _ int.cast_injective)
  (map_fun_zero _) (map_fun_one _) (map_fun_add _) (map_fun_mul _) (map_fun_neg _)

local attribute [instance] comm_ring_aux₂

/-- The commutative ring structure on `𝕎 R`. -/
instance : comm_ring (𝕎 R) :=
function.surjective.comm_ring
  (map_fun $ mv_polynomial.counit _) (map_fun_surjective _ $ counit_surjective _)
  (map_fun_zero _) (map_fun_one _) (map_fun_add _) (map_fun_mul _) (map_fun_neg _)

variables {p R}

section map
open function

/-- `witt_vector.map f` is the ring homomorphism `𝕎 R →+* 𝕎 S` naturally induced
by a ring homomorphism `f : R →+* S`. It acts coefficientwise. -/
def map (f : R →+* S) : 𝕎 R →+* 𝕎 S :=
{ to_fun := map_fun f,
  map_zero' := map_fun_zero f,
  map_one' := map_fun_one f,
  map_add' := map_fun_add f,
  map_mul' := map_fun_mul f }

lemma map_injective (f : R →+* S) (hf : injective f) :
  injective (map f : 𝕎 R → 𝕎 S) :=
map_fun_injective f hf

lemma map_surjective (f : R →+* S) (hf : surjective f) :
  surjective (map f : 𝕎 R → 𝕎 S) :=
map_fun_surjective f hf

@[simp] lemma map_coeff (f : R →+* S) (x : 𝕎 R) (n : ℕ) :
  (map f x).coeff n = f (x.coeff n) := rfl

end map

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`. -/
def ghost_component (n : ℕ) : 𝕎 R →+* R :=
{ to_fun := ghost_component_fun n,
  map_zero' := ghost_component_fun_zero n,
  map_one' := ghost_component_fun_one n,
  map_add' := ghost_component_fun_add n,
  map_mul' := ghost_component_fun_mul n }

lemma ghost_component_apply (n : ℕ) (x : 𝕎 R) :
  ghost_component n x = aeval x.coeff (W_ ℤ n) := rfl

/-- `witt_vector.ghost_map` is a ring homomorphism that maps each Witt vector
to the sequence of its ghost components. -/
def ghost_map : 𝕎 R →+* ℕ → R :=
{ to_fun := ghost_map_fun,
  map_zero' := ghost_map_fun.zero R,
  map_one' := ghost_map_fun.one R,
  map_add' := ghost_map_fun.add,
  map_mul' := ghost_map_fun.mul }

@[simp] lemma ghost_map_apply (x : 𝕎 R) (n : ℕ) :
  ghost_map x n = ghost_component n x := rfl

variables (p R)

/-- `witt_vector.ghost_map` is a ring isomorphism when `p` is invertible in `R`. -/
def ghost_equiv [invertible (p : R)] : 𝕎 R ≃+* (ℕ → R) :=
{ inv_fun := (ghost_map_fun.equiv_of_invertible p R).inv_fun,
  left_inv :=
  begin
    dsimp [ghost_map], rw [ghost_map_fun_eq],
    exact (ghost_map_fun.equiv_of_invertible p R).left_inv
  end,
  right_inv :=
  begin
    dsimp [ghost_map], rw [ghost_map_fun_eq],
    exact (ghost_map_fun.equiv_of_invertible p R).right_inv
  end,
  .. (ghost_map : 𝕎 R →+* (ℕ → R)) }

lemma ghost_map.bijective_of_invertible [invertible (p : R)] :
  function.bijective (ghost_map : 𝕎 R → ℕ → R) :=
ghost_map_fun.bijective_of_invertible p R

end witt_vector

attribute [irreducible] witt_vector
