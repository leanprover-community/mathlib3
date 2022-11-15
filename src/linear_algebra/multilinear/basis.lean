/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import linear_algebra.basis
import linear_algebra.multilinear.basic

/-!
# Multilinear maps in relation to bases.

This file proves lemmas about the action of multilinear maps on basis vectors.

## TODO

 * Refactor the proofs in terms of bases of tensor products, once there is an equivalent of
   `basis.tensor_product` for `pi_tensor_product`.

-/

open multilinear_map

variables {R : Type*} {ι : Type*} {n : ℕ} {M : fin n → Type*} {M₂ : Type*} {M₃ : Type*}
variables [comm_semiring R] [add_comm_monoid M₂] [add_comm_monoid M₃] [∀i, add_comm_monoid (M i)]
variables [∀i, module R (M i)] [module R M₂] [module R M₃]

/-- Two multilinear maps indexed by `fin n` are equal if they are equal when all arguments are
basis vectors. -/
lemma basis.ext_multilinear_fin {f g : multilinear_map R M M₂} {ι₁ : fin n → Type*}
  (e : Π i, basis (ι₁ i) R (M i)) (h : ∀ (v : Π i, ι₁ i), f (λ i, e i (v i)) = g (λ i, e i (v i))) :
  f = g :=
begin
  unfreezingI { induction n with m hm },
  { ext x,
    convert h fin_zero_elim },
  { apply function.left_inverse.injective uncurry_curry_left,
    refine basis.ext (e 0) _,
    intro i,
    apply hm (fin.tail e),
    intro j,
    convert h (fin.cons i j),
    iterate 2
    { rw curry_left_apply,
      congr' 1 with x,
      refine fin.cases rfl (λ x, _) x,
      dsimp [fin.tail],
      rw [fin.cons_succ, fin.cons_succ], } }
end

/-- Two multilinear maps indexed by a `fintype` are equal if they are equal when all arguments
are basis vectors. Unlike `basis.ext_multilinear_fin`, this only uses a single basis; a
dependently-typed version would still be true, but the proof would need a dependently-typed
version of `dom_dom_congr`. -/
lemma basis.ext_multilinear [decidable_eq ι] [finite ι] {f g : multilinear_map R (λ i : ι, M₂) M₃}
  {ι₁ : Type*} (e : basis ι₁ R M₂) (h : ∀ v : ι → ι₁, f (λ i, e (v i)) = g (λ i, e (v i))) :
  f = g :=
by { casesI nonempty_fintype ι, exact (dom_dom_congr_eq_iff (fintype.equiv_fin ι) f g).mp
    (basis.ext_multilinear_fin (λ i, e) $ λ i, h (i ∘ _)) }
