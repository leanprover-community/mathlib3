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

-/

open multilinear_map

variables {R : Type*} {ι : Type*} {n : ℕ} {M : fin n.succ → Type*} {M₂ : Type*} {M₃ : Type*}
variables [comm_semiring R] [add_comm_monoid M₂] [add_comm_monoid M₃] [∀i, add_comm_monoid (M i)]
variables [∀i, module R (M i)] [module R M₂] [module R M₃]

/-- Two multilinear maps indexed by `fin n.succ` are equal if they are equal when all arguments
are basis vectors. -/
lemma basis.ext_multilinear_fin {f g : multilinear_map R M M₂} {ι₁ : fin n.succ → Type*}
  (e : Π i, basis (ι₁ i) R (M i)) (h : ∀ v : Π i, ι₁ i, f (λ i, e i (v i)) = g (λ i, e i (v i))) :
  f = g :=
begin
  unfreezingI { induction n with m hm },
  { rw [←f.uncurry_curry_left, ←g.uncurry_curry_left],
    congr' 1,
    refine basis.ext (e 0) _,
    intro i,
    ext v,
    rw [curry_left_apply, curry_left_apply],
    convert h (fin.cons i fin_zero_elim),
    iterate 2 {
      ext x,
      obtain rfl : x = 0 := subsingleton.elim _ _,
      refl, },
  { rw [←f.uncurry_curry_left, ←g.uncurry_curry_left],
    congr' 1,
    refine basis.ext (e 0) _,
    intro i,
    replace hm := @hm _ _ _ (f.curry_left ((e 0) i)) (g.curry_left ((e 0) i)) (fin.tail ι₁)
                      (fin.tail e),
    apply hm,
    intro j,
    convert h (fin.cons i j),
    iterate 2 { {
      rw curry_left_apply,
      congr' 1 with x,
      refine fin.cases rfl (λ x, _) x,
      dsimp [fin.tail],
      rw [fin.cons_succ, fin.cons_succ], } }
end

/-- Two multilinear maps indexed by a `fintype` are equal if they are equal when all arguments
are basis vectors. Unlike `basis.ext_multilinear_fin`, this only uses a single basis; a
dependently-typed version would still be true, but the proof would need a dependently-typed
version of `dom_dom_congr`. -/
lemma basis.ext_multilinear [decidable_eq ι] [fintype ι] {f g : multilinear_map R (λ i : ι, M₂) M₃}
  {ι₁ : Type*} (e : basis ι₁ R M₂) (h : ∀ v : ι → ι₁, f (λ i, e (v i)) = g (λ i, e (v i))) :
  f = g :=
begin
  generalize' hn : fintype.card ι = n,
  let f' := f.dom_dom_congr (fintype.equiv_fin_of_card_eq hn),
  let g' := g.dom_dom_congr (fintype.equiv_fin_of_card_eq hn),
  rw ←dom_dom_congr_eq_iff (fintype.equiv_fin_of_card_eq hn),
  change f' = g',
  cases n with m hm,
  { ext x,
    haveI := fintype.card_eq_zero_iff.1 hn,
    convert h is_empty_elim,
    { rw dom_dom_congr_apply,
      congr },
    { rw dom_dom_congr_apply,
      congr } },
  { exact basis.ext_multilinear_fin (λ i : fin m.succ, e)
                                    (λ i, h (i ∘ fintype.equiv_fin_of_card_eq hn)) }
end
