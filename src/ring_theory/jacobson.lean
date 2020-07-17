/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.mv_polynomial
import ring_theory.ideals
import ring_theory.ideal_operations

/-!
# Jacobson rings

The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its jacobson radical

Any ring satisfying any of these equivalent conditions is said to be Jacobson.

## Main definitions

Let `R` be a commutative ring. Jacobson Rings are defined using the first of the above conditions

* `is_jacobson R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.radical = I` implies `I.jacobson = I`.

## Main statements

* `is_jacobson_iff_prime_eq` is the equivalence between conditions 1 and 3 above.

* `is_jacobson_iff_Inf_maximal` is the equivalence between conditions 1 and 2 above.

## Tags

Jacobson, Jacobson Ring

-/

universes u v

namespace ideal
section is_jacobson
variables {R : Type u} [comm_ring R] {I : ideal R}

/-- Definition of jacobson rings in terms of radical ideals -/
@[class] def is_jacobson (R : Type u) [comm_ring R] :=
    ∀ (I : ideal R), I.radical = I → I.jacobson = I

/-- Defining jacobson rings in terms of prime ideals is completely equivalent -/
lemma is_jacobson_iff_prime_eq : is_jacobson R ↔ ∀ P : ideal R, is_prime P → P.jacobson = P :=
begin
  split,
  { exact λ h I hI, h I (is_prime.radical hI) },
  { refine λ h I hI, le_antisymm (λ x hx, _) (λ x hx, mem_Inf.mpr (λ _ hJ, hJ.left hx)),
    erw mem_Inf at hx,
    rw [← hI, radical_eq_Inf I, mem_Inf],
    intros P hP,
    rw set.mem_set_of_eq at hP,
    erw [← h P hP.right, mem_Inf],
    exact λ J hJ, hx ⟨le_trans hP.left hJ.left, hJ.right⟩ }
end

/-- I equals its jacobson iff it can be written as an Inf of maximal ideals -/
lemma is_jacobson_iff_Inf_maximal : is_jacobson R ↔
    ∀ {I : ideal R}, I.radical = I → ∃ M ⊆ {J : ideal R | J.is_maximal ∨ J = ⊤}, I = Inf M :=
begin
  use λ H I h, ⟨{J : ideal R | I ≤ J ∧ J.is_maximal}, ⟨λ _ hJ, or.inl hJ.right, eq.symm (H _ h)⟩⟩,
  intros H I hI,
  rcases H hI with ⟨M, hM, hInf⟩,
  refine le_antisymm _ le_jacobson,
  intros x hx,
  rw hInf,
  erw mem_Inf at ⊢ hx,
  intros I hI,
  cases hM hI with is_max is_top,
  { refine hx ⟨le_Inf_iff.1 (le_of_eq hInf) I hI, is_max⟩ },
  { rw is_top, exact submodule.mem_top }
end

lemma radical_eq_jacobson (H : is_jacobson R) (I : ideal R) : I.radical = I.jacobson :=
le_antisymm (le_Inf (λ J ⟨hJ, hJ_max⟩, (is_prime.radical_le_iff hJ_max.is_prime).mpr hJ))
            ((H I.radical (radical_idem I)) ▸ (jacobson_mono le_radical))

/-- Fields have only two ideals, and the condition holds for both of them -/
theorem is_jacobson_field {K : Type u} [field K] : is_jacobson K :=
λ I hI, or.rec_on (eq_bot_or_top I)
(λ h, le_antisymm
  (Inf_le ⟨le_of_eq rfl, (eq.symm h) ▸ bot_is_maximal⟩)
  ((eq.symm h) ▸ bot_le))
(λ h, by rw [h, jacobson_eq_top_iff])

-- TODO: Can this be rewritten as a special case of a statement about images?
theorem is_jacobson_iso {S : Type u} [comm_ring S] (e : S ≃+* R)
  : is_jacobson S ↔ is_jacobson R :=
begin
  split,
  swap,
  replace e := e.symm, -- After this swap both proofs are identical
  all_goals {
    let iso := order_iso_of_bijective e.to_ring_hom (equiv.bijective e.to_equiv),
    exact λ H I hI, iso.injective ((comap_jacobson e).trans (H _ (by rw [← comap_radical, hI]))),
  }
end

theorem is_jacobson_quotient [H : is_jacobson R] : is_jacobson (quotient I) :=
begin
  rw is_jacobson_iff_Inf_maximal,
  intros p hp,
  use quotient.map_mk I '' {J : ideal R | quotient.comap_mk I p ≤ J ∧ J.is_maximal},
  use λ j ⟨J, hJ, hmap⟩, hmap ▸ or.symm (quotient.map_eq_top_or_is_maximal_of_is_maximal hJ.right),
  have : p = quotient.map_mk I ((quotient.comap_mk I p).jacobson),
  from (H (quotient.comap_mk I p) (by rw [comap_mk_eq_comap, ← comap_radical, hp])).symm
    ▸ (quotient.map_mk_comap_mk_left_inverse p).symm,
  exact eq.trans this (quotient.map_mk_Inf (λ J ⟨hJ, _⟩, le_trans (quotient.le_comap_mk) hJ))
end

-- lemma is_jacobson_polynomial (H : is_jacobson R) : is_jacobson (polynomial R) := sorry

-- lemma is_jacobson_mv_polynomial (H : is_jacobson R) (n : ℕ) :
--   is_jacobson (mv_polynomial (fin n) R) :=
-- nat.rec_on n
--   ((is_jacobson_iso
--     ((mv_polynomial.ring_equiv_of_equiv R (equiv.equiv_pempty $ fin.elim0)).trans
--     (mv_polynomial.pempty_ring_equiv R))).mpr H)
--   (λ n hn, (is_jacobson_iso (mv_polynomial.fin_succ_equiv R n)).2 (ideal.is_jacobson_polynomial hn))

end is_jacobson

end ideal
