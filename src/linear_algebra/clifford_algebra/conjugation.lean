/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.basic
import algebra.module.opposites

/-!
# Conjugations

This file defines the grade reversal and grade involution functions on multivectors, `reverse` and
`involute`.
Together, these operations compose to form the "Clifford conjugate", hence the name of this file.

https://en.wikipedia.org/wiki/Clifford_algebra#Antiautomorphisms

## Main definitions

* `clifford_algebra.involute`: the grade involution, negating each basis vector
* `clifford_algebra.reverse`: the grade reversion, reversing the order of a product of vectors

## Main statements

* `clifford_algebra.involute_involutive`
* `clifford_algebra.reverse_involutive`
* `clifford_algebra.reverse_involute_commute`
-/

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {Q : quadratic_form R M}

namespace clifford_algebra

section involute

/-- Grade involution, inverting the sign of each basis vector. -/
def involute : clifford_algebra Q →ₐ[R] clifford_algebra Q :=
clifford_algebra.lift Q ⟨-(ι Q), λ m, by simp⟩

@[simp] lemma involute_ι (m : M) : involute (ι Q m) = -ι Q m :=
lift_ι_apply _ _ m

@[simp] lemma involute_comp_involute : involute.comp involute = alg_hom.id R (clifford_algebra Q) :=
by { ext, simp }

lemma involute_involutive : function.involutive (involute : _ → clifford_algebra Q) :=
alg_hom.congr_fun involute_comp_involute

@[simp] lemma involute_involute : ∀ a : clifford_algebra Q, involute (involute a) = a :=
involute_involutive

end involute

section reverse
open opposite

/-- Grade reversion, inverting the multiplication order of basis vectors.
Also called *transpose* in some literature. -/
def reverse : clifford_algebra Q →ₗ[R] clifford_algebra Q :=
(op_linear_equiv R).symm.to_linear_map.comp (
  clifford_algebra.lift Q ⟨(opposite.op_linear_equiv R).to_linear_map.comp (ι Q),
    λ m, unop_injective $ by simp⟩).to_linear_map

@[simp] lemma reverse_ι (m : M) : reverse (ι Q m) = ι Q m :=
by simp [reverse]

@[simp] lemma reverse.commutes (r : R) :
  reverse (algebra_map R (clifford_algebra Q) r) = algebra_map R _ r :=
by simp [reverse]

@[simp] lemma reverse.map_one : reverse (1 : clifford_algebra Q) = 1 :=
by convert reverse.commutes (1 : R); simp

@[simp] lemma reverse.map_mul (a b : clifford_algebra Q) :
  reverse (a * b) = reverse b * reverse a :=
by simp [reverse]

@[simp] lemma reverse_comp_reverse :
  reverse.comp reverse = (linear_map.id : _ →ₗ[R] clifford_algebra Q) :=
begin
  ext m,
  simp only [linear_map.id_apply, linear_map.comp_apply],
  induction m using clifford_algebra.induction,
  -- simp can close these goals, but is slow
  case h_grade0 : { rw [reverse.commutes, reverse.commutes] },
  case h_grade1 : { rw [reverse_ι, reverse_ι] },
  case h_mul : a b ha hb { rw [reverse.map_mul, reverse.map_mul, ha, hb], },
  case h_add : a b ha hb { rw [reverse.map_add, reverse.map_add, ha, hb], },
end

@[simp] lemma reverse_involutive : function.involutive (reverse : _ → clifford_algebra Q) :=
linear_map.congr_fun reverse_comp_reverse

@[simp] lemma reverse_reverse : ∀ a : clifford_algebra Q, reverse (reverse a) = a :=
reverse_involutive

lemma reverse_comp_involute :
  reverse.comp involute.to_linear_map =
    (involute.to_linear_map.comp reverse : _ →ₗ[R] clifford_algebra Q) :=
begin
  ext,
  simp only [linear_map.comp_apply, alg_hom.to_linear_map_apply],
  induction x using clifford_algebra.induction,
  case h_grade0 : { simp },
  case h_grade1 : { simp },
  case h_mul : a b ha hb { simp only [ha, hb, reverse.map_mul, alg_hom.map_mul], },
  case h_add : a b ha hb { simp only [ha, hb, reverse.map_add, alg_hom.map_add], },
end

/-- `clifford_algebra.reverse` and `clifford_algebra.inverse` commute. Note that the composition
is sometimes referred to as the "clifford conjugate". -/
lemma reverse_involute_commute : function.commute (reverse : _ → clifford_algebra Q) involute :=
linear_map.congr_fun reverse_comp_involute

lemma reverse_involute : ∀ a : clifford_algebra Q, reverse (involute a) = involute (reverse a) :=
reverse_involute_commute

end reverse

/-!
### Statements about conjugations of products of lists
-/

section list

/-- Taking the reverse of the product a list of $n$ vectors lifted via `ι` is equivalent to
taking the product of the reverse of that list. -/
lemma reverse_prod_map_ι : ∀ (l : list M), reverse (l.map $ ι Q).prod = (l.map $ ι Q).reverse.prod
| [] := by simp
| (x :: xs) := by simp [reverse_prod_map_ι xs]

/-- Taking the involute of the product a list of $n$ vectors lifted via `ι` is equivalent to
premultiplying by ${-1}^n$. -/
lemma involute_prod_map_ι : ∀ l : list M,
  involute (l.map $ ι Q).prod = ((-1 : R)^l.length) • (l.map $ ι Q).prod
| [] := by simp
| (x :: xs) := by simp [pow_add, involute_prod_map_ι xs]

end list

end clifford_algebra
