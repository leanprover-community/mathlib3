/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.grading
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
* `clifford_algebra.involute_mem_even_odd_iff`
* `clifford_algebra.reverse_mem_even_odd_iff`

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

/-- `clifford_algebra.involute` as an `alg_equiv`. -/
@[simps] def involute_equiv : clifford_algebra Q ≃ₐ[R] clifford_algebra Q :=
alg_equiv.of_alg_hom involute involute
  (alg_hom.ext $ involute_involute) (alg_hom.ext $ involute_involute)

end involute

section reverse
open mul_opposite

/-- Grade reversion, inverting the multiplication order of basis vectors.
Also called *transpose* in some literature. -/
def reverse : clifford_algebra Q →ₗ[R] clifford_algebra Q :=
(op_linear_equiv R).symm.to_linear_map.comp (
  clifford_algebra.lift Q ⟨(mul_opposite.op_linear_equiv R).to_linear_map.comp (ι Q),
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

/-- `clifford_algebra.reverse` as a `linear_equiv`. -/
@[simps] def reverse_equiv : clifford_algebra Q ≃ₗ[R] clifford_algebra Q :=
linear_equiv.of_involutive reverse reverse_involutive

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

/-!
### Statements about `submodule.map` and `submodule.comap`
-/

section submodule

variables (Q)

section involute

lemma submodule_map_involute_eq_comap (p : submodule R (clifford_algebra Q)) :
  p.map involute.to_linear_map = p.comap involute.to_linear_map :=
(submodule.map_equiv_eq_comap_symm involute_equiv.to_linear_equiv _)

@[simp] lemma ι_range_map_involute : (ι Q).range.map involute.to_linear_map = (ι Q).range :=
(ι_range_map_lift _ _).trans (linear_map.range_neg _)

@[simp] lemma ι_range_comap_involute : (ι Q).range.comap involute.to_linear_map = (ι Q).range :=
by rw [←submodule_map_involute_eq_comap, ι_range_map_involute]

@[simp] lemma even_odd_map_involute (n : zmod 2) :
  (even_odd Q n).map involute.to_linear_map = (even_odd Q n) :=
by simp_rw [even_odd, submodule.map_supr, submodule.map_pow, ι_range_map_involute]

@[simp] lemma even_odd_comap_involute (n : zmod 2) :
  (even_odd Q n).comap involute.to_linear_map = even_odd Q n :=
by rw [←submodule_map_involute_eq_comap, even_odd_map_involute]

end involute

section reverse

lemma submodule_map_reverse_eq_comap (p : submodule R (clifford_algebra Q)) :
  p.map reverse = p.comap reverse :=
(submodule.map_equiv_eq_comap_symm (reverse_equiv : _ ≃ₗ[R] _) _)

@[simp] lemma ι_range_map_reverse : (ι Q).range.map reverse = (ι Q).range :=
begin
  rw [reverse, submodule.map_comp, ι_range_map_lift, linear_map.range_comp, ←submodule.map_comp],
  exact submodule.map_id _,
end

@[simp] lemma ι_range_comap_reverse : (ι Q).range.comap reverse = (ι Q).range :=
by rw [←submodule_map_reverse_eq_comap, ι_range_map_reverse]

/-- Like `submodule.map_mul`, but with the multiplication reversed. -/
lemma submodule_map_mul_reverse (p q : submodule R (clifford_algebra Q)) :
  (p * q).map reverse = q.map reverse * p.map reverse :=
by simp_rw [reverse, submodule.map_comp, linear_equiv.to_linear_map_eq_coe, submodule.map_mul,
  submodule.map_unop_mul]

lemma submodule_comap_mul_reverse (p q : submodule R (clifford_algebra Q)) :
  (p * q).comap reverse = q.comap reverse * p.comap reverse :=
by simp_rw [←submodule_map_reverse_eq_comap, submodule_map_mul_reverse]

/-- Like `submodule.map_pow` -/
lemma submodule_map_pow_reverse (p : submodule R (clifford_algebra Q)) (n : ℕ) :
  (p ^ n).map reverse = p.map reverse ^ n :=
by simp_rw [reverse, submodule.map_comp, linear_equiv.to_linear_map_eq_coe, submodule.map_pow,
  submodule.map_unop_pow]

lemma submodule_comap_pow_reverse  (p : submodule R (clifford_algebra Q)) (n : ℕ) :
  (p ^ n).comap reverse = p.comap reverse ^ n :=
by simp_rw [←submodule_map_reverse_eq_comap, submodule_map_pow_reverse]

@[simp] lemma even_odd_map_reverse (n : zmod 2) : (even_odd Q n).map reverse = even_odd Q n :=
by simp_rw [even_odd, submodule.map_supr, submodule_map_pow_reverse, ι_range_map_reverse]

@[simp] lemma even_odd_comap_reverse (n : zmod 2) : (even_odd Q n).comap reverse = even_odd Q n :=
by rw [←submodule_map_reverse_eq_comap, even_odd_map_reverse]

end reverse

@[simp] lemma involute_mem_even_odd_iff {x : clifford_algebra Q} {n : zmod 2} :
  involute x ∈ even_odd Q n ↔ x ∈ even_odd Q n :=
set_like.ext_iff.mp (even_odd_comap_involute Q n) x

@[simp] lemma reverse_mem_even_odd_iff {x : clifford_algebra Q} {n : zmod 2} :
  reverse x ∈ even_odd Q n ↔ x ∈ even_odd Q n :=
set_like.ext_iff.mp (even_odd_comap_reverse Q n) x

end submodule

end clifford_algebra
