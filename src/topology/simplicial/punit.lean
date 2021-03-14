/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import topology.simplicial.singular
import algebra.punit_instances
import data.fintype.card

-- noncomputable theory

universe variables u

open category_theory Top simplicial_object sSet

variables (X : Top.{u}) (R : Type u) [comm_ring R]

lemma singular_chain_complex_d_of_nonpos :
  Π (i : ℤ) (h : i ≤ 0), ((singular_chain_complex R).obj X).d i = 0
| -[1+n]  h := rfl
| 0       h := rfl
| (n+1:ℕ) h := false.elim (by { norm_cast at h, exact nat.not_succ_le_zero n h })

open_locale big_operators

lemma foobar [subsingleton ↥X]
  (α : (((sSet.free_simplicial_module R).obj
             (singular_standard_simplex.op.comp_left.obj
                (category_theory.yoneda.obj X))).graded_object 1)) :
  ⇑((∑ (i : fin (0 + 2)),
            (-1:R) ^ (i:ℕ) • simplicial_object.δ
                ((sSet.free_simplicial_module R).obj
                   (singular_standard_simplex.op.comp_left.obj
                      (category_theory.yoneda.obj X))) i)) α = 0 :=
begin
  rw [fin.sum_univ_succ, fin.sum_univ_succ, fin.sum_univ_zero],
  simp only [add_zero, fin.coe_zero, linear_map.smul_apply, one_smul, linear_map.add_apply, pow_zero],
  simp only [fin.coe_zero, fin.coe_succ, one_smul, pow_one, neg_smul],
  rw add_neg_eq_zero,
  -- dsimp [simplicial_object.δ, free_simplicial_module, Module.Free, skeletal],
  -- dsimp [functor.comp_right, functor.comp_left],
  apply finsupp.map_domain_congr,
  intros x hx,
  ext,
  apply subsingleton.elim,
end

lemma singular_chain_complex_d_one_of_unique [subsingleton X] :
  ((singular_chain_complex R).obj X).d 1 = 0 :=
begin
  ext1 α,
  dsimp [singular_chain_complex, singular, simplicial_module.graded_object_d] at *,
  show (simplicial_module.boundary _ 0 ≫ _) α = 0,
  dsimp,
  show (((sSet.free_simplicial_module R).obj (singular_standard_simplex.op.comp_left.obj
    (category_theory.yoneda.obj X))).boundary 0) α = 0,
  dsimp [simplicial_module.boundary],
  apply foobar,
end
