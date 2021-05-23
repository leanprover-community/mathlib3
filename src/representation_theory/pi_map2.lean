/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import representation_theory.pi_map

universes u v w
open_locale direct_sum classical big_operators
open classical linear_map
noncomputable theory
/-!
# Simple Modules



-/

def submodule.prod_equiv_of_set_independent
  {R : Type v} [ring R] [nontrivial R] {M : Type w} [add_comm_group M] [module R M]
  (S : set (submodule R M)) (h : complete_lattice.set_independent S) :
  (⨁ m : S, m) ≃ₗ[R] (Sup S : submodule R M) :=
(submodule.prod_equiv_of_independent (λ m : S, m.val)
  ((complete_lattice.set_independent_iff S).mp h)).trans (dumb_map Sup_eq_supr'.symm)

def is_decomposition.equiv'
  {R : Type v} [ring R] [nontrivial R] {M : Type w} [add_comm_group M] [module R M]
  (S : set (submodule R M)) (h : complete_lattice.set_independent S) (hSup : Sup S = ⊤) :
  (⨁ m : S, m) ≃ₗ[R] M :=
(submodule.prod_equiv_of_set_independent S h).trans ((dumb_map hSup).trans (submodule.top_equiv R M))
