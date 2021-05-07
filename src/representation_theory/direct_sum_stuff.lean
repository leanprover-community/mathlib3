import representation_theory.main2
import representation_theory.pi_map
import linear_algebra.direct_sum_module

open_locale direct_sum classical big_operators direct_sum
open classical linear_map finite_dimensional
noncomputable theory
/-!
# Simple Modules

-/

universes u v w

variables (R : Type u) [ring R] (M : Type v) [add_comm_group M] [module R M] [is_semisimple_module R M]

def direct_sum.of_set (N : Type w) [add_comm_monoid N] [module R N] (S : set (submodule R N)) :=
  ⨁ m : S, m

#print direct_sum.of_set

lemma is_internal_of_semisimple : direct_sum.submodule_is_internal
