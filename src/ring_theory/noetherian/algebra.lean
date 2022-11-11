/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
import algebra.algebra.subalgebra.tower
import ring_theory.noetherian.basic

/-!
# Finitely generated and Noetherian subalgebras

## Main results

 * `subalgebra.fg_bot_to_submodule`: the trivial subalgebra `⊥` is finitely generated

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel1967]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/

lemma subalgebra.fg_bot_to_submodule {R A : Type*}
  [comm_semiring R] [semiring A] [algebra R A] :
  (⊥ : subalgebra R A).to_submodule.fg :=
⟨{1}, by simp [algebra.to_submodule_bot] ⟩
