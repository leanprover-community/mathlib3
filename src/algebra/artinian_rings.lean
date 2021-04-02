/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/

import ring_theory.ideal.operations
import linear_algebra.finite_dimensional
import order.order_iso_nat

variables {R : Type*} {M : Type*} [semiring R] [add_comm_monoid M] [semimodule R M]

class is_artinian_module (R M) [semiring R] [add_comm_monoid M] [semimodule R M] : Prop :=
(artinian : well_founded ((<) : submodule R M → submodule R M → Prop))

class is_artinian (R) [semiring R] : Prop :=
(artinian : (is_artinian_module R R))

-- define the length of a module

-- show the length of a module is ≤ number of generators
--https://stacks.math.columbia.edu/tag/02LZ

-- given a ring map R → S, construct a map of complete lattices submodules S M → submodules R M
-- deduce https://stacks.math.columbia.edu/tag/00IX

--is_sup_closed_compact.well_founded
lemma is_artinian_of_finite_dimensional (k : Type*) [field k]
  [vector_space k R] [finite_dimensional k R] : is_artinian_module R R :=
begin
--  fconstructor,
  let order_nat := ((>) : ℕ → ℕ → Prop),
  let order_mod := ((<) : submodule R R → submodule R R → Prop),
  have : ¬ nonempty (order_nat ↪r order_mod) :=
  begin
    intro hyp,
    let s := classical.choice hyp,

    sorry,
  end,
end

lemma finitely_many_maximal_ideals_of_artinian [is_artinian R] :
  true -- there are finitely many maximal ideals
:=
begin
end

-- construct a sequence of powers of ideals
lemma radical_nilpotent [is_artinian R]
