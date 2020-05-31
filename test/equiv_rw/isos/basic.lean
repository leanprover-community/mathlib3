/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.equiv_rw
import tactic.transport
import category_theory.functorial
import category_theory.types
import algebra.category.CommRing.basic

universes u

open category_theory

-- TODO eventually, we should move this lemma (and its analogues for all concrete categories)
-- to the files where those categories are set up.
-- While `equiv_rw` is being actively developed, I'd prefer not to do that, so as not to
-- make all the concrete categories dependent on `equiv_rw`.
-- (We probably should write a command that synthesizes all the apparatus of a concrete category!)
@[functoriality]
lemma coe_as_forget_obj (R : Ring.{u}) : (R : Type u) = (forget Ring.{u}).obj R := rfl

set_option trace.equiv_rw_type true

example (R S : Ring.{u}) (i : R ≅ S) (r : R) : S :=
begin
  equiv_rw i at r,
  exact r,
end

example (R S : Ring.{u}) (i : R ≅ S) (s : S) : R :=
begin
  equiv_rw i,
  dsimp,
  exact s,
end

/-
Let's set ourselves some ambitious goals.

We'd like to (easily, automatically) prove:
0. if R ≅ S as commutative rings, and R is nonzero, then S is nonzero.
1. if R ≅ S as commutative rings, then R[X] ≅ S[X] as rings.
2. if R ≅ S as commutative rings, and R is local, then S is local.
3. if φ : R ≅ S as commutative rings, and f : T ⟶ R is integrally closed, then f ≫ φ.hom is too.

What do we need?

There are some bundling/unbundling issues,
but let's ignore those for now,
and just deal with proving functoriality.
-/
