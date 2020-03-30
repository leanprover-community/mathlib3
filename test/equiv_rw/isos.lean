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
import data.polynomial

universes u

set_option trace.equiv_rw_type true

open category_theory

mk_simp_attribute functoriality
"The simpset `functoriality` is used by the tactic `equiv_rw`
to write expressions explicitly as applications of functors."

@[functoriality]
lemma coe_as_forget (R : Ring.{u}) : (R : Type u) = (forget Ring.{u}).obj R := rfl

-- set_option trace.app_builder true
-- set_option pp.all true

example (R S : Ring.{u}) (i : R ≅ S) (r : R) : S :=
begin
  -- let t : R ≃ _ := by equiv_rw_type i,
  equiv_rw i at r,
  exact r,
end

example (R S : Ring.{u}) (i : R ≅ S) (s : S) : R :=
begin
  equiv_rw i,
  dsimp, -- maybe dsimp the other way afterwards?
  exact s,
end

/-
Let's set ourselves some ambitious goals.

We'd like to (easily, automatically) prove:
1. that if R ≅ S as commutative rings, then R[X] ≅ S[X] as rings.
2. that is R ≅ S as commutative rings, and R is local, the S is local.

What do we need?

There are some issues because of bundling,
but let's ignore those for now, and just deal
with proving functoriality.
-/

noncomputable theory

def Polynomial : CommRing → CommRing :=
(λ R, CommRing.of (polynomial R))

-- We want to build an instance of the (not-yet-written)
-- `iso_functorial Polynomial`.

-- How are we going to do that?
-- The only way is brute force: we're going to start at type level.

@[simp]
lemma refl_symm {α : Type*} : (equiv.refl α).symm = equiv.refl α := rfl

-- set_option pp.all true

example {R S : CommRing.{u}} (i : R ⟶ S) (r : R) (h : r = 0) : i r = 0 :=
begin
  simp [h],
  erw ring_hom.map_zero i, -- argh, why is erw required? why not just by simp?
end



-- TODO make sure that if this lemma is missing, transport still mostly works.
@[simp]
lemma eq_zero_iff {R S : CommRing.{u}} (i : R ≅ S) (r : R) : i.hom r = 0 ↔ r = 0 :=
begin
  split,
  { intro h,
    replace h := congr_arg i.inv h,
    simpa using h, },
  { intro h, simp [h], erw ring_hom.map_zero i.hom, } -- argh, why is erw required? why not by simp? -- probably related to the problem below
end




set_option pp.all true
def iso_functorial.map.to_fun {R S : CommRing.{u}} (i : R ≅ S) : Polynomial R → Polynomial S :=
begin
  intro X,
  -- This certainly doesn't work yet, but we may be reasonably close.
  -- transport X with i,
  -- Let's try to do it by hand to see how it's meant to go.

  -- dsimp [Polynomial, polynomial, add_monoid_algebra],
  tactic.whnf_target,

  refine_struct { .. } ,

  have support := finsupp.support X,
  try { equiv_rw i at support }, -- who cares, it didn't even depend on R
  exact support,

  have to_fun := finsupp.to_fun X,
  have i' := (forget CommRing).map_iso i,
  equiv_rw i' at to_fun, -- but we need this to work without us constructing i' by hand
  exact to_fun,

  have mem_support_to_fun := finsupp.mem_support_to_fun X,
  dsimp,
  intros,
  simp, dsimp, rw [eq_zero_iff], -- so close! this needs to work by simp.
  simp at mem_support_to_fun,
  apply mem_support_to_fun,
end

-- Now we need to hope that all the algebraic axioms work out!

def iso_functorial.map.map_one : sorry := sorry
def iso_functorial.map.map_mul : sorry := sorry
-- etc

-- We can now put those facts together as

def iso_functorial.map {R S : CommRing} (i : R ≅ S) : Polynomial R ⟶ Polynomial S :=
sorry

-- And then we need to prove `iso_functorial.map_id` and `iso_functorial.map_comp`,
-- which should be consequences of the behaviour of `transport`.
-- (Note that means "practical" rather than "logical" consequences, since `transport` is meta.)

def iso_functorial.map_id (R : CommRing) : iso_functorial.map (iso.refl R) = 𝟙 (Polynomial R) :=
sorry
def iso_functorial.map_comp : sorry := sorry


----

-- We want to prove `is_local_ring` is "hygienic"
#check and.imp

theorem is_local_ring_hygienic (R S : CommRing) (i : R ≅ S) (h : is_local_ring R) : is_local_ring S :=
begin
  tactic.whnf_target,
  equiv_rw i.symm,
  transport h with i,
end
