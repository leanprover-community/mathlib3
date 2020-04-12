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
1. that if R ≅ S as commutative rings, then R[X] ≅ S[X] as rings.
2. that is R ≅ S as commutative rings, and R is local, the S is local.

What do we need?

There are some issues because of bundling,
but let's ignore those for now, and just deal
with proving functoriality.
-/

noncomputable theory

@[reducible]
def Polynomial : CommRing → CommRing :=
(λ R, CommRing.of (polynomial R))

-- We want to build an instance of the (not-yet-written)
-- `iso_functorial Polynomial`.

-- How are we going to do that?
-- The only way is brute force: we're going to start at type level.

@[simp]
lemma refl_symm {α : Type*} : (equiv.refl α).symm = equiv.refl α := rfl

@[simp]
lemma polynomial.to_fun_as_coeff {α : Type*} [comm_semiring α] (p : polynomial α) (n : ℕ) :
  p.to_fun n = polynomial.coeff p n :=
begin
  refl,
end


lemma coeff_one_zero {α : Type*} [comm_semiring α] : polynomial.coeff (1 : polynomial α) 0 = (1 : α) :=
begin
  simp,
end

@[simp]
lemma zero_eq_succ_iff_false (n : ℕ) : 0 = n + 1 ↔ false := sorry

lemma coeff_one_succ {α : Type*} [comm_semiring α] (n : ℕ) : polynomial.coeff (1 : polynomial α) (n+1) = (0 : α) :=
begin
  simp,
end


-- set_option pp.all true

example {R S : CommRing.{u}} (i : R ⟶ S) (r : R) (h : r = 0) : i r = 0 :=
begin
  simp [h],
end



-- TODO make sure that if this lemma is missing, transport still mostly works.
@[simp]
lemma eq_zero_iff {R S : CommRing.{u}} (i : R ≅ S) (r : R) : i.hom r = 0 ↔ r = 0 :=
begin
  split,
  { intro h,
    replace h := congr_arg i.inv h,
    simpa using h, },
  { intro h, simp [h] }
end

-- set_option pp.all true
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
  simp, dsimp,
  simp at mem_support_to_fun,
  apply mem_support_to_fun,
end.

-- Now we need to hope that all the algebraic axioms work out!

-- set_option pp.all true
def iso_functorial.map.map_one {R S : CommRing.{u}} (i : R ≅ S) :
  iso_functorial.map.to_fun i 1 = 1 :=
begin
  dsimp [iso_functorial.map.to_fun],
  ext,
  simp,
  dsimp,
  cases n, -- hmm, could be awkward
  dsimp,
  simp,
  simp,
end

def iso_functorial.map.map_mul {R S : CommRing.{u}} (i : R ≅ S) (x y : Polynomial R) :
  iso_functorial.map.to_fun i (x * y) =
    iso_functorial.map.to_fun i x * iso_functorial.map.to_fun i y := sorry
-- etc

-- We can now put those facts together as

def iso_functorial.map {R S : CommRing} (i : R ≅ S) : Polynomial R ⟶ Polynomial S :=
{ to_fun := iso_functorial.map.to_fun i,
  map_one' := iso_functorial.map.map_one i,
  map_mul' := iso_functorial.map.map_mul i,
  map_zero' := sorry,
  map_add' := sorry, }

-- And then we need to prove `iso_functorial.map_id` and `iso_functorial.map_comp`,
-- which should be consequences of the behaviour of `transport`.
-- (Note that means "practical" rather than "logical" consequences, since `transport` is meta.)

def iso_functorial.map_id (R : CommRing) : iso_functorial.map (iso.refl R) = 𝟙 (Polynomial R) :=
begin
  ext,
  simp,
  dsimp [iso_functorial.map, iso_functorial.map.to_fun],
  simp,
  dsimp,
  simp,
end
def iso_functorial.map_comp : sorry := sorry


----

-- We want to prove `is_local_ring` is "hygienic"

set_option pp.proofs true
theorem is_local_ring_hygienic (R S : CommRing) (i : R ≅ S) (h : is_local_ring R) : is_local_ring S :=
begin
  tactic.whnf_target,
  split,

  { equiv_rw i.symm,
    simp,
    exact h.1, },
  { sorry
    --equiv_rw i.symm,  -- not there yet
    }
end

-- Okay, that didn't go so well. Let's do some work on `units` and `is_unit` first,
-- but remembering that this eventually needs to be automated!

@[reducible]
def Units : Mon → Group :=
(λ R, Group.of (units R))


@[functoriality]
lemma Mon.coe_as_forget (R : Mon.{u}) : (R : Type u) = (forget Mon.{u}).obj R := rfl

-- #print category_theory.iso.symm_hom
-- universes v
-- lemma category_theory.iso.symm_hom {C : Type u} [category.{v} C] {X Y : C} (i : X ≅ Y) : i.symm.hom = i.inv := rfl

-- again, our goal is to define an iso_functorial instance (or at least the fields thereof, for now)
def iso_functorial.map.to_fun' {R S : Mon.{u}} (i : R ≅ S) : Units R → Units S :=
begin
  intro S,
  tactic.whnf_target,

  refine_struct {..},
  { have val := units.val S,
    equiv_rw i at val,
    exact val, },
  { have inv := units.inv S,
    equiv_rw i at inv,
    exact inv, },
  { have val_inv := units.val_inv S,
    dsimp,
    apply i.symm.injective,
    simp,
    dsimp,
    simp,
    exact val_inv, },
  { have inv_val := units.inv_val S,
    dsimp,
    apply i.symm.injective,
    simp,
    dsimp,
    simp,
    exact inv_val, }
end
