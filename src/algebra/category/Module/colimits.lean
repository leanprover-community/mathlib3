/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.basic
import group_theory.quotient_group
import category_theory.limits.concrete_category
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.concrete_category

/-!
# The category of R-modules has all colimits.

This file uses a "pre-automated" approach, just as for `Mon/colimits.lean`.

Note that finite colimits can already be obtained from the instance `abelian (Module R)`.

TODO:
In fact, in `Module R` there is a much nicer model of colimits as quotients
of finitely supported functions, and we really should implement this as well (or instead).
-/

universes u v

open category_theory
open category_theory.limits

variables {R : Type v} [ring R]

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.

namespace Module.colimits
/-!
We build the colimit of a diagram in `Module` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/

variables {J : Type v} [small_category J] (F : J ⥤ Module.{v} R)

/--
An inductive type representing all module expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive prequotient
-- There's always `of`
| of : Π (j : J) (x : F.obj j), prequotient
-- Then one generator for each operation
| zero : prequotient
| neg : prequotient → prequotient
| add : prequotient → prequotient → prequotient
| smul : R → prequotient → prequotient

instance : inhabited (prequotient F) := ⟨prequotient.zero⟩

open prequotient

/--
The relation on `prequotient` saying when two expressions are equal
because of the module laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive relation : prequotient F → prequotient F → Prop
-- Make it an equivalence relation:
| refl : Π (x), relation x x
| symm : Π (x y) (h : relation x y), relation y x
| trans : Π (x y z) (h : relation x y) (k : relation y z), relation x z
-- There's always a `map` relation
| map : Π (j j' : J) (f : j ⟶ j') (x : F.obj j), relation (of j' (F.map f x)) (of j x)
-- Then one relation per operation, describing the interaction with `of`
| zero : Π (j), relation (of j 0) zero
| neg : Π (j) (x : F.obj j), relation (of j (-x)) (neg (of j x))
| add : Π (j) (x y : F.obj j), relation (of j (x + y)) (add (of j x) (of j y))
| smul : Π (j) (s) (x : F.obj j), relation (of j (s • x)) (smul s (of j x))
-- Then one relation per argument of each operation
| neg_1 : Π (x x') (r : relation x x'), relation (neg x) (neg x')
| add_1 : Π (x x' y) (r : relation x x'), relation (add x y) (add x' y)
| add_2 : Π (x y y') (r : relation y y'), relation (add x y) (add x y')
| smul_1 : Π (s) (x x') (r : relation x x'), relation (smul s x) (smul s x')
-- And one relation per axiom
| zero_add      : Π (x), relation (add zero x) x
| add_zero      : Π (x), relation (add x zero) x
| add_left_neg  : Π (x), relation (add (neg x) x) zero
| add_comm      : Π (x y), relation (add x y) (add y x)
| add_assoc     : Π (x y z), relation (add (add x y) z) (add x (add y z))
| one_smul      : Π (x), relation (smul 1 x) x
| mul_smul      : Π (s t) (x), relation (smul (s * t) x) (smul s (smul t x))
| smul_add      : Π (s) (x y), relation (smul s (add x y)) (add (smul s x) (smul s y))
| smul_zero     : Π (s), relation (smul s zero) zero
| add_smul      : Π (s t) (x), relation (smul (s + t) x) (add (smul s x) (smul t x))
| zero_smul     : Π (x), relation (smul 0 x) zero

/--
The setoid corresponding to module expressions modulo module relations and identifications.
-/
def colimit_setoid : setoid (prequotient F) :=
{ r := relation F, iseqv := ⟨relation.refl, relation.symm, relation.trans⟩ }
attribute [instance] colimit_setoid

/--
The underlying type of the colimit of a diagram in `Module R`.
-/
@[derive inhabited]
def colimit_type : Type v := quotient (colimit_setoid F)

instance : add_comm_group (colimit_type F) :=
{ zero :=
  begin
    exact quot.mk _ zero
  end,
  neg :=
  begin
    fapply @quot.lift,
    { intro x,
      exact quot.mk _ (neg x) },
    { intros x x' r,
      apply quot.sound,
      exact relation.neg_1 _ _ r },
  end,
  add :=
  begin
    fapply @quot.lift _ _ ((colimit_type F) → (colimit_type F)),
    { intro x,
      fapply @quot.lift,
      { intro y,
        exact quot.mk _ (add x y) },
      { intros y y' r,
        apply quot.sound,
        exact relation.add_2 _ _ _ r } },
    { intros x x' r,
      funext y,
      induction y,
      dsimp,
      apply quot.sound,
      { exact relation.add_1 _ _ _ r },
      { refl } },
  end,
  zero_add := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.zero_add,
    refl,
  end,
  add_zero := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.add_zero,
    refl,
  end,
  add_left_neg := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.add_left_neg,
    refl,
  end,
  add_comm := λ x y,
  begin
    induction x,
    induction y,
    dsimp,
    apply quot.sound,
    apply relation.add_comm,
    refl,
    refl,
  end,
  add_assoc := λ x y z,
  begin
    induction x,
    induction y,
    induction z,
    dsimp,
    apply quot.sound,
    apply relation.add_assoc,
    refl,
    refl,
    refl,
  end, }

instance : module R (colimit_type F) :=
{ smul := λ s,
  begin
    fapply @quot.lift,
    { intro x,
      exact quot.mk _ (smul s x) },
    { intros x x' r,
      apply quot.sound,
      exact relation.smul_1 s _ _ r },
  end,
  one_smul := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.one_smul,
    refl,
  end,
  mul_smul := λ s t x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.mul_smul,
    refl,
  end,
  smul_add := λ s x y,
  begin
    induction x,
    induction y,
    dsimp,
    apply quot.sound,
    apply relation.smul_add,
    refl,
    refl,
  end,
  smul_zero := λ s, begin apply quot.sound, apply relation.smul_zero, end,
  add_smul := λ s t x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.add_smul,
    refl,
  end,
  zero_smul := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.zero_smul,
    refl,
  end, }

@[simp] lemma quot_zero : quot.mk setoid.r zero = (0 : colimit_type F) := rfl
@[simp] lemma quot_neg (x) :
  quot.mk setoid.r (neg x) = (-(quot.mk setoid.r x) : colimit_type F) := rfl
@[simp] lemma quot_add (x y) :
  quot.mk setoid.r (add x y) = ((quot.mk setoid.r x) + (quot.mk setoid.r y) : colimit_type F) := rfl
@[simp] lemma quot_smul (s x) :
  quot.mk setoid.r (smul s x) = (s • (quot.mk setoid.r x) : colimit_type F) := rfl

/-- The bundled module giving the colimit of a diagram. -/
def colimit : Module R := Module.of R (colimit_type F)

/-- The function from a given module in the diagram to the colimit module. -/
def cocone_fun (j : J) (x : F.obj j) : colimit_type F :=
quot.mk _ (of j x)

/-- The group homomorphism from a given module in the diagram to the colimit module. -/
def cocone_morphism (j : J) : F.obj j ⟶ colimit F :=
{ to_fun := cocone_fun F j,
  map_smul' := by { intros, apply quot.sound, apply relation.smul, },
  map_add' := by intros; apply quot.sound; apply relation.add }

@[simp] lemma cocone_naturality {j j' : J} (f : j ⟶ j') :
  F.map f ≫ (cocone_morphism F j') = cocone_morphism F j :=
begin
  ext,
  apply quot.sound,
  apply relation.map,
end

@[simp] lemma cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j):
  (cocone_morphism F j') (F.map f x) = (cocone_morphism F j) x :=
by { rw ←cocone_naturality F f, refl }

/-- The cocone over the proposed colimit module. -/
def colimit_cocone : cocone F :=
{ X := colimit F,
  ι :=
  { app := cocone_morphism F } }.

/-- The function from the free module on the diagram to the cone point of any other cocone. -/
@[simp] def desc_fun_lift (s : cocone F) : prequotient F → s.X
| (of j x)  := (s.ι.app j) x
| zero      := 0
| (neg x)   := -(desc_fun_lift x)
| (add x y) := desc_fun_lift x + desc_fun_lift y
| (smul s x) := s • (desc_fun_lift x)

/-- The function from the colimit module to the cone point of any other cocone. -/
def desc_fun (s : cocone F) : colimit_type F → s.X :=
begin
  fapply quot.lift,
  { exact desc_fun_lift F s },
  { intros x y r,
    induction r; try { dsimp },
    -- refl
    { refl },
    -- symm
    { exact r_ih.symm },
    -- trans
    { exact eq.trans r_ih_h r_ih_k },
    -- map
    { simp, },
    -- zero
    { simp, },
    -- neg
    { simp, },
    -- add
    { simp, },
    -- smul,
    { simp, },
    -- neg_1
    { rw r_ih, },
    -- add_1
    { rw r_ih, },
    -- add_2
    { rw r_ih, },
    -- smul_1
    { rw r_ih, },
    -- zero_add
    { rw zero_add, },
    -- add_zero
    { rw add_zero, },
    -- add_left_neg
    { rw add_left_neg, },
    -- add_comm
    { rw add_comm, },
    -- add_assoc
    { rw add_assoc, },
    -- one_smul
    { rw one_smul, },
    -- mul_smul
    { rw mul_smul, },
    -- smul_add
    { rw smul_add, },
    -- smul_zero
    { rw smul_zero, },
    -- add_smul
    { rw add_smul, },
    -- zero_smul
    { rw zero_smul, }, }
end

/-- The group homomorphism from the colimit module to the cone point of any other cocone. -/
def desc_morphism (s : cocone F) : colimit F ⟶ s.X :=
{ to_fun := desc_fun F s,
  map_smul' := λ s x, by { induction x; refl, },
  map_add' := λ x y, by { induction x; induction y; refl }, }

/-- Evidence that the proposed colimit is the colimit. -/
def colimit_cocone_is_colimit : is_colimit (colimit_cocone F) :=
{ desc := λ s, desc_morphism F s,
  uniq' := λ s m w,
  begin
    ext,
    induction x,
    induction x,
    { have w' := congr_fun (congr_arg (λ f : F.obj x_j ⟶ s.X, (f : F.obj x_j → s.X)) (w x_j)) x_x,
      erw w',
      refl, },
    { simp *, },
    { simp *, },
    { simp *, },
    { simp *, },
    refl
  end }.

instance has_colimits_Module : has_colimits (Module R) :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk
    { cocone := colimit_cocone F,
      is_colimit := colimit_cocone_is_colimit F } } }

end Module.colimits
