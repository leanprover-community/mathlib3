/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.pullbacks
import algebraic_geometry.AffineScheme

/-!
# (Co)Limits of Schemes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct various limits and colimits in the category of schemes.

* The existence of fibred products was shown in `algebraic_geometry/pullbacks.lean`.
* `Spec ℤ` is the terminal object.
* The preceding two results imply that `Scheme` has all finite limits.
* The empty scheme is the (strict) initial object.

## Todo

* Coproducts exists (and the forgetful functors preserve them).

-/

universe u

open category_theory category_theory.limits opposite topological_space

namespace algebraic_geometry

/-- `Spec ℤ` is the terminal object in the category of schemes. -/
noncomputable
def Spec_Z_is_terminal : is_terminal (Scheme.Spec.obj (op $ CommRing.of ℤ)) :=
@@is_terminal.is_terminal_obj _ _ Scheme.Spec _ infer_instance
  (terminal_op_of_initial CommRing.Z_is_initial)

instance : has_terminal Scheme := has_terminal_of_has_terminal_of_preserves_limit Scheme.Spec

instance : is_affine (⊤_ Scheme.{u}) :=
is_affine_of_iso (preserves_terminal.iso Scheme.Spec).inv

instance : has_finite_limits Scheme :=
has_finite_limits_of_has_terminal_and_pullbacks

section initial

/-- The map from the empty scheme. -/
@[simps]
def Scheme.empty_to (X : Scheme.{u}) : ∅ ⟶ X :=
⟨{ base := ⟨λ x, pempty.elim x, by continuity⟩,
    c := { app := λ U, CommRing.punit_is_terminal.from _ } }, λ x, pempty.elim x⟩

@[ext]
lemma Scheme.empty_ext {X : Scheme.{u}} (f g : ∅ ⟶ X) : f = g :=
by { ext a, exact pempty.elim a }

lemma Scheme.eq_empty_to {X : Scheme.{u}} (f : ∅ ⟶ X) : f = Scheme.empty_to X :=
Scheme.empty_ext f (Scheme.empty_to X)

instance (X : Scheme.{u}) : unique (∅ ⟶ X) :=
⟨⟨Scheme.empty_to _⟩, λ _, Scheme.empty_ext _ _⟩

/-- The empty scheme is the initial object in the category of schemes. -/
def empty_is_initial : is_initial (∅ : Scheme.{u}) :=
is_initial.of_unique _

@[simp]
lemma empty_is_initial_to : empty_is_initial.to = Scheme.empty_to := rfl

instance : is_empty Scheme.empty.carrier :=
show is_empty pempty, by apply_instance

instance Spec_punit_is_empty : is_empty (Scheme.Spec.obj (op $ CommRing.of punit)).carrier :=
⟨prime_spectrum.punit⟩

@[priority 100]
instance is_open_immersion_of_is_empty {X Y : Scheme} (f : X ⟶ Y) [is_empty X.carrier] :
  is_open_immersion f :=
begin
  apply_with is_open_immersion.of_stalk_iso { instances := ff },
  { apply open_embedding_of_continuous_injective_open,
    { continuity },
    { rintro (i : X.carrier), exact is_empty_elim i },
    { intros U hU, convert is_open_empty, ext, apply (iff_false _).mpr,
      exact λ x, is_empty_elim (show X.carrier, from x.some) } },
  { rintro (i : X.carrier), exact is_empty_elim i }
end

@[priority 100]
instance is_iso_of_is_empty {X Y : Scheme} (f : X ⟶ Y) [is_empty Y.carrier] : is_iso f :=
begin
  haveI : is_empty X.carrier := ⟨λ x, is_empty_elim (show Y.carrier, from f.1.base x)⟩,
  haveI : epi f.1.base,
  { rw Top.epi_iff_surjective, rintro (x : Y.carrier), exact is_empty_elim x },
  apply is_open_immersion.to_iso
end

/-- A scheme is initial if its underlying space is empty . -/
noncomputable
def is_initial_of_is_empty {X : Scheme} [is_empty X.carrier] : is_initial X :=
empty_is_initial.of_iso (as_iso $ empty_is_initial.to _)

/-- `Spec 0` is the initial object in the category of schemes. -/
noncomputable
def Spec_punit_is_initial : is_initial (Scheme.Spec.obj (op $ CommRing.of punit)) :=
empty_is_initial.of_iso (as_iso $ empty_is_initial.to _)

@[priority 100]
instance is_affine_of_is_empty {X : Scheme} [is_empty X.carrier] : is_affine X :=
is_affine_of_iso (inv (empty_is_initial.to X) ≫
  empty_is_initial.to (Scheme.Spec.obj (op $ CommRing.of punit)))

instance : has_initial Scheme :=
has_initial_of_unique Scheme.empty

instance initial_is_empty : is_empty (⊥_ Scheme).carrier :=
⟨λ x, ((initial.to Scheme.empty : _).1.base x).elim⟩

lemma bot_is_affine_open (X : Scheme) : is_affine_open (⊥ : opens X.carrier) :=
begin
  convert range_is_affine_open_of_open_immersion (initial.to X),
  ext,
  exact (false_iff _).mpr (λ x, is_empty_elim (show (⊥_ Scheme).carrier, from x.some)),
end

instance : has_strict_initial_objects Scheme :=
has_strict_initial_objects_of_initial_is_strict (λ A f, by apply_instance)

end initial

end algebraic_geometry
