/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.pullbacks
import algebraic_geometry.AffineScheme
import category_theory.limits.constructions.finite_products_of_binary_products
import category_theory.limits.constructions.equalizers

/-!
# (Co)Limits of Schemes

We construct various limits and colimits in the category of schemes.

* The existence of fibred products was shown in `algebraic_geometry/pullbacks.lean`.
* `Spec ℤ` is the terminal object.
* The preceding two results imply that `Scheme` has all finite limits.
* The empty scheme is the (strict) initial object.
* Coproducts exists (and the forgetful functors preserve them).

-/

universe u

open category_theory category_theory.limits opposite

namespace algebraic_geometry

lemma has_finite_limits_of_has_terminal_has_pullbacks
  {C : Type*} [category C] [has_terminal C] [has_pullbacks C] : has_finite_limits C :=
@@finite_limits_from_equalizers_and_finite_products _
  (@@has_finite_products_of_has_binary_and_terminal _
    (has_binary_products_of_terminal_and_pullbacks C) infer_instance)
  (@@has_equalizers_of_pullbacks_and_binary_products _
    (has_binary_products_of_terminal_and_pullbacks C) infer_instance)

noncomputable
def Spec_Z_is_terminal : is_terminal (Scheme.Spec.obj (op $ CommRing.of ℤ)) :=
(terminal_op_of_initial CommRing.Z_is_initial).is_terminal_obj Scheme.Spec _

instance : has_terminal Scheme := has_terminal_of_has_terminal_of_preserves_limit Scheme.Spec

instance : is_affine (⊤_ Scheme.{u}) :=
is_affine_of_iso (preserves_terminal.iso Scheme.Spec).inv

instance : has_finite_limits Scheme :=
has_finite_limits_of_has_terminal_has_pullbacks

section initial

def sheaf_of_is_terminal {C A : Type*} [category C] [category A] (J : grothendieck_topology C)
  {X : A} (hX : is_terminal X) :
  Sheaf J A :=
{ val := (category_theory.functor.const _).obj X,
  cond := λ _ _ _ _ _ _, ⟨hX.from _, λ _ _ _, hX.hom_ext _ _, λ _ _, hX.hom_ext _ _⟩ }

@[simps]
def Scheme_empty : Scheme.{u} :=
{ carrier := Top.of pempty,
  presheaf := (category_theory.functor.const _).obj (CommRing.of punit),
  is_sheaf := by { apply Top.presheaf.is_sheaf_spaces_of_is_sheaf_sites,
    exact (sheaf_of_is_terminal _ CommRing.punit_is_terminal).cond },
  local_ring := λ x, pempty.elim x,
  local_affine := λ x, pempty.elim x }

@[simps]
def Scheme_empty_to (X : Scheme.{u}) : Scheme_empty ⟶ X :=
⟨{ base := ⟨λ x, pempty.elim x, by continuity⟩,
    c := { app := λ U, CommRing.punit_is_terminal.from _ } }, λ x, pempty.elim x⟩

@[ext]
def Scheme_empty_ext {X : Scheme.{u}} (f g : Scheme_empty ⟶ X) : f = g :=
by { ext x, exact pempty.elim x }

@[simp]
lemma Scheme_empty_to_eq {X : Scheme.{u}} (f : Scheme_empty ⟶ X) : f = Scheme_empty_to _ :=
Scheme_empty_ext f (Scheme_empty_to X)

instance (X : Scheme.{u}) : unique (Scheme_empty ⟶ X) :=
⟨⟨Scheme_empty_to _⟩, λ _, Scheme_empty_ext _ _⟩

def empty_is_initial : is_initial Scheme_empty :=
is_initial.of_unique _

@[simp]
lemma empty_is_initial_to : empty_is_initial.to = Scheme_empty_to := rfl

instance : is_empty (Scheme.Spec.obj (op $ CommRing.of punit)).carrier :=
⟨prime_spectrum.punit⟩

instance : is_iso (empty_is_initial.to (Scheme.Spec.obj (op $ CommRing.of punit))) :=
sorry

instance : is_affine Scheme_empty :=
is_affine_of_iso (empty_is_initial.to (Scheme.Spec.obj (op $ CommRing.of punit)))

instance : has_initial Scheme :=
has_initial_of_unique Scheme_empty

instance : has_strict_initial_objects Scheme :=
has_strict_initial_objects_of_initial_is_strict
begin
  intros A f,
  refine ⟨⟨(colimit.iso_colimit_cocone ⟨_, empty_is_initial⟩).hom ≫ empty_is_initial.to _, _, _⟩⟩,
  { sorry },
  { apply initial_is_initial.hom_ext }
end

end initial

section coproduct

-- by showing that the coproducts of schemes in the category of locally ringed spaces is a scheme
-- (presumably using `LocallyRingedSpace.is_open_immersion.Scheme`),
-- or by showing that gluing with empty intersection is the coproduct.
instance : has_coproducts Scheme.{u} := sorry

instance (I : Type*) :
  preserves_colimits_of_shape (discrete.{u} I) Scheme.forget_to_LocallyRingedSpace.{u} := sorry

noncomputable
instance (I : Type*) :
  preserves_colimits_of_shape (discrete.{u} I) Scheme.forget_to_Top.{u} :=
by { delta Scheme.forget_to_Top LocallyRingedSpace.forget_to_Top, apply_instance }

end coproduct

end algebraic_geometry
