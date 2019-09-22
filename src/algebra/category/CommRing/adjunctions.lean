/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import algebra.category.CommRing.basic
import category_theory.adjunction.basic
import data.mv_polynomial

/-!
Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/

noncomputable theory

universe u

open mv_polynomial
open category_theory

namespace CommRing

open_locale classical

/--
The free functor `Type u ⥤ CommRing.{u}` sending a type `X` to the multivariable (commutative)
polynomials with variables `x : X`.
-/
def free : Type u ⥤ CommRing.{u} :=
{ obj := λ α, of (mv_polynomial α ℤ),
  -- TODO this should just be `ring_hom.of (rename f)`, but this causes a mysterious deterministic timeout!
  map := λ X Y f, @ring_hom.of _ _ _ _ (rename f) (by apply_instance),
  -- TODO these next two fields can be done by `tidy`, but the calls in `dsimp` and `simp` it generates are rather slow.
  map_id' := λ X, ring_hom.ext $ funext $ rename_id,
  map_comp' := λ X Y Z f g, ring_hom.ext $ funext $ λ p, (rename_rename f g p).symm }

@[simp] lemma free_obj_coe {α : Type u} :
  (free.obj α : Type u) = mv_polynomial α ℤ := rfl

@[simp] lemma free_map_coe {α β : Type u} {f : α → β} :
  ⇑(free.map f) = rename f := rfl

namespace adj
-- The next two definitions are (unfortunate) "implementation details", helping the elaborator / typeclass search.

/-- Version of `mv_polynomial.hom_equiv` for bundled commutative rings. -/
def hom_equiv (X : Type u) (R : CommRing) : (mv_polynomial X ℤ →+* R) ≃ (X → R) := hom_equiv R X
instance (R : CommRing) : is_ring_hom (λ (n : ℤ), (n : R)) := by apply_instance

end adj
open adj

/--
The free-forgetful adjunction for commutative rings.
-/
def adj : free ⊣ forget CommRing.{u} :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X R, hom_equiv X R,
  hom_equiv_naturality_left_symm' := by { intros, ext, dsimp, apply eval₂_cast_comp } }

end CommRing
