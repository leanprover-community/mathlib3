/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.CommRing.basic
import topology.category.Top.basic
import topology.algebra.ring

/-!
# Category of topological commutative rings

We introduce the category `TopCommRing` of topological commutative rings together with the relevant
forgetful functors to topological spaces and commutative rings.
-/

universes u

open category_theory

/-- A bundled topological commutative ring. -/
structure TopCommRing :=
(α : Type u)
[is_comm_ring : comm_ring α]
[is_topological_space : topological_space α]
[is_topological_ring : topological_ring α]

namespace TopCommRing

instance : has_coe_to_sort TopCommRing :=
{ S := Type u, coe := TopCommRing.α }

attribute [instance] is_comm_ring is_topological_space is_topological_ring

instance : category TopCommRing.{u} :=
{ hom   := λ R S, {f : R →+* S // continuous f },
  id    := λ R, ⟨ring_hom.id R, by obviously⟩, -- TODO remove obviously?
  comp  := λ R S T f g, ⟨g.val.comp f.val,
    begin -- TODO automate
      cases f, cases g,
      dsimp, apply continuous.comp ; assumption
    end⟩ }

instance : concrete_category TopCommRing.{u} :=
{ forget := { obj := λ R, R, map := λ R S f, f.val },
  forget_faithful := { } }

/-- Construct a bundled `TopCommRing` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [comm_ring X] [topological_space X] [topological_ring X] : TopCommRing := ⟨X⟩

@[simp] lemma coe_of (X : Type u) [comm_ring X] [topological_space X] [topological_ring X] :
  (of X : Type u) = X := rfl

instance forget_topological_space (R : TopCommRing) :
  topological_space ((forget TopCommRing).obj R) :=
R.is_topological_space
instance forget_comm_ring (R : TopCommRing) :
  comm_ring ((forget TopCommRing).obj R) :=
R.is_comm_ring
instance forget_topological_ring (R : TopCommRing) :
  topological_ring ((forget TopCommRing).obj R) :=
R.is_topological_ring

instance has_forget_to_CommRing : has_forget₂ TopCommRing CommRing :=
has_forget₂.mk'
  (λ R, CommRing.of R)
  (λ x, rfl)
  (λ R S f, f.val)
  (λ R S f, heq.rfl)

instance forget_to_CommRing_topological_space (R : TopCommRing) :
  topological_space ((forget₂ TopCommRing CommRing).obj R) :=
R.is_topological_space

/-- The forgetful functor to Top. -/
instance has_forget_to_Top : has_forget₂ TopCommRing Top :=
has_forget₂.mk'
  (λ R, Top.of R)
  (λ x, rfl)
  (λ R S f, ⟨⇑f.1, f.2⟩)
  (λ R S f, heq.rfl)

instance forget_to_Top_comm_ring (R : TopCommRing) :
  comm_ring ((forget₂ TopCommRing Top).obj R) :=
R.is_comm_ring

instance forget_to_Top_topological_ring (R : TopCommRing) :
  topological_ring ((forget₂ TopCommRing Top).obj R) :=
R.is_topological_ring

/--
The forgetful functors to `Type` do not reflect isomorphisms,
but the forgetful functor from `TopCommRing` to `Top` does.
-/
instance : reflects_isomorphisms (forget₂ TopCommRing.{u} Top.{u}) :=
{ reflects := λ X Y f _,
  begin
    resetI,
    -- We have an isomorphism in `Top`,
    let i_Top := as_iso ((forget₂ TopCommRing Top).map f),

    -- and a `ring_equiv`.
    let e_Ring : X ≃+* Y := { ..f.1, ..((forget Top).map_iso i_Top).to_equiv },

    -- Putting these together we obtain the isomorphism we're after:
    exact
    ⟨⟨⟨e_Ring.symm, i_Top.inv.2⟩,
      ⟨by { ext x, exact e_Ring.left_inv x, }, by { ext x, exact e_Ring.right_inv x, }⟩⟩⟩
  end }

end TopCommRing
