/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.CommRing.basic
import topology.category.Top.basic
import topology.instances.complex

universes u

open category_theory

/-- A bundled topological commutative ring. -/
structure TopCommRing :=
(α : Type u)
[is_comm_ring : comm_ring α]
[is_topological_space : topological_space α]
[is_topological_ring : topological_ring α]

namespace TopCommRing

section
-- We momentarily turn on some instances; we'll provide permanant instances in a moment,
-- written in terms of the coercion to `Type u`.
local attribute [instance] TopCommRing.is_comm_ring TopCommRing.is_topological_space TopCommRing.is_topological_ring

instance : concrete_category TopCommRing.{u} :=
{ to_category :=
  { hom   := λ R S, {f : R.1 →+* S.1 // continuous f },
    id    := λ R, ⟨ring_hom.id R.1, λ s a, a⟩,
    comp  := λ R S T f g, ⟨g.val.comp f.val,
      begin -- TODO automate
        cases f, cases g,
        dsimp, apply continuous.comp ; assumption
      end⟩ },
  forget := { obj := λ R, R.1, map := λ R S f, f.val },
  forget_faithful := { } }

instance : has_coe_to_sort TopCommRing.{u} := concrete_category.has_coe_to_sort TopCommRing
end

instance (R : TopCommRing) : comm_ring R := R.is_comm_ring
instance (R : TopCommRing) : topological_space R := R.is_topological_space
instance (R : TopCommRing) : topological_ring R := R.is_topological_ring

/-- Construct a bundled `TopCommRing` from the underlying type and the appropriate typeclasses. -/
def of (R : Type u) [comm_ring R] [topological_space R] [topological_ring R] : TopCommRing := ⟨R⟩

noncomputable example : TopCommRing := TopCommRing.of ℚ
noncomputable example : TopCommRing := TopCommRing.of ℝ
noncomputable example : TopCommRing := TopCommRing.of ℂ

instance forget_topological_space (R : TopCommRing) : topological_space ((forget TopCommRing).obj R) :=
R.is_topological_space
instance forget_comm_ring (R : TopCommRing) : comm_ring ((forget TopCommRing).obj R) :=
R.is_comm_ring
instance forget_topological_ring (R : TopCommRing) : topological_ring ((forget TopCommRing).obj R) :=
R.is_topological_ring

instance has_forget_to_CommRing : has_forget₂ TopCommRing CommRing :=
has_forget₂.mk'
  (λ R, CommRing.of R) (by tidy)
  (λ R S f, f.val) (by tidy)

instance forget_to_CommRing_topological_space (R : TopCommRing) :
  topological_space ((forget₂ TopCommRing CommRing).obj R) :=
R.is_topological_space

/-- The forgetful functor to Top. -/
instance has_forget_to_Top : has_forget₂ TopCommRing Top :=
has_forget₂.mk'
  (λ R, Top.of R) (by tidy)
  (λ R S f, ⟨f.1, f.2⟩) (by tidy)

instance forget_to_Top_comm_ring (R : TopCommRing) : comm_ring ((forget₂ TopCommRing Top).obj R) :=
R.is_comm_ring
instance forget_to_Top_topological_ring (R : TopCommRing) : topological_ring ((forget₂ TopCommRing Top).obj R) :=
R.is_topological_ring

end TopCommRing
