-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import algebra.CommRing.basic
import topology.Top.basic
import topology.instances.complex

universes u

open category_theory

structure TopCommRing :=
(α : Type u)
[is_comm_ring : comm_ring α]
[is_topological_space : topological_space α]
[is_topological_ring : topological_ring α]

namespace TopCommRing

instance : has_coe_to_sort TopCommRing :=
{ S := Type u, coe := TopCommRing.α }

attribute [instance] is_comm_ring is_topological_space is_topological_ring

instance TopCommRing_category : category TopCommRing :=
{ hom   := λ R S, {f : R → S // is_ring_hom f ∧ continuous f },
  id    := λ R, ⟨id, by obviously⟩, -- TODO remove obviously?
  comp  := λ R S T f g, ⟨g.val ∘ f.val,
    begin -- TODO automate
      cases f, cases g, cases f_property, cases g_property, split,
      dsimp, resetI, apply_instance,
      dsimp, apply continuous.comp ; assumption
    end⟩ }.

def of (X : Type u) [comm_ring X] [topological_space X] [topological_ring X] : TopCommRing := ⟨X⟩

noncomputable example : TopCommRing := TopCommRing.of ℚ
noncomputable example : TopCommRing := TopCommRing.of ℝ
noncomputable example : TopCommRing := TopCommRing.of ℂ

/-- The forgetful functor to CommRing. -/
def forget_to_CommRing : TopCommRing ⥤ CommRing :=
{ obj := λ R, { α := R },
  map := λ R S f, ⟨ f.1, f.2.left ⟩ }

instance forget_to_CommRing_faithful : faithful (forget_to_CommRing) := by tidy

instance forget_to_CommRing_topological_space (R : TopCommRing) : topological_space (forget_to_CommRing.obj R) :=
R.is_topological_space

/-- The forgetful functor to Top. -/
def forget_to_Top : TopCommRing ⥤ Top :=
{ obj := λ R, { α := R },
  map := λ R S f, ⟨ f.1, f.2.right ⟩ }

instance forget_to_Top_faithful : faithful (forget_to_Top) := by tidy

instance forget_to_Top_comm_ring (R : TopCommRing) : comm_ring (forget_to_Top.obj R) :=
R.is_comm_ring
instance forget_to_Top_topological_ring (R : TopCommRing) : topological_ring (forget_to_Top.obj R) :=
R.is_topological_ring

def forget : TopCommRing ⥤ Type u :=
{ obj := λ R, R,
  map := λ R S f, f.1 }

instance forget_faithful : faithful forget := {}

instance forget_topological_space (R : TopCommRing) : topological_space (forget.obj R) :=
R.is_topological_space
instance forget_comm_ring (R : TopCommRing) : comm_ring (forget.obj R) :=
R.is_comm_ring
instance forget_topological_ring (R : TopCommRing) : topological_ring (forget.obj R) :=
R.is_topological_ring

def forget_to_Type_via_Top : forget_to_Top ⋙ Top.forget ≅ forget := iso.refl _
def forget_to_Type_via_CommRing : forget_to_CommRing ⋙ CommRing.forget ≅ forget := iso.refl _

end TopCommRing
