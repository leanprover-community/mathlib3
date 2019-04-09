import category_theory.instances.rings
import category_theory.instances.Top
import topology.algebra.ring
import data.real.basic
import data.complex.basic
import topology.instances.real
import topology.instances.complex

universes u

open category_theory

namespace category_theory.instances

structure TopCommRing :=
{α : Type u}
[is_comm_ring : comm_ring α]
[is_topological_space : topological_space α]
[is_topological_ring : topological_ring α]

instance : has_coe_to_sort TopCommRing :=
{ S := Type u, coe := TopCommRing.α }

instance TopCommRing_comm_ring (R : TopCommRing) : comm_ring R := R.is_comm_ring
instance TopCommRing_topological_space (R : TopCommRing) : topological_space R := R.is_topological_space
instance TopCommRing_topological_ring (R : TopCommRing) : topological_ring R := R.is_topological_ring

instance TopCommRing_category : category TopCommRing :=
{ hom   := λ R S, {f : R → S // is_ring_hom f ∧ continuous f },
  id    := λ R, ⟨id, by obviously⟩,
  comp  := λ R S T f g, ⟨g.val ∘ f.val,
    begin -- TODO automate
      cases f, cases g, cases f_property, cases g_property, split,
      dsimp, resetI, apply_instance,
      dsimp, apply continuous.comp ; assumption
    end⟩ }.

namespace TopCommRing

noncomputable def rational : TopCommRing :=
{ α := ℚ }
noncomputable def real : TopCommRing :=
{ α := ℝ }
noncomputable def complex : TopCommRing :=
{ α := ℂ }

/-- The forgetful functor to CommRing. -/
def forget_to_CommRing : TopCommRing ⥤ CommRing :=
{ obj := λ R, { α := R, str := instances.TopCommRing_comm_ring R },
  map := λ R S f, ⟨ f.1, f.2.left ⟩ }

instance forget_to_CommRing_faithful : faithful (forget_to_CommRing) := by tidy

instance forget_to_CommRing_topological_space (R : TopCommRing) : topological_space (forget_to_CommRing.obj R) :=
R.is_topological_space

/-- The forgetful functor to Top. -/
def forget_to_Top : TopCommRing ⥤ Top :=
{ obj := λ R, { α := R, str := instances.TopCommRing_topological_space R },
  map := λ R S f, ⟨ f.1, f.2.right ⟩ }

instance forget_to_Top_faithful : faithful (forget_to_Top) := by tidy

instance forget_to_Top_comm_ring (R : TopCommRing) : comm_ring (forget_to_Top.obj R) :=
R.is_comm_ring
instance forget_to_Top_topological_ring (R : TopCommRing) : topological_ring (forget_to_Top.obj R) :=
R.is_topological_ring

def forget : TopCommRing ⥤ (Type u) :=
{ obj := λ R, R,
  map := λ R S f, f.1 }

instance forget_faithful : faithful (forget) := by tidy

instance forget_topological_space (R : TopCommRing) : topological_space (forget.obj R) :=
R.is_topological_space
instance forget_comm_ring (R : TopCommRing) : comm_ring (forget.obj R) :=
R.is_comm_ring
instance forget_topological_ring (R : TopCommRing) : topological_ring (forget.obj R) :=
R.is_topological_ring

def forget_to_Type_via_Top : forget_to_Top ⋙ category_theory.forget ≅ forget := iso.refl _
def forget_to_Type_via_CommRing : forget_to_Top ⋙ category_theory.forget ≅ forget := iso.refl _

end TopCommRing

end category_theory.instances
