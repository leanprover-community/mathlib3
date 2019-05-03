import category_theory.instances.Top.presheaf
import category_theory.instances.TopCommRing.basic
import category_theory.yoneda
import group_theory.submonoid
import ring_theory.subring
import topology.algebra.continuous_functions

universes v u

open category_theory
open category_theory.instances
open topological_space

open category_theory
open category_theory.instances
open topological_space

namespace category_theory.instances.Top

variables (X : Top.{v})

def continuous_presheaf (T : Top.{v}) : X.presheaf (Type v) :=
(opens.to_Top X).op ⋙ (yoneda.obj T)

def continuous_functions (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) : CommRing.{v} :=
{ α := (unop X) ⟶ (TopCommRing.forget_to_Top.obj R),
  str := presheaf_on_space.continuous_comm_ring } -- but infer_instance doesn't work?

-- FIXME why do we have to state these about monoid.one and comm_ring.add, instead
-- of using notation
@[simp] def continuous_functions_one (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) (x) :
  (monoid.one ↥(continuous_functions X R)).val x = 1 :=
rfl
@[simp] def continuous_functions_add (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) (f g : continuous_functions X R) (x) :
  (comm_ring.add f g).val x = f.1 x + g.1 x :=
rfl
@[simp] def continuous_functions_mul (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) (f g : continuous_functions X R) (x) :
  (ring.mul f g).val x = f.1 x * g.1 x :=
rfl

def continuous_functions.pullback {X Y : Topᵒᵖ} (f : X ⟶ Y) (R : TopCommRing) : continuous_functions X R ⟶ continuous_functions Y R :=
{ val := λ g, f.unop ≫ g,
  property :=
  { map_one := rfl,
    map_add := by tidy,
    map_mul := by tidy } }

local attribute [extensionality] subtype.eq

def continuous_functions.map (X : Topᵒᵖ) {R S : TopCommRing} (φ : R ⟶ S) : continuous_functions X R ⟶ continuous_functions X S :=
{ val := λ g, g ≫ (TopCommRing.forget_to_Top.map φ),
  property :=
  { map_one := begin ext1, ext1, dsimp, simp, exact φ.2.1.map_one end,
    map_add := λ x y, begin ext1, ext1, dsimp, simp, apply φ.2.1.map_add end,
    map_mul := λ x y, begin ext1, ext1, dsimp, simp, apply φ.2.1.map_mul end } }

def CommRing_yoneda : TopCommRing ⥤ (Topᵒᵖ ⥤ CommRing) :=
{ obj := λ R,
  { obj := λ X, continuous_functions X R,
    map := λ X Y f, continuous_functions.pullback f R },
  map := λ R S φ,
  { app := λ X, continuous_functions.map X φ } }

def presheaf_of_functions_to_TopCommRing (T : TopCommRing.{v}) :
  X.presheaf CommRing.{v} :=
(opens.to_Top X).op ⋙ (CommRing_yoneda.obj T)

noncomputable def presheaf_of_rational_functions (Y : Top.{0}) : Y.presheaf CommRing :=
presheaf_of_functions_to_TopCommRing Y (TopCommRing.of ℚ)

noncomputable def presheaf_of_real_functions (Y : Top) : Y.presheaf CommRing :=
presheaf_of_functions_to_TopCommRing Y (TopCommRing.of ℝ)

noncomputable def presheaf_of_complex_functions (Y : Top) : Y.presheaf CommRing :=
presheaf_of_functions_to_TopCommRing Y (TopCommRing.of ℂ)

end algebraic_geometry.presheaf_on_space
