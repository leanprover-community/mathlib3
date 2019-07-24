import topology.Top.presheaf
import category_theory.limits.limits

universes v u

open category_theory
open category_theory.limits
open topological_space
open opposite

namespace Top

variables (X : Top.{v})

structure cover :=
(ι : Type v)
(map : ι → opens X)

variables {X}

namespace cover

def total (c : cover X) : opens X := sorry

inductive intersections (c : cover X)
| single : c.ι → intersections
| double : c.ι → c.ι → intersections
.

namespace intersections
variable (c : cover.{v} X)

inductive hom : intersections c → intersections c → Type v
| id_single : Π (a : c.ι), hom (single a) (single a)
| id_double : Π (a b : c.ι), hom (double a b) (double a b)
| left : Π (a b : c.ι), hom (single a) (double a b)
| right : Π (a b : c.ι), hom (single b) (double a b)
.

def id : Π j : intersections c, hom c j j
| (single a) := hom.id_single a
| (double a b) := hom.id_double a b
.

def comp : Π j₁ j₂ j₃ : intersections c, hom c j₁ j₂ → hom c j₂ j₃ → hom c j₁ j₃
| _ _ _ (hom.id_single _) x := x
| _ _ _ (hom.id_double _ _) x := x
| _ _ _ (hom.left a b) (hom.id_double _ _) := hom.left a b
| _ _ _ (hom.right a b) (hom.id_double _ _) := hom.right a b

local attribute [tidy] tactic.case_bash
instance : small_category (intersections c) :=
{ hom := hom c,
  id := id c,
  comp := comp c }

end intersections

end cover

open cover.intersections

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

variables (F : X.presheaf C)

namespace presheaf
variables (c : cover.{v} X)

def on_cover_obj : c.intersections → C
| (single a) := F.obj (op (c.map a))
| (double a b) := F.obj (op ((c.map a) ∩ (c.map b)))

def on_cover_map : Π (x y : c.intersections) (f : x ⟶ y), on_cover_obj F c x ⟶ on_cover_obj F c y
| _ _ (hom.id_single _) := 𝟙 _
| _ _ (hom.id_double _ _) := 𝟙 _
| _ _ (hom.left a b) := sorry
| _ _ (hom.right a b) := sorry

def on_cover (c : cover.{v} X) : c.intersections ⥤ C :=
{ obj := on_cover_obj F c,
  map := λ X Y f, on_cover_map F c X Y f,
  map_id' := sorry,
  map_comp' := sorry, }

def cover_cone (c : cover.{v} X) : cone (F.on_cover c) :=
{ X := c.total,
  π :=
  { app := sorry,
    naturality' := sorry, }}

def sheaf_condition := Π (c : cover.{v} X), is_limit (F.cover_cone c)
end presheaf

structure sheaf :=
(F : X.presheaf C)
(condition : F.sheaf_condition)

end Top
