import category_theory.instances.topological_spaces
import category_theory.limits.shapes
import topology.instances.real

/- This file contains some demos of using the limits API to do topology.
   Because we haven't provided much support for limits of special shapes,
   it's a bit cumbersome at present. -/

noncomputable theory

open category_theory
open category_theory.instances
open category_theory.limits

def R : Top := Top.of ℝ
def I : Top := Top.of (set.Icc 0 1 : set ℝ)
def pt : Top := Top.of unit

section MappingCylinder
-- Let's construct the mapping cylinder.
def to_pt (X : Top) : X ⟶ pt :=
{ val := λ _, unit.star, property := continuous_const }
def I_1 : pt ⟶ I :=
{ val := λ _, ⟨(1 : ℝ), begin simp, split; norm_num, end⟩,
  property := continuous_const }

def cylinder (X : Top) : Top := limit (functor.of_function (pair X I))
def cylinder_1 (X : Top) : X ⟶ cylinder X :=
-- To define a map to the cylinder, we give a map to each factor.
-- There's no nice API for this yet, so you just have to use the general limits API for now.
limit.lift (functor.of_function (pair X I))
{ X := X,
  π :=
  { app := λ j : walking_pair, match j with
    | walking_pair.left := 𝟙 X
    | walking_pair.right := to_pt X ≫ I_1
    end }}
def mapping_cylinder {X Y : Top} (f : X ⟶ Y) : Top := colimit (span (𝟙 X) (cylinder_1 X))

end MappingCylinder

section Gluing
-- Similarly, here's two copies of the real line glued together at a point.
def f : pt ⟶ R := { val := λ _, (0 : ℝ), property := continuous_const }
def X : Top := colimit (span f f)

-- To define a map out of it, we define maps out of each copy of the line,
-- and check the maps agree at 0.

-- We're still discussing the best API for this, so for now it's quite gross:
local attribute [tidy] tactic.case_bash

def g : X ⟶ R :=
colimit.desc (span f f)
{ X := R,
  ι :=
  { app := λ j : walking_span, match j with
    | walking_span.zero  := f
    | walking_span.left  := 𝟙 _
    | walking_span.right := 𝟙 _
    end } }.
end Gluing

section Products
-- Let's construct an infinite product of copies of ℝ
def Y : Top := limit (functor.of_function (λ n : ℕ, R))
-- As above, for now we need to use the general limits API.
-- To construct of point of Y, we give points in each factor.
def q : pt ⟶ Y :=
limit.lift (functor.of_function (λ n : ℕ, R))
{ X := pt,
  π := { app := λ n : ℕ, { val := λ _, (n : ℝ), property := continuous_const } } }.

example : (q.val ()).val (57 : ℕ) = ((57 : ℕ) : ℝ) := rfl
end Products
