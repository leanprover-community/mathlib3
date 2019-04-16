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
def I_0 : pt ⟶ I :=
{ val := λ _, ⟨(0 : ℝ), begin simp, split; norm_num, end⟩,
  property := continuous_const }
def I_1 : pt ⟶ I :=
{ val := λ _, ⟨(1 : ℝ), begin simp, split; norm_num, end⟩,
  property := continuous_const }

def cylinder (X : Top) : Top := limit (pair X I)
-- To define a map to the cylinder, we give a map to each factor.
-- `binary_fan` is a helper method for constructing a `cone` over `pair X Y`.
def cylinder_0 (X : Top) : X ⟶ cylinder X :=
limit.lift (pair X I) (binary_fan (𝟙 X) (to_pt X ≫ I_0))
def cylinder_1 (X : Top) : X ⟶ cylinder X :=
limit.lift (pair X I) (binary_fan (𝟙 X) (to_pt X ≫ I_1))

-- The mapping cylinder is the colimit of the diagram
--    X
--   / \
--  Y   (X x I)
def mapping_cylinder {X Y : Top} (f : X ⟶ Y) : Top := colimit (span f (cylinder_1 X))

-- The mapping cone is the colimit of the diagram
--    X        X
--   / \      / \
--  Y   (X x I)  pt
-- Here we'll calculate it as an iterated colimit, as the colimit of
--         X
--        / \
-- (Cyl f)   (X x I)

def mapping_cylinder_0 {X Y : Top} (f : X ⟶ Y) : X ⟶ mapping_cylinder f :=
cylinder_0 X ≫ colimit.ι (span f (cylinder_1 X)) walking_span.right

def mapping_cone {X Y : Top} (f : X ⟶ Y) : Top := colimit (span (mapping_cylinder_0 f) (to_pt X))

-- TODO Hopefully someone will write a nice tactic for generating diagrams quickly,
-- and we'll be able to verify that this iterated construction is the same as the colimit
-- over a single diagram.
end MappingCylinder

section Gluing

-- Here's two copies of the real line glued together at a point.
def f : pt ⟶ R := { val := λ _, (0 : ℝ), property := continuous_const }
def X : Top := colimit (span f f)

-- To define a map out of it, we define maps out of each copy of the line,
-- and check the maps agree at 0.
-- `pushout_cocone.mk` is a helper method for constructing cocones over a span.
def g : X ⟶ R :=
colimit.desc (span f f) (pushout_cocone.mk (𝟙 _) (𝟙 _) rfl).

end Gluing

universes v u w

section Products

def d : discrete ℕ ⥤ Top := functor.of_function (λ n : ℕ, R)
/- (There is a coercion that lets us omit `functor.of_function`, but since you usually
   need explicitly stated universes before Lean inserts the coercion correctly,
   it's not really worth it: -/
-- def d' : discrete ℕ ⥤ Top.{0} := (λ n : ℕ, R)

def Y : Top := limit d

def w : cone d := fan.of_function (λ (n : ℕ), ⟨λ (_ : pt), (n : ℝ), continuous_const⟩)

def q : pt ⟶ Y :=
limit.lift d w

example : (q.val ()).val (57 : ℕ) = ((57 : ℕ) : ℝ) := rfl

end Products
