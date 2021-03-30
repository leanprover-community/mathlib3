import topology.category.Top.limits
import category_theory.limits.shapes
import topology.instances.real
import topology.tactic

/-! This file contains some demos of using the (co)limits API to do topology. -/

noncomputable theory

open category_theory
open category_theory.limits

def R : Top := Top.of ℝ
def I : Top := Top.of (set.Icc 0 1 : set ℝ)
def pt : Top := Top.of unit

section MappingCylinder
-- Let's construct the mapping cylinder.
def to_pt (X : Top) : X ⟶ pt :=
{ to_fun := λ _, unit.star, } -- We don't need to prove continuity: this is done automatically.
def I₀ : pt ⟶ I :=
{ to_fun := λ _, ⟨(0 : ℝ), by norm_num [set.left_mem_Icc]⟩, }
def I₁ : pt ⟶ I :=
{ to_fun := λ _, ⟨(1 : ℝ), by norm_num [set.right_mem_Icc]⟩, }

def cylinder (X : Top) : Top := prod X I
-- To define a map to the cylinder, we give a map to each factor.
-- `prod.lift` is a helper method, providing a wrapper around `limit.lift` for binary products.
def cylinder₀ (X : Top) : X ⟶ cylinder X :=
prod.lift (𝟙 X) (to_pt X ≫ I₀)
def cylinder₁ (X : Top) : X ⟶ cylinder X :=
prod.lift (𝟙 X) (to_pt X ≫ I₁)

-- The mapping cylinder is the pushout of the diagram
--    X
--   ↙ ↘
--  Y   (X x I)
-- (`pushout` is implemented just as a wrapper around `colimit`) is
def mapping_cylinder {X Y : Top} (f : X ⟶ Y) : Top := pushout f (cylinder₁ X)

/-- We construct the map from `X` into the "bottom" of the mapping cylinder
for `f : X ⟶ Y`, as the composition of the inclusion of `X` into the bottom of the
cylinder `prod X I`, followed by the map `pushout.inr` of `prod X I` into `mapping_cylinder f`. -/
def mapping_cylinder₀ {X Y : Top} (f : X ⟶ Y) : X ⟶ mapping_cylinder f :=
cylinder₀ X ≫ pushout.inr

/--
The mapping cone is defined as the pushout of
```
         X
        ↙ ↘
 (Cyl f)   pt
```
(where the left arrow is `mapping_cylinder₀`).

This makes it an iterated colimit; one could also define it in one step as the colimit of
```
--    X        X
--   ↙ ↘      ↙ ↘
--  Y   (X x I)  pt
```
-/
def mapping_cone {X Y : Top} (f : X ⟶ Y) : Top := pushout (mapping_cylinder₀ f) (to_pt X)

-- TODO Hopefully someone will write a nice tactic for generating diagrams quickly,
-- and we'll be able to verify that this iterated construction is the same as the colimit
-- over a single diagram.
end MappingCylinder

section Gluing

-- Here's two copies of the real line glued together at a point.
def f : pt ⟶ R := { to_fun := λ _, (0 : ℝ), }

/-- Two copies of the real line glued together at 0. -/
def X : Top := pushout f f

-- To define a map out of it, we define maps out of each copy of the line,
-- and check the maps agree at 0.
def g : X ⟶ R :=
pushout.desc (𝟙 _) (𝟙 _) rfl

end Gluing

section Products

/-- The countably infinite product of copies of `ℝ`. -/
def Y : Top := ∏ (λ n : ℕ, R)

/--
We can define a point in this infinite product by specifying its coordinates.
Let's define the point whose `n`-th coordinate is `n + 1` (as a real number).
-/
def q : pt ⟶ Y :=
pi.lift (λ (n : ℕ), ⟨λ (_ : pt), (n + 1 : ℝ), by continuity⟩)

-- Note that writing `Y := ∏ (λ n : ℕ, R)` gives us *some* topological space which satisfies the
-- universal property of the product, not some explicit construction of the product, so we cannot
-- rely on any definitional properties of `Y` or `q`.
-- If we really want to talk about a specific construction of the limit, we have to work directly
-- with the corresponding limit cones. In this case, `Top.limit_cone`.

end Products
