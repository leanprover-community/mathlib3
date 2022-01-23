import ring_theory.localization
import algebraic_geometry.Spec

open Top
open topological_space
open category_theory
open opposite
open algebraic_geometry

variables (R : CommRing) (U : opens (prime_spectrum R)) (x y : U) (h1 : y = x)

variable (hh : (algebraic_geometry.structure_sheaf R).1.obj (op U))

include h1
example (a) (b) (h2 : hh.1 x = localization.mk a b) : hh.1 y = localization.mk a ⟨b.1, begin
  erw h1,
  exact b.2
end⟩ :=
begin
  convert h2,
  rw h1,
  apply heq_of_cast_eq,
  work_on_goal 1 {
    apply eq.rec_on h1,
    refl,
   },

  sorry,
end
