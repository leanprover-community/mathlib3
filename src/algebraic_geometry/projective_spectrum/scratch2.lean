import ring_theory.localization
import algebraic_geometry.Spec

open Top
open topological_space
open category_theory
open opposite
open algebraic_geometry

local notation `Spec` ring := Spec.LocallyRingedSpace_obj (CommRing.of ring)

variables (R : Type) [comm_ring R] (U : opens (Spec R)) (x y : U) (h1 : y = x)

variable (hh : (algebraic_geometry.structure_sheaf R).1.obj (op U))

include h1
lemma section_congr_arg (a) (b) (h2 : hh.1 x = localization.mk a b) : hh.1 y =
  localization.mk a ⟨b.1, begin
  erw h1,
  exact b.2
end⟩ :=
begin
  induction h1,
  convert h2,
  rw subtype.ext_iff_val,
end
