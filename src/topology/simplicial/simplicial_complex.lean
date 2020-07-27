/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import topology.simplicial.simplicial_module
import algebra.category.Module.monoidal

/-! # The simplicial complex associated with a simplicial module -/

noncomputable theory

universe variables u

open category_theory

namespace simplicial_module
open Simplicial opposite
variables {R : Type u} [comm_ring R]

def graded_object (M : simplicial_module R) : graded_object_with_shift (-1:ℤ) (Module R)
| -[1+n] := Module.of R punit -- this should just be 0
| (n:ℕ)  := (skeletal.obj M).obj (op n)

def graded_object_d (M : simplicial_module R) :
  M.graded_object ⟶ M.graded_object⟦1⟧
| -[1+n]  := 0
| (0:ℕ)   := 0
| (n+1:ℕ) :=
begin
  refine M.boundary n ≫ _,
  show M.graded_object n ⟶ M.graded_object (n+1-1),
end


variables (R)

@[simps]
def simplicial_complex : simplicial_module R ⥤ chain_complex (Module R) :=
{ obj := λ M,
  { X := M.graded_object,
    d := λ i, _, --graded_object_d M,
    d_squared' := _ },
  map := _,
  map_id' := _,
  map_comp' := _ }

end simplicial_module
