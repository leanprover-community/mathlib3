import data.matrix.reflection

variables {α: Type*}

open_locale matrix
open matrix

-- This one is too long for the docstring, but is nice to have tested
example [add_comm_monoid α] [has_mul α]
  (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) :
  !![a₁₁, a₁₂, a₁₃;
     a₂₁, a₂₂, a₂₃;
     a₃₁, a₃₂, a₃₃] ⬝ !![b₁₁, b₁₂, b₁₃;
                        b₂₁, b₂₂, b₂₃;
                        b₃₁, b₃₂, b₃₃] =
  !![a₁₁*b₁₁ + a₁₂*b₂₁ + a₁₃*b₃₁, a₁₁*b₁₂ + a₁₂*b₂₂ + a₁₃*b₃₂, a₁₁*b₁₃ + a₁₂*b₂₃ + a₁₃*b₃₃;
     a₂₁*b₁₁ + a₂₂*b₂₁ + a₂₃*b₃₁, a₂₁*b₁₂ + a₂₂*b₂₂ + a₂₃*b₃₂, a₂₁*b₁₃ + a₂₂*b₂₃ + a₂₃*b₃₃;
     a₃₁*b₁₁ + a₃₂*b₂₁ + a₃₃*b₃₁, a₃₁*b₁₂ + a₃₂*b₂₂ + a₃₃*b₃₂, a₃₁*b₁₃ + a₃₂*b₂₃ + a₃₃*b₃₃] :=
(matrix.mulᵣ_eq _ _).symm
