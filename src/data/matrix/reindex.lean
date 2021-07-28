/-
Copyright (c) 2021 Filippo Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo Nuccio
-/
import data.matrix.basic
import linear_algebra.matrix.reindex

/-!
# Matrices
-/

open matrix

variables {m n o : Type*} [fintype m] [fintype n] [fintype o]
variables {m₁ n₁ o₁ : Type*} [fintype m₁] [fintype n₁] [fintype o₁]
variables {R : Type*}

namespace matrix

/-- equivalences between matrix ((m × n) × o) ((m₁ × n₁) × o₁) R and
 matrix (m × n × o) (m₁ × n₁ × o₁) R -/
def index_assoc : matrix ((m × n) × o) ((m₁ × n₁) × o₁) R ≃ matrix (m × n × o) (m₁ × n₁ × o₁) R :=
matrix.reindex (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _)

variables {α : Type*} [semiring α]
variables [add_comm_monoid R] [module α R]

def linear_equiv_index_assoc :
  matrix ((m × n) × o) ((m₁ × n₁) × o₁) R ≃ₗ[α] matrix (m × n × o) (m₁ × n₁ × o₁) R :=
matrix.reindex_linear_equiv α R (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _)

end matrix
