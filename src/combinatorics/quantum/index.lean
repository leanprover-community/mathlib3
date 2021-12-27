/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.quiver
import data.sym.sym2

/-!
# Indexed multigraphs
-/

variables {F E α β W : Type*}

structure index_multigraph (E α : Type*) :=
(edges : E → sym2 α)

structure index_weight_multigraph (E α W : Type*) extends index_multigraph E α :=
(edge_weight : E → W)
