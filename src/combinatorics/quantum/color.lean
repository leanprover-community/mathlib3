/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import .hierarchy

/-!
# Edge coloring of multigraphs
-/

variables {α F W 𝒸 : Type*}

namespace graph
section quiver
variables [quiver_class F α] {G : F}

structure hom_coloring (G : F) (𝒸 : Type*) :=
(color (a b : α) : (a ⟶[G] b) → 𝒸)


end quiver

section weight_digraph
variables [weight_digraph_class F α W] {G : F}

def hom_coloring_weight (G : F) : hom_coloring G W :=

end weight_digraph
end graph
