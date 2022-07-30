import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic

import .ends

open category_theory
open opposite
open simple_graph

/- Implementing Kyle Miller's suggestion:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Geometric.20group.20theory/near/290624806 -/



universes u v w
variables {V : Type u} [decidable_eq V] (G : simple_graph V) (Gpc : G.preconnected)

instance : preorder (finset V) := {
  le := λ A B, A ⊆ B,
  lt := λ A B, A ⊂ B,
  le_refl := by {obviously},
  le_trans := by {obviously},
  lt_iff_le_not_le := by {obviously}
  }

/- The category of finite subsets of `V` with the morphisms being inclusions -/
instance FinIncl : category (finset V) := infer_instance

instance : is_directed (finset V) (≤) := {
  directed := λ A B, ⟨A ∪ B, ⟨finset.subset_union_left A B, finset.subset_union_right A B⟩⟩ }

/-The functor assigning a finite set in `V` to the set of infinite connected components in its complement-/
def ComplInfComp : (finset V)ᵒᵖ ⥤ Type* := {
  obj := λ A, inf_ro_components G (unop A),
  map := λ A B f, ends.bwd_map G Gpc (le_of_hom f.unop),
  map_id' := by {intro, funext, simp, apply ends.bwd_map_refl}, -- tricky to get right
  map_comp' := by {intros, funext, simp, apply eq.symm, apply ends.bwd_map_comp',},
  }

-- theorem exists_end_inf_graph := nonempty_sections_of_fintype_cofiltered_system (ComplInfComp G Gpc)
