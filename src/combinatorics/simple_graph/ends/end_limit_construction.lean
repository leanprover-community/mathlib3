import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic

import .bwd_map

open category_theory
open opposite
open simple_graph
open classical
open simple_graph.bwd_map

/- Implementing Kyle Miller's suggestion:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Geometric.20group.20theory/near/290624806 -/

noncomputable theory
local attribute [instance] prop_decidable

universes u v w
variables {V : Type u} [decidable_eq V] (h : V ≃ ℕ)
variables (G : simple_graph V) (Gpc : G.preconnected) [locally_finite G]

instance finset_preorder : preorder (finset V) := {
  le := λ A B, A ⊆ B,
  lt := λ A B, A ⊂ B,
  le_refl := by {obviously},
  le_trans := by {obviously},
  lt_iff_le_not_le := by {obviously}
  }

/- The category of finite subsets of `V` with the morphisms being inclusions -/
instance FinIncl : category (finset V) := infer_instance

instance finset_directed : is_directed (finset V) (≤) := {
  directed := λ A B, ⟨A ∪ B, ⟨finset.subset_union_left A B, finset.subset_union_right A B⟩⟩ }

/-The functor assigning a finite set in `V` to the set of connected components in its complement-/
def ComplComp : (finset V)ᵒᵖ ⥤ Type u := {
  obj := λ A, ro_components G (unop A),
  map := λ A B f, bwd_map G Gpc (le_of_hom f.unop),
  map_id' := by {intro, funext, simp, apply bwd_map_refl',}, -- tricky to get right
  map_comp' := by {intros, funext, simp, apply eq.symm, apply bwd_map_comp',},
}

def Ends := (ComplComp G Gpc).sections

/-The functor assigning a finite set in `V` to the set of **infinite** connected components in its complement-/
def ComplInfComp : (finset V)ᵒᵖ ⥤ Type u := {
  obj := λ A, {C : ro_components G (unop A) | C.val.infinite},
  map := λ A B f, set.maps_to.restrict (bwd_map G Gpc (le_of_hom f.unop)) _ _ (bwd_map_inf_to_inf G Gpc (le_of_hom f.unop)),
  map_id' := by {sorry}, -- tricky to get right
  map_comp' := by {sorry},
}

def Endsinfty := (ComplInfComp G Gpc).sections

lemma Ends_are_Endsinfty : (Ends G Gpc) ≃ (Endsinfty G Gpc) := sorry
-- Should use `fis.sections_surjective_equiv_sections` and the fact that `inf_ro_components` is exactly the surjective part



instance obj_nonempty (Vinf : set.infinite (@set.univ V)) :  ∀ (j : (finset V)ᵒᵖ), nonempty ((ComplComp G Gpc).obj j) := by {
  intro K,
  obtain ⟨C,Ccomp,Cinf⟩ := ro_component.infinite_graph_to_inf_components_nonempty G Gpc K.unop Vinf,
  use [C,Ccomp],
}

instance obj_fintype : Π (j : (finset V)ᵒᵖ), fintype ((ComplComp G Gpc).obj j) := by {
  intro K,
  exact (ro_component.finite G Gpc K.unop).fintype,
}


theorem exists_end_inf_graph (Vinf : set.infinite  (@set.univ V)) : (Ends G Gpc).nonempty :=
  @nonempty_sections_of_fintype_inverse_system _ _ _ (ComplComp G Gpc) _ (obj_nonempty G Gpc Vinf)
