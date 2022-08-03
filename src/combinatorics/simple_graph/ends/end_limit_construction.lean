import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic

import .ends

open category_theory
open opposite
open simple_graph

/- Implementing Kyle Miller's suggestion:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Geometric.20group.20theory/near/290624806 -/

noncomputable theory

universes u v w
variables {V : Type u} [decidable_eq V] [Vinf : set.infinite (set.univ : set V)] (h : V ≃ ℕ)
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

/-The functor assigning a finite set in `V` to the set of infinite connected components in its complement-/
def ComplInfComp : (finset V)ᵒᵖ ⥤ Type u := {
  obj := λ A, inf_ro_components G (unop A),
  map := λ A B f, ends.bwd_map G Gpc (le_of_hom f.unop),
  map_id' := by {intro, funext, simp, apply ends.bwd_map_refl',}, -- tricky to get right
  map_comp' := by {intros, funext, simp, apply eq.symm, apply ends.bwd_map_comp',},
  }

/-
instance : is_cofiltered (finset V) := {
  cocone_objs := _,
  cocone_maps := _,
  nonempty := _ }
-/

instance obj_nonempty :  ∀ (j : (finset V)ᵒᵖ), nonempty ((ComplInfComp G Gpc).obj j) := by {
  intro, show (nonempty (inf_ro_components G (unop _))), generalize : (unop _) = x,
   apply ro_component.infinite_graph_to_inf_components_nonempty,
  assumption, sorry, -- exact Vinf,
}

instance obj_fintype : Π (j : (finset V)ᵒᵖ), fintype ((ComplInfComp G Gpc).obj j) := by {
  intro, show (fintype (inf_ro_components G (unop _))), generalize : unop _ = x,
  apply ro_component.inf_components_finite, exact Gpc,
}

theorem exists_end_inf_graph : (ComplInfComp G Gpc).sections.nonempty :=
  nonempty_sections_of_fintype_inverse_system (ComplInfComp G Gpc)

-- a slightly modified definition of ends, meant to make proving equivalence with the sections definition easier
def ends :=
  {f : Π (K : finset V), inf_ro_components G K // ∀ A B : finset V, Π h: A ⊆ B, ends.bwd_map G Gpc h (f B) = f A}

lemma ends_eq_sections :  (ComplInfComp G Gpc).sections ≃ (ends G Gpc)  :=
begin
  rw [functor.sections, ends, ComplInfComp], simp,
  split, rotate 2,
  { rintro ⟨Kfmly : Π (K : (finset V)ᵒᵖ), G.inf_ro_components (unop K), hbwd⟩,
    let endK : Π (K : finset V), G.inf_ro_components K := by {
      intro K, rw [← opposite.unop_op K], apply Kfmly, },
    use endK,
    intros _ _ hsub,
    exact hbwd (quiver.hom.op (hom_of_le hsub)), },
  { rintro ⟨Kfmly, hbwd⟩,
    apply subtype.mk, rotate,
    let endKop : Π (K : (finset V)ᵒᵖ), G.inf_ro_components (unop K) := by {intro Kop, apply Kfmly,},
    use endKop,
    intros _ _ f,
    simp, apply hbwd, },
  { simp [function.left_inverse],
    intros, ext, refl, },
  { simp [function.right_inverse, function.left_inverse],
    intros, ext, refl, }
end
