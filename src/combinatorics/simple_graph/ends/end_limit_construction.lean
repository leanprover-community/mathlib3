import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic

import .bwd_map
import .mathlib_fintype_inverse_systems

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


-- Defined backwards for simpler use of `mathlib_fintype_inverse_systems.lean`
instance finset_preorder : preorder (finset V) := {
  le := λ A B, A ⊇ B,
  lt := λ A B, A ⊃ B,
  le_refl := by {obviously},
  le_trans := by {obviously},
  lt_iff_le_not_le := by {dsimp only [superset,ssuperset],obviously,}
  }

/- The category of finite subsets of `V` with the morphisms being inclusions -/
instance FinIncl : category (finset V) := infer_instance

instance finset_directed : is_directed (finset V) (≥) := {
  directed := λ A B, ⟨A ∪ B, ⟨finset.subset_union_left A B, finset.subset_union_right A B⟩⟩ }

/-The functor assigning a finite set in `V` to the set of connected components in its complement-/
def ComplComp : finset V ⥤ Type u := {
  obj := λ A, ro_components G A,
  map := λ A B f, bwd_map G Gpc (le_of_hom f),
  map_id' := by {intro, funext, simp, apply bwd_map.refl',},
  map_comp' := by {intros, funext, simp, apply eq.symm, apply bwd_map.comp',},
}

def Ends := (ComplComp G Gpc).sections

/-The functor assigning a finite set in `V` to the set of **infinite** connected components in its complement-/
def ComplInfComp : finset V ⥤ Type u := {
  obj := λ A, inf_ro_components' G A,
  map := λ A B f, bwd_map_inf G Gpc (le_of_hom f),
  map_id' := by {intro, funext, simp, apply bwd_map_inf.refl', },
  map_comp' := by {intros, funext, simp, symmetry, apply bwd_map_inf.comp', },
}

def Endsinfty := (ComplInfComp G Gpc).sections


lemma ComplInfComp_eq_ComplComp_to_surjective : ComplInfComp G Gpc = inverse_system.to_surjective (ComplComp G Gpc) :=
begin

  have objeq : ∀ (X : (finset V)), (ComplInfComp G Gpc).obj X = (inverse_system.to_surjective (ComplComp G Gpc)).obj X, by
  { simp [ComplInfComp,inverse_system.to_surjective,ComplComp],
    rintro K,
    have : {C : ↥(G.ro_components K) | (C.val : set V).infinite} = (⋂ (L ≤ K), set.range (bwd_map G Gpc H)), by
    { apply set.ext, rintro C, split,
      { rintro Cinf, simp at Cinf, rw set.mem_Inter₂, rintro L KL,
        obtain ⟨D,DtoC⟩ := bwd_map_inf.surjective G Gpc KL ⟨C,Cinf⟩, use D, dsimp [bwd_map_inf] at DtoC, sorry },
      { sorry, /-rintro Crange, simp at Crange, apply bwd_map_inf_of_surjective_on G Gpc, rintro L KL, simp, exact Crange L KL,-/},
    },
    sorry,
    /-rw this, simp, refl,-/},

  -- TODO: this should be very clean, but isn't!!! please help me
  apply category_theory.functor.hext,
  { exact objeq, },
  { rintro Kop Lop KL,
    dsimp [ComplInfComp, ComplComp, inverse_system.to_surjective, set.maps_to.restrict],
    apply heq.symm, apply heq_of_cast_eq,
    { dsimp [subtype.map],
      ext,
      split,
      { sorry },
      { sorry },
      -- dsimp [cast],
     },
    { sorry, }
  },
end

lemma Ends_equiv_Endsinfty : (Ends G Gpc) ≃ (Endsinfty G Gpc) :=
begin
  dsimp [Ends,Endsinfty],
  rw ComplInfComp_eq_ComplComp_to_surjective,
  apply inverse_system.to_surjective.sections_equiv,
end


instance ComplComp_nonempty [infinite V] :  ∀ (j : (finset V)), nonempty ((ComplComp G Gpc).obj j) := by {
  intro K,
  obtain ⟨C,Ccomp,Cinf⟩ := ro_component.infinite_graph_to_inf_components_nonempty G Gpc K,
  use [C,Ccomp],
}

instance ComplComp_fintype : Π (j : (finset V)), fintype ((ComplComp G Gpc).obj j) := by
{ intro K,
  exact (ro_component.finite G Gpc K).fintype,}

instance ComplInfComp_nonempty [infinite V] :
  Π (j : (finset V)), nonempty ((ComplInfComp G Gpc).obj j) := by
{ intro K,
  obtain ⟨C,Ccomp,Cinf⟩ := ro_component.infinite_graph_to_inf_components_nonempty G Gpc K,
  use [C,Ccomp],}

instance ComplInfComp_fintype : Π (j : (finset V)), fintype ((ComplInfComp G Gpc).obj j) := by
{ intro K,
  haveI := (ro_component.finite G Gpc K).fintype,
  dsimp [ComplInfComp],
  apply subtype.fintype,}



lemma all_empty [finite V] : ∀ (K : finset V), is_empty ((ComplInfComp G Gpc).obj K) :=
begin
  sorry,
end

lemma ComplInfComp.surjective : inverse_system.is_surjective (ComplInfComp G Gpc) :=
begin
  dsimp [Endsinfty],
  rw ComplInfComp_eq_ComplComp_to_surjective,
  by_cases hfin : finite V,
  { haveI := hfin,
    rintro i j h x,
    let jempty := all_empty  G Gpc j,
    rw ComplInfComp_eq_ComplComp_to_surjective at jempty,
    exfalso,
    exact is_empty_iff.mp jempty x, },
  { haveI : infinite V := infinite.of_not_finite hfin,
    exact @inverse_system.to_surjective.is_surjective _ _ _ (ComplComp G Gpc) _ (ComplComp_nonempty G Gpc), },
end

lemma Endsinfty_surjective : Π (j : (finset V)), function.surjective (λ e : Endsinfty G Gpc, e.val j) :=
begin
  rintro j,
  dsimp [Endsinfty],
  have := ComplInfComp.surjective G Gpc,
  rw inverse_system.is_surjective_iff at this,
  apply inverse_system.sections_surjective,
  rintro i h, exact this i j h,
end

lemma Endsinfty_eventually_constant
  (K : finset V)
  (top : Π (L : finset V) (KL : L ≤ K), (ComplInfComp G Gpc).obj L ≃ (ComplInfComp G Gpc).obj K) :
  Endsinfty G Gpc ≃ (ComplInfComp G Gpc).obj K :=
begin

  by_cases hfin : finite V, rotate,
  { haveI : infinite V := infinite.of_not_finite hfin,
    haveI :  Π (j : (finset V)), nonempty ((ComplComp G Gpc).obj j), from ComplComp_nonempty G Gpc,
    apply equiv.of_bijective _ (inverse_system.sections_bijective (ComplInfComp G Gpc) K _),
    rintros ⟨L,KL⟩,
    have sur : function.surjective ((ComplInfComp G Gpc).map (hom_of_le KL)), by {
      rw (ComplInfComp_eq_ComplComp_to_surjective G Gpc),
      rintros a,
      exact (inverse_system.to_surjective.is_surjective (ComplComp G Gpc) L K KL a),
    },
    split, rotate,
    { exact sur },
    { exact (fintype.injective_iff_surjective_of_equiv (top L KL)).mpr sur },},
  { -- degenerate case: If V is finite, then everything is empty,
    haveI := hfin,
    have :  Π (j : (finset V)), is_empty ((ComplInfComp G Gpc).obj j), from all_empty G Gpc,
    apply equiv.of_bijective,
    apply inverse_system.sections_bijective (ComplInfComp G Gpc),
    rintro ⟨L,KL⟩,
    -- Have to show that a map A → B with both A and B empty is necessarily a bijection.
    unfold function.bijective, split,
    { rintro x, exact (this L).elim x,},
    { rintro y, exact (this K).elim y,},}
end
