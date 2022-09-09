import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic

import .comp_out
import .for_mathlib.fintype_inverse_systems

open category_theory
open opposite
open simple_graph
open classical
open simple_graph.comp_out

/- Implementing Kyle Miller's suggestion:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Geometric.20group.20theory/near/290624806 -/

/--!

## Ends of a graph

One way to define ends in a graph is via [havens](https://en.wikipedia.org/wiki/End_(graph_theory)#Definition_and_characterization).
An `end` is defined as a function that takes in a finite set and returns a connected component in its complement. The constraint on
this function is that it chooses the connected components consistently, i.e., if `K` and `L` are finite sets with `K` contained in `L`, then
the component chosen for `L` must be contained in the component chosen for `K`.

## An inverse system of sets

The ends also lend themselves to a more categorical description, detailed in the message by Kyle Miller above.
One can consider the poset of finite subsets of the vertex set `V` under inclusion as a category, and a functor to **Type** that
assigns to each finite set the set of connected components in its complement and to each morphism the "backward map" of
connected components (i.e., the map `back` taking each component outside a set to the unique component outside a given subset that contains it).

When the graph is infinite and locally finite, the set of connected components outside a finite set of vertices is always non-empty and finite.
It follows from general category theory that the limit of an inverse system of non-empty and finite sets exists and is a non-empty set.

## Defining ends as the sections of a functor

Each element in the limit corresponds to a section of the functor, and vice versa.

It turns out that every element in the limit set also determines an end - the component outside a given finite set is given by
the value of the element under the corresponding projection, and the assignment of connected components is consistent by the definition of a limit.

-/

noncomputable theory
local attribute [instance] prop_decidable

universes u v w
variables {V : Type u} [decidable_eq V]
variables (G : simple_graph V) (Glf : locally_finite G) (Gpc : preconnected G)


-- Defined backwards for simpler use of `mathlib_fintype_inverse_systems.lean`
instance finset_preorder : preorder (finset V) := {
  le := λ A B, A ⊇ B,
  lt := λ A B, A ⊃ B,
  le_refl := by obviously,
  le_trans := by obviously,
  lt_iff_le_not_le := by {dsimp only [superset,ssuperset],obviously,}
  }

/-- The category of finite subsets of `V` with the morphisms being inclusions -/
instance FinIncl : category (finset V) := infer_instance

instance finset_directed : is_directed (finset V) (≥) := {
  directed := λ A B, ⟨A ∪ B, ⟨finset.subset_union_left A B, finset.subset_union_right A B⟩⟩ }

/-- The functor assigning a finite set in `V` to the set of connected components in its complement-/
def ComplComp : finset V ⥤ Type u := {
  obj := λ A, dis_comp_out G A,
  map := λ _ _ f, dis_comp_out.back (le_of_hom f),
  map_id' := by {intro, funext, simp only [types_id_apply],apply dis_comp_out.back_refl_apply, },
  map_comp' := by {intros, funext, simp only [types_comp_apply], symmetry, apply dis_comp_out.back_trans_apply, },
}

/-- The ends of a graph, defined as the sections of the functor. -/
def Ends := (ComplComp G).sections

/-- A modified definition assigning each set to the *infinite* connected components outside it.
    The two notions of ends coincide, as shown below.
 -/
def ComplInfComp : finset V ⥤ Type u :=
  (ComplComp G).subfunctor
    (λ K, {C : G.dis_comp_out K | C.val.inf})
    (by {intros _ _ _, apply dis_comp_out.back_of_inf,})

-- The slightly modified notion of ends
def Endsinfty := (ComplInfComp G).sections

lemma ComplInfComp.obj : ∀ K : finset V, (ComplInfComp G).obj K = G.inf_comp_out K := by {intro, refl,}

lemma ComplInfComp.map : ∀ {K L : finset V}, ∀ f : K ⟶ L, (ComplInfComp G).map f = inf_comp_out.back (le_of_hom f) := by {intros, ext ⟨_, _⟩, refl,}

-- (see `to_surjective`)
lemma ComplInfComp_eq_ComplComp_to_surjective : ComplInfComp G = inverse_system.to_surjective (ComplComp G) :=
begin
  apply functor.subfunctor.ext,
  dsimp [ComplComp], intro K, ext C,
  show C.val.inf ↔ C ∈ (⋂ (i : {L // K ⊆ L}), _), split,
  { rintro Cinf, simp, rintro L KsubL,
    obtain ⟨D, Ddis, hback⟩ := in_all_ranges_of_inf _ Cinf KsubL,
    use D,
    exact Ddis,
    have := back_sub KsubL D,
    rw [hback] at this,
    exact this, },
  { -- use inf_of_in_all_ranges
    rintro h,
    simp at h,
    apply inf_of_in_all_ranges,
    intros L KsubL,
    obtain ⟨⟨D, Ddis⟩, hyp⟩ := h L KsubL,
    use D,
    split,
    exact Ddis,
    simp only [subtype.val_eq_coe, eq_back_iff_sub],
    exact hyp,},
end

lemma Ends_equiv_Endsinfty : Ends G ≃ Endsinfty G :=
begin
  dsimp [Ends,Endsinfty],
  rw ComplInfComp_eq_ComplComp_to_surjective,
  apply inverse_system.to_surjective.sections_equiv,
end

include Gpc Glf
instance ComplComp_nonempty [infinite V] :  ∀ (j : (finset V)), nonempty ((ComplComp G).obj j) := by {
  intro K, dsimp only [ComplComp],
  --refine nonempty.map subtype.val _,
  --rotate,
  obtain ⟨C,Cinf⟩ := comp_out.exists_inf G K Gpc Glf,
  constructor,
  use [C,comp_out.dis_of_inf C Cinf], }

instance ComplComp_fintype : Π (j : (finset V)), fintype ((ComplComp G).obj j) := by
{ intro,
  dsimp only [ComplComp],
  haveI := @fintype.of_finite (G.comp_out j) (comp_out_finite G j Gpc Glf),
  apply subtype.fintype, }

instance ComplInfComp_nonempty [infinite V] : Π (j : (finset V)), nonempty ((ComplInfComp G).obj j) := by
{ intro K, dsimp only [ComplComp],

  obtain ⟨C,Cinf⟩ := comp_out.exists_inf G K Gpc Glf,
  constructor,
  use [C,comp_out.dis_of_inf C Cinf, Cinf],}

instance ComplInfComp_fintype : Π (j : (finset V)), fintype ((ComplInfComp G).obj j) := by
{ intro K, rw ComplInfComp.obj,
  haveI := @fintype.of_finite (G.comp_out K) (comp_out_finite G K Gpc Glf),
  have dis_fin := subtype.fintype (λ (C : G.comp_out K), C.dis),
  change fintype (G.dis_comp_out K) at dis_fin,
  haveI := dis_fin,
  apply subtype.fintype, }


omit Glf Gpc
lemma all_empty [finite V] : ∀ (K : finset V), is_empty ((ComplInfComp G).obj K) :=
begin
  rintro K,
  by_contra h, rw not_is_empty_iff at h,
  obtain ⟨⟨C,Cdis⟩,Cinf⟩ := h,
  simp at Cinf,
  have : (@set.univ V).finite := (@set.univ V).to_finite,
  exact set.infinite.mono (by {simp only [set.subset_univ],} : (C : set V) ⊆ set.univ) Cinf this,
end

include Glf Gpc
lemma ComplInfComp.surjective : inverse_system.is_surjective (ComplInfComp G) :=
begin
  dsimp [Endsinfty],
  rw ComplInfComp_eq_ComplComp_to_surjective,
  by_cases hfin : finite V,
  { haveI := hfin,
    rintro i j h x,
    let jempty := all_empty  G j,
    rw ComplInfComp_eq_ComplComp_to_surjective at jempty,
    exact jempty.elim x, },
  { haveI : infinite V := infinite.of_not_finite hfin,
    haveI := ComplComp_fintype G Glf Gpc,
    haveI := ComplComp_nonempty G Glf Gpc,
    exact inverse_system.to_surjective.is_surjective (ComplComp G), },
end

lemma inf_comp_out.back_surjective {K L : finset V} (h : K ⊆ L) :
  function.surjective (@inf_comp_out.back V G K L h) :=
begin
  have := ComplInfComp.surjective G Glf Gpc,
  rw inverse_system.is_surjective_iff at this,
  specialize this L K h,
  rw ComplInfComp.map G ((hom_of_le h) : L ⟶ K) at this,
  exact this,
end

lemma Endsinfty_surjective : Π (j : (finset V)), function.surjective (λ e : Endsinfty G, e.val j) :=
begin
  rintro j,
  dsimp [Endsinfty],
  have := ComplInfComp.surjective G Glf Gpc,
  haveI := ComplInfComp_fintype G Glf Gpc,
  rw inverse_system.is_surjective_iff at this,
  apply inverse_system.sections_surjective,
  rintro i h, exact this i j h,
end





lemma Endsinfty_eventually_constant
  (K : finset V)
  (top : Π (L : finset V) (KL : L ≤ K), (ComplInfComp G).obj L ≃ (ComplInfComp G).obj K) :
  Endsinfty G ≃ (ComplInfComp G).obj K :=
begin

  by_cases hfin : finite V, rotate,
  { haveI : infinite V := infinite.of_not_finite hfin,
    haveI := ComplComp_nonempty G Glf Gpc,
    haveI := ComplComp_fintype G Glf Gpc,
    haveI := ComplInfComp_fintype G Glf Gpc,

    apply equiv.of_bijective _ (inverse_system.sections_bijective (ComplInfComp G) K _),
    rintros ⟨L,KL⟩,
    have sur : function.surjective ((ComplInfComp G).map (hom_of_le KL)), by {
      rw (ComplInfComp_eq_ComplComp_to_surjective G),
      rintros a,
      exact (inverse_system.to_surjective.is_surjective (ComplComp G) L K KL a),
    },
    split, rotate,
    { exact sur },
    { exact (fintype.injective_iff_surjective_of_equiv (top L KL)).mpr sur },},
  { -- degenerate case: If V is finite, then everything is empty,
    haveI := hfin,
    have :  Π (j : (finset V)), is_empty ((ComplInfComp G).obj j), from all_empty G,
    apply equiv.of_bijective,
    apply inverse_system.sections_bijective (ComplInfComp G),
    rintro ⟨L,KL⟩,
    -- Have to show that a map A → B with both A and B empty is necessarily a bijection.
    unfold function.bijective, split,
    { rintro x, exact (this L).elim x,},
    { rintro y, exact (this K).elim y,},}
end
