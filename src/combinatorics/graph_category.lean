import combinatorics.simple_graph
import category_theory.category
import category_theory.concrete_category


universes v u

--namespace simple_graph

--variables (V : Type v) (U : Type u) (G : simple_graph_on V) (G' : simple_graph_on U)

/-
A graph homomorphism is a map on vertex sets that respects the adjacency relations.

@[ext]
structure homomorphism' :=
(to_fun : simple_graph.U G → simple_graph.U G')
(map_adj' : ∀ {x y : simple_graph.V G}, x ~g y → to_fun x ~g to_fun y)-/

--end simple_graph

open category_theory


def SimpleGraph := bundled simple_graph_on

/-- The category of simple graphs and graph homomorphisms. -/
add_decl_doc SimpleGraph

namespace SimpleGraph

/-instance bundled_hom : bundled_hom @simple_graph.homomorphism :=
⟨@monoid_hom.to_fun, @monoid_hom.id, @monoid_hom.comp, @monoid_hom.coe_inj⟩-/

--attribute [derive [has_coe_to_sort, large_category, concrete_category]] SimpleGraph

/-instance bundled_hom : bundled_hom @simple_graph.homomorphism :=
⟨@ring_hom.to_fun, @ring_hom.id, @ring_hom.comp, @ring_hom.coe_inj⟩-/

/-instance category : large_category.{max v u} Groupoid.{v u} :=
{ hom := λ C D, C.α ⥤ D.α,
  id := λ C, 𝟭 C.α,
  comp := λ C D E F G, F ⋙ G,
  id_comp' := λ C D F, by cases F; refl,
  comp_id' := λ C D F, by cases F; refl,
  assoc' := by intros; refl }-/


end SimpleGraph
