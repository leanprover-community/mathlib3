import representation_theory.cohomology.hmmmm
import topology.category.Profinite.as_limit
namespace stuff
variables {k : Type*} [comm_ring k] {G : Profinite} [group G] [topological_group G]
  {V : Type*} [topological_space V] [discrete_topology V] [add_comm_group V] [module k V]
  (ρ : representation k G V) (h : ∀ v : V, continuous (λ g : G, ρ g v)) (n : ℕ)

noncomputable theory
open_locale classical

abbreviation open_normal (G : Profinite) [group G] [topological_group G] :=
@subtype (subgroup G) (λ U, is_open (U : set G) ∧ U.normal)

instance open_normal_normal (U : open_normal G) : (U : subgroup G).normal := U.2.2
instance : preorder (open_normal G) := by apply_instance

abbreviation coh_lim := @module.direct_limit k _ (open_normal G) _ _
 (λ U, cts_coh (inf_rep ρ (U : subgroup G)) n) (λ n, by apply_instance) (λ n, by apply_instance)
 (λ S T hST, 0) -- can't define the map because of weird error -___-

lemma goal : cts_coh ρ n ≃ₗ[k] coh_lim ρ n := sorry

lemma goal2 : cts_coh ρ n ≃ₗ[k] (cochain_cx ρ).homology n := sorry

end stuff
