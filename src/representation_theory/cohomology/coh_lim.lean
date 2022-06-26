#exit
import representation_theory.cohomology.hmmmm
import topology.category.Profinite.as_limit
namespace stuff
variables {k : Type*} [comm_ring k] {G : Profinite} [group G] [topological_group G]
  {V : Type*} [topological_space V] [discrete_topology V] [add_comm_group V] [module k V]
  (ρ : representation k G V) (h : ∀ v : V, continuous (λ g : G, ρ g v)) (n : ℕ)

noncomputable theory
open_locale classical

abbreviation open_normal (G : Profinite) [group G] [topological_group G] :=
order_dual $ @subtype (subgroup G) (λ U, is_open (U : set G) ∧ U.normal)

instance : has_coe (open_normal G) (subgroup G) :=
⟨λ U, U.1⟩

instance open_normal_normal (U : open_normal G) : (U : subgroup G).normal := U.2.2
--instance : preorder (open_normal G) := by apply_instance

variables (S T : open_normal G) (hST : S ≤ T)

def coh_lim_aux : (cochain_cx (inf_rep ρ ↑S)).homology n →ₗ[k] (cochain_cx (inf_rep ρ ↑T)).homology n :=
(homology_functor (Module k) _ n).map (pair_chain_map _ _
  (quotient_group.map _ _ (monoid_hom.id G) (λ x hx, hST hx)) (submodule.of_le $
  λ x hx g, hx (⟨g, hST g.2⟩ : S)) $ λ g x, quotient_group.induction_on g (λ b, rfl))

open representation

abbreviation coh_lim := @module.direct_limit k _ (open_normal G) _ _
 (λ U, (cochain_cx (inf_rep ρ (U : subgroup G))).homology n) (λ n, by apply_instance)
 (λ n, by apply_instance) (λ S T hST, coh_lim_aux ρ n _ _ hST)

--#check homology.desc
def fdjgfd (U : open_normal G) (x : (cochain.d (inf_rep ρ (U : subgroup G)) n).ker) :
  (d_of_cts ρ n).ker :=
⟨⟨λ f, x.1 (quotient.mk' ∘ f), _⟩, _⟩

#check homological_complex.d_to_comp_d_from
def inv_map_aux (U : open_normal G) :
  (cochain_cx (inf_rep ρ (U : subgroup G))).homology n →ₗ[k] cts_coh ρ n :=
homology.desc _ _ ((cochain_cx (inf_rep ρ (U : subgroup G))).d_to_comp_d_from _) _ _

#exit
def inv_map : coh_lim ρ n →ₗ[k] cts_coh ρ n :=
module.direct_limit.lift k (open_normal G) _ _ (λ U, _) _

lemma goal : cts_coh ρ n ≃ₗ[k] coh_lim ρ n := sorry

lemma goal2 : cts_coh ρ n ≃ₗ[k] (cochain_cx ρ).homology n := sorry

end stuff
