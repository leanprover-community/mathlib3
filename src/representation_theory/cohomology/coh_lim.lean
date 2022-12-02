import representation_theory.cohomology.hmmmm
import representation_theory.cohomology.profiniteummmmmmmm
universes v u
namespace stuff
variables {k : Type u} [comm_ring k] {G : ProfiniteGroup.{u}}
  {V : Type u} [topological_space V] [discrete_topology V] [add_comm_group V] [module k V]
  {ρ : representation k G V} (hρ : ∀ v : V, continuous (λ g : G, ρ g v)) (n : ℕ)


noncomputable theory
open_locale classical
open discrete_quotient_group

variables (S T : open_normal G) (hST : S ≤ T)

def coh_lim_aux : (cochain_cx (inf_rep ρ ↑S)).homology n →ₗ[k] (cochain_cx (inf_rep ρ ↑T)).homology n :=
(homology_functor (Module k) _ n).map (pair_chain_map _ _
  (quotient_group.map _ _ (monoid_hom.id G) (λ x hx, hST hx)) (submodule.of_le $
  λ x hx g, hx (⟨g, hST g.2⟩ : S)) $ λ g x, quotient_group.induction_on g (λ b, rfl))

open representation

abbreviation coh_lim (hρ : ∀ v : V, continuous (λ g : G, ρ g v)) :=
@module.direct_limit k _ (open_normal G) _ _
 (λ U, (cochain_cx (inf_rep ρ (U : subgroup G))).homology n) (λ n, by apply_instance)
 (λ n, by apply_instance) (λ S T hST, coh_lim_aux n _ _ hST)

open category_theory

variables (U : open_normal G)

def to_cts_coh_aux :
  (cochain_cx (inf_rep ρ U)).X n →ₗ[k] cts_cochain.{u u u} k G V n :=
linear_map.cod_restrict _ ((pair_chain_map ρ (inf_rep ρ U) (quotient_group.mk' U) (submodule.subtype _)
    (λ g x, rfl)).f n) $
begin
  intro c,
  haveI := discrete_quotient_of_open_subgroup (U : subgroup G) U.2.1,
  exact (continuous_of_discrete_topology).comp (continuous_of_discrete_topology.comp
    (continuous_pi (λ i, continuous_quot_mk.comp (continuous_apply _)))),
end

variables (f : (cochain_cx (inf_rep ρ U)).X n) (x : fin n → G)
#exit
#check (to_cts_coh_aux n U f).1
lemma to_cts_coh_aux_apply :
  (to_cts_coh_aux n U f : (fin n → G) → V) x = f (coe ∘ x) :=
rfl
#check Module.as_hom
lemma to_cts_coh_aux_comm :
   ((cochain_cx (inf_rep ρ U)).d (n + 1) n) ≫ (@Module.as_hom.{u u u} k _ _ _ _ _ _ _ (to_cts_coh_aux n U)) =
  (@Module.as_hom.{u u u} k _ _ _ _ _ _ _ (to_cts_coh_aux (n + 1) U)) ≫ ((cts_cochain_cx ρ hρ).d (n + 1) n) :=
begin
  ext f x,
  dsimp,
  rw to_cts_coh_aux_apply,
  dunfold cts_cochain_cx d_of_cts cochain_cx,
  dsimp,
  erw cochain_complex.of_d,
  rw cochain_complex.of_d,


end

#exit
linear_map.cod_restrict _ ((((invariants (ρ.comp (U : subgroup G).subtype)).subtype.comp
  (invariants (inf_rep ρ U)).subtype).comp_left
  (fin n → G)).comp (linear_map.fun_left k (invariants (inf_rep ρ U))
  (λ f : fin n → G, (quotient_group.mk : G → G ⧸ (U : subgroup G)) ∘ f))) $
begin
  intros,
  dsimp,
  show continuous _,

end
--linear_map.cod_restrict _ (linear_map.comp_left (submodule.subtype _) _).comp (linear_map.fun_left k _ (λ f, _)) _


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
