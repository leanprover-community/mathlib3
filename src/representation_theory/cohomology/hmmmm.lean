import topology.category.Profinite.as_limit
import representation_theory.cohomology.sles

universes v u

namespace stuff
variables {k : Type*} [comm_ring k] {G : Type u} [topological_space G] [group G] [topological_group G]
  {V : Type v} [topological_space V] [discrete_topology V] [add_comm_group V] [module k V]
  (ρ : representation k G V) (hρ : ∀ v : V, continuous (λ g : G, ρ g v))

variables (k G V)

def cts_cochain (n : ℕ) : submodule k ((fin n → G) → V) :=
{ carrier := {f | continuous f },
  add_mem' := λ f g, continuous.add,
  zero_mem' := @continuous_zero (fin n → G) V _ _ _,
  smul_mem' := λ r x hx, @continuous.const_smul _ _ _ _ _ (⟨λ r, continuous_of_discrete_topology⟩) _ _ hx r }

lemma continuous_F (n : ℕ) (i : fin (n + 1)) :
  continuous (λ g : fin (n + 1) → G, F i g) :=
begin
  refine continuous_pi (λ j, _),
  dunfold F,
  split_ifs,
  { exact continuous_apply _ },
  { exact continuous.mul (continuous_apply _) (continuous_apply _), },
  { exact continuous_apply _ }
end

variables {k G V}

instance : has_continuous_const_smul k V :=
⟨λ r, continuous_of_discrete_topology⟩

lemma continuous_ρ_apply (g : G) : continuous (ρ g) := continuous_of_discrete_topology

include hρ

def d_of_cts (n : ℕ) :
  cts_cochain k G V n →ₗ[k] cts_cochain k G V (n + 1) :=
((cochain.d ρ n).comp (cts_cochain k G V n).subtype).cod_restrict _ $
λ x, (@continuous.comp₂ _ _ _ _ _ _ _ _ (λ g, ρ g.1 $ (cts_cochain k G V n).subtype x g.2)
  (((continuous_uncurry_of_discrete_topology_left hρ).comp
    continuous_swap).comp (continuous_id.prod_map x.2)) (λ g : fin (n + 1) → G, g 0)
  (continuous_apply 0) (λ (x : fin (n + 1) → G) (i : fin n), x ((fin.add_nat 1) i))
  (continuous_pi (λ i, continuous_apply _))).add (continuous_finset_sum _
  (λ i H, (x.2.comp (continuous_F G n (⟨i, finset.mem_range.1 H⟩ : fin (n + 1)))).const_smul _))

lemma d_of_cts_square_zero (n : ℕ) :
  (d_of_cts ρ hρ (n + 1)).comp (d_of_cts ρ hρ n) = 0 :=
begin
  ext1, ext1,
  exact d_to_fun_square_zero ρ (x : (fin n → G) → V),
end

lemma d_of_cts_square_apply (n : ℕ) (x : cts_cochain k G V n) :
  d_of_cts ρ hρ (n + 1) (d_of_cts ρ hρ n x) = 0 :=
by ext1; exact d_to_fun_square_zero _ _

def cts_cochain_cx : cochain_complex (Module k) ℕ :=
cochain_complex.of (λ n, Module.of k $ cts_cochain k G V n) (λ n, d_of_cts ρ hρ n)
  (λ n, by { ext1, ext1, exact d_to_fun_square_zero _ _ })

noncomputable abbreviation cts_coh (n : ℕ) := (cts_cochain_cx ρ hρ).homology n

variables {k ρ} {H : Type u} [topological_space H] [group H] [topological_group H]
  {W : Type v} [topological_space W] [discrete_topology W] [add_comm_group W]
  [module k W] {τ : representation k H W} (hτ : ∀ w : W, continuous (λ g : H, τ g w))

include hτ

lemma pair_chain_map_aux_cts (f : G →* H) (hf : continuous f)
  (φ : W →ₗ[k] V) (n : ℕ) (x : cts_cochain k H W n) :
  continuous (pair_chain_map_aux k f φ n x) :=
continuous_of_discrete_topology.comp $ x.2.comp (continuous_pi (λ i, hf.comp (continuous_apply _)))

def cts_pair_chain_map_aux (f : G →* H) (hf : continuous f) (φ : W →ₗ[k] V) (n : ℕ) :
  (cts_cochain k H W n) →ₗ[k] (cts_cochain k G V n) :=
((pair_chain_map_aux k f φ n).comp (cts_cochain k H W n).subtype).cod_restrict _
  (pair_chain_map_aux_cts hρ hτ _ hf _ _)

variables {k}

  lemma cts_pair_chain_map_aux_comm (f : G →* H) (hf : continuous f) (φ : W →ₗ[k] V)
    (hp : pair ρ τ f φ) (n : ℕ) :
  (d_of_cts ρ hρ n).comp (cts_pair_chain_map_aux hρ hτ f hf φ n)
    = (cts_pair_chain_map_aux hρ hτ f hf φ (n + 1)).comp (d_of_cts τ hτ n) :=
begin
  ext1, ext1,
  exact linear_map.ext_iff.1 (pair_chain_map_aux_comm ρ τ f φ hp n) x,
end

def cts_pair_chain_map (f : G →* H) (hf : continuous f) (φ : W →ₗ[k] V) (hp : pair ρ τ f φ) :
  cts_cochain_cx τ hτ ⟶ cts_cochain_cx ρ hρ :=
{ f := λ i, cts_pair_chain_map_aux hρ hτ f hf φ i,
  comm' := λ i j hij, by
  { cases hij,
    dsimp,
    erw [cochain_complex.of_d, cochain_complex.of_d],
    convert cts_pair_chain_map_aux_comm hρ hτ f hf φ hp i }}

noncomputable def cts_coh_map (f : G →* H) (hf : continuous f) (φ : W →ₗ[k] V)
  (hp : pair ρ τ f φ) (n : ℕ) : cts_coh τ hτ n →ₗ[k] cts_coh ρ hρ n :=
(homology_functor _ _ n).map (cts_pair_chain_map _ _ f hf φ hp)

end stuff
