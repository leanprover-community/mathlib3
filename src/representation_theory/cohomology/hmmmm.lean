import topology.category.Profinite.as_limit
import representation_theory.cohomology.sles

universes v u

namespace stuff
variables {k : Type*} [comm_ring k] {G : Type u} [topological_space G] [group G] [topological_group G]
  {V : Type v} [topological_space V] [discrete_topology V] [add_comm_group V] [module k V]
  (ρ : representation k G V) (h : ∀ v : V, continuous (λ g : G, ρ g v))

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

def d_of_cts (n : ℕ) : cts_cochain k G V n →ₗ[k] cts_cochain k G V (n + 1) :=
((cochain.d ρ n).comp (cts_cochain k G V n).subtype).cod_restrict _ $
λ x, continuous.add sorry sorry
/-(continuous.smul (continuous_apply _) (continuous.comp x.2
  (continuous_pi (λ i, continuous_apply _)))) (continuous_finset_sum _ (λ i H,
  continuous.const_smul (continuous.comp x.2 (continuous_F k G V n
    (⟨i, finset.mem_range.1 H⟩ : fin (n + 1)))) _))-/

lemma d_of_cts_square_zero (n : ℕ) :
  (d_of_cts ρ (n + 1)).comp (d_of_cts ρ n) = 0 :=
begin
  ext1, ext1,
  exact d_to_fun_square_zero ρ (x : (fin n → G) → V),
end

lemma d_of_cts_square_apply (n : ℕ) (x : cts_cochain k G V n) :
  d_of_cts ρ (n + 1) (d_of_cts ρ n x) = 0 :=
by ext1; exact d_to_fun_square_zero _ _

def cts_cochain_cx : cochain_complex (Module k) ℕ :=
cochain_complex.of (λ n, Module.of k $ cts_cochain k G V n) (λ n, d_of_cts ρ n)
  (λ n, by { ext1, ext1, exact d_to_fun_square_zero _ _ })

noncomputable abbreviation cts_coh (n : ℕ) := (cts_cochain_cx ρ).homology n

variables {H : Type u} [topological_space H] [group H] [topological_group H]
  {W : Type v} [topological_space W] [discrete_topology W] [add_comm_group W]
  [module k W] (τ : representation k H W) (hW : ∀ w : W, continuous (λ g : H, τ g w))

lemma pair_chain_map_aux_cts (f : G →* H) (hf : continuous f) (φ : W →ₗ[k] V) (n : ℕ)
  (x : cts_cochain k H W n) :
  continuous (pair_chain_map_aux ρ τ f φ n x) :=
continuous.comp continuous_of_discrete_topology $ continuous.comp x.2 (continuous_pi
(λ i, continuous.comp hf (continuous_apply _)))

def cts_pair_chain_map_aux (f : G →* H) (hf : continuous f) (φ : W →ₗ[k] V) (n : ℕ) :
  (cts_cochain k H W n) →ₗ[k] (cts_cochain k G V n) :=
((pair_chain_map_aux ρ τ f φ n).comp (cts_cochain k H W n).subtype).cod_restrict _
  (pair_chain_map_aux_cts ρ τ f hf φ n)

  lemma cts_pair_chain_map_aux_comm (f : G →* H) (hf : continuous f) (φ : W →ₗ[k] V)
    (hp : pair ρ τ f φ) (n : ℕ) :
  (d_of_cts ρ n).comp (cts_pair_chain_map_aux ρ τ f hf φ n)
    = (cts_pair_chain_map_aux ρ τ f hf φ (n + 1)).comp (d_of_cts τ n) :=
begin
  ext1, ext1,
  exact linear_map.ext_iff.1 (pair_chain_map_aux_comm ρ τ f φ hp n) x,
end
.

def cts_pair_chain_map (f : G →* H) (hf : continuous f) (φ : W →ₗ[k] V) (hp : pair ρ τ f φ) :
  cts_cochain_cx τ ⟶ cts_cochain_cx ρ :=
{ f := λ i, cts_pair_chain_map_aux ρ τ f hf φ i,
  comm' := λ i j hij, by
  { cases hij,
    dsimp,
    erw [cochain_complex.of_d, cochain_complex.of_d],
    convert cts_pair_chain_map_aux_comm f hf φ hp i }}

#exit

noncomputable def cts_pair_homology_map (f : G →* H) (hf : continuous f) (φ : B →+ A)
  (hp : pair f φ) (n : ℕ) : (cts_cochain_cx H B).homology n →+ (cts_cochain_cx G A).homology n :=
(homology_functor _ _ n).map (cts_pair_chain_map f hf φ hp)


end stuff
