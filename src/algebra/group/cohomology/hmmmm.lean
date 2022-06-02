import topology.category.Profinite.as_limit
import algebra.group.cohomology.sles
universes v u

namespace stuff
variables (G : Type u) [topological_space G] [group G] [topological_group G]
  (A : Type u) [topological_space A] [discrete_topology A] [add_comm_group A]
  [distrib_mul_action G A] [has_continuous_smul G A]

---- uhh why doesn't this exist... even as a def
instance hmm : topological_add_group A :=
{ continuous_add := continuous_of_discrete_topology,
  continuous_neg := continuous_of_discrete_topology }

def cts_cochain (n : ℕ) : add_subgroup ((fin n → G) → A) :=
{ carrier := {f | continuous f },
  add_mem' := λ f g, continuous.add,
  zero_mem' := @continuous_zero (fin n → G) A _ _ _,
  neg_mem' := λ f, continuous.neg }

variables {G A}

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

variables (G A)
def d_of_cts (n : ℕ) : cts_cochain G A n →+ cts_cochain G A (n + 1) :=
((cochain.d G A n).comp (cts_cochain G A n).subtype).cod_restrict _ $
λ x, continuous.add (continuous.smul (continuous_apply _) (continuous.comp x.2
  (continuous_pi (λ i, continuous_apply _)))) (continuous_finset_sum _ (λ i H,
  continuous.const_smul (continuous.comp x.2 (continuous_F n
    (⟨i, finset.mem_range.1 H⟩ : fin (n + 1)))) _))

lemma d_of_cts_square_zero (n : ℕ) :
  (d_of_cts G A (n + 1)).comp (d_of_cts G A n) = 0 :=
begin
  ext1, ext1,
  exact d_to_fun_square_zero (x : (fin n → G) → A),
end

lemma d_of_cts_square_apply (n : ℕ) (x : cts_cochain G A n) :
  d_of_cts G A (n + 1) (d_of_cts G A n x) = 0 :=
by ext1; exact d_to_fun_square_zero _

def cts_cochain_cx : cochain_complex Ab ℕ :=
cochain_complex.of (λ n, AddCommGroup.of $ cts_cochain G A n) (λ n, d_of_cts G A n)
  (λ n, by { ext1, ext1, exact d_to_fun_square_zero _ })

variables {G A} {H : Type u} [topological_space H] [group H] [topological_group H]
  {B : Type u} [topological_space B] [discrete_topology B] [add_comm_group B]
  [distrib_mul_action H B] [has_continuous_smul H B]

lemma pair_chain_map_aux_cts (f : G →* H) (hf : continuous f) (φ : B →+ A) (n : ℕ) (x : cts_cochain H B n) :
  continuous (pair_chain_map_aux f φ n x) :=
continuous.comp continuous_of_discrete_topology $ continuous.comp x.2 (continuous_pi
(λ i, continuous.comp hf (continuous_apply _)))

@[simps] def cts_pair_chain_map_aux (f : G →* H) (hf : continuous f) (φ : B →+ A) (n : ℕ) :
  (cts_cochain H B n) →+ (cts_cochain G A n) :=
((pair_chain_map_aux f φ n).comp (cts_cochain H B n).subtype).cod_restrict _
  (pair_chain_map_aux_cts f hf φ n)

  lemma cts_pair_chain_map_aux_comm (f : G →* H) (hf : continuous f) (φ : B →+ A)
    (hp : pair f φ) (n : ℕ) :
  (d_of_cts G A n).comp (cts_pair_chain_map_aux f hf φ n)
    = (cts_pair_chain_map_aux f hf φ (n + 1)).comp (d_of_cts H B n) :=
begin
  ext1, ext1,
  exact add_monoid_hom.ext_iff.1 (pair_chain_map_aux_comm f φ hp n) x,
end

def cts_pair_chain_map (f : G →* H) (hf : continuous f) (φ : B →+ A) (hp : pair f φ) :
  cts_cochain_cx H B ⟶ cts_cochain_cx G A :=
{ f := λ i, cts_pair_chain_map_aux f hf φ i,
  comm' := λ i j hij, by
  { cases hij,
    dsimp,
    erw [cochain_complex.of_d, cochain_complex.of_d],
    convert cts_pair_chain_map_aux_comm f hf φ hp i }}

noncomputable def cts_pair_homology_map (f : G →* H) (hf : continuous f) (φ : B →+ A)
  (hp : pair f φ) (n : ℕ) : (cts_cochain_cx H B).homology n →+ (cts_cochain_cx G A).homology n :=
(homology_functor _ _ n).map (cts_pair_chain_map f hf φ hp)


end stuff
