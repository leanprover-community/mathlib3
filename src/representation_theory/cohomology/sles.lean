#exit
import representation_theory.cohomology.wabagoosa
-- ("short long exact sequence")
universes v u

variables {k : Type*} [comm_ring k] {G : Type*} [group G]
noncomputable theory

namespace stuff

#exit
def one_cocycles_map {M N : Type*} [add_comm_group M] [add_comm_group N]
  [module k M] [module k N] (ρ : representation k G M) (τ : representation k G N)
  (f : M →ₗ[k] N) (hp : pair τ ρ (monoid_hom.id G) f) :
  one_cocycles ρ →ₗ[k] one_cocycles τ :=
((f.comp_left G).comp (one_cocycles ρ).subtype).cod_restrict _ $ λ x,
begin
  intros g h,
  dsimp,
  sorry, --norm_cast,
  --rw [one_cocycles_map_mul, f.map_add, f.map_smul],
  --abel,
end

variables {M N : Type*} [add_comm_group M] [add_comm_group N]
  [module k M] [module k N] (ρ : representation k G M) (τ : representation k G N)
  (f : M →ₗ[k] N) (hp : pair τ ρ (monoid_hom.id G) f)

#check cohomology_map ρ τ

#exit
def firstcoh_map {M N : Type*} [add_comm_group M] [add_comm_group N]
  [module k M] [module k N] (ρ : representation k G M) (τ : representation k G N)
  (f : M →ₗ[k] N) (hp : pair τ ρ (monoid_hom.id G) f) :
  firstcoh ρ →ₗ[k] firstcoh τ :=
((first_iso τ).to_linear_map.comp (cohomology_map _ _ f hp 1)).comp (first_iso ρ).symm.to_linear_map

lemma firstcoh_map_apply {M N : Type*} [add_comm_group M] [add_comm_group N]
  [module k M] [module k N] (ρ : representation k G M) (τ : representation k G N)
  (f : M →ₗ[k] N) (hp : pair τ ρ (monoid_hom.id G) f) (x : one_cocycles ρ) (g : G) :
  firstcoh_map _ _ f hp x = quotient.mk' (one_cocycles_map _ _ f hp x) := sorry

-- here we go...
variables {M N P : Type*} [add_comm_group M] [add_comm_group N] [add_comm_group P]
  [module k M] [module k N] [module k P] (ρ : representation k G M)
  (τ : representation k G N) (σ : representation k G P)
  (f : M →ₗ[k] N) (g : N →ₗ[k] P)
  (hf : pair τ ρ (monoid_hom.id G) f) (hg : pair σ τ (monoid_hom.id G) g)
  (hf : f.ker = ⊥) (hfg : g.ker = f.range) (hg : g.range = ⊤)

-- i cba, these shouldn't exist. not sure which hyps i need
lemma cochains_ses_left_exact (ι : Type*) (hf : f.ker = ⊥) :
  (f.comp_left ι).ker = ⊥ := sorry

lemma cochains_ses_exact (ι : Type*) (hf : f.ker = ⊥) (hfg : g.ker = f.range) :
  (g.comp_left ι).ker = (f.comp_left ι).range :=
sorry

lemma cochains_ses_right_exact (ι : Type*) (hg : g.range = ⊤) :
  (g.comp_left ι).range = ⊤ := sorry

lemma invariants_ses_left_exact (hf : f.ker = ⊥) :
  (invariants_map ρ f).ker = ⊥ := sorry

lemma invariants_ses_exact (hf : f.ker = ⊥) (hfg : g.ker = f.range) :
  (invariants_map τ g).ker = (invariants_map ρ f).range :=
sorry

def invariants_connecting_hom_aux (hf : f.ker = ⊥) (hfg : g.ker = f.range) (hg : g.range = ⊤)
  (x : invariants σ P) : one_cocycles ρ :=
begin
  rw linear_map.range_eq_top at hg,
  let X := classical.some (hg (x : P)),
  let hX : g X = x := classical.some_spec (hg (x : P)),
  have HXx : (λ g : G, ρ g X - X) ∈ (g.comp_left G).ker :=
  begin
    rw linear_map.mem_ker,
    ext y,
    dsimp,
    sorry, --rw [g.coe_fn_coe, distrib_mul_action_hom.map_sub, g.map_smul, hX, coe_invariants y, sub_self],
  end,
  erw cochains_ses_exact _ _ _ f g _ _ G hf hfg at HXx,
  let Y := classical.some HXx,
  let hY : (f.comp_left G) Y = (λ g : G, ρ g X - X) := classical.some_spec HXx,
  use Y,
  sorry,
end

def invariants_connecting_hom (hf : f.ker = ⊥) (hfg : g.ker = f.range)
  (hg : g.range = ⊤) : invariants σ P →ₗ[k] firstcoh ρ :=
(submodule.mkq _).comp ⟨invariants_connecting_hom_aux _ _ _ f g _ _ hf hfg hg, sorry, sorry⟩

lemma connecting_hom_exact (hf : f.ker = ⊥)
  (hfg : g.ker = f.range)
  (hg : g.range = ⊤) :
  (invariants_connecting_hom _ _ _ f g _ _ hf hfg hg).ker = (invariants_map τ g).range := sorry

--lol.
end stuff
