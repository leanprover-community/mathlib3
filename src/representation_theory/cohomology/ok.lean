#exit
import representation_theory.cohomology.morestuff
import representation_theory.cohomology.sles
import representation_theory.cohomology.hmmmm
import field_theory.is_alg_closed.algebraic_closure
import field_theory.krull_topology
import ring_theory.roots_of_unity
universes v u
variables (k : Type u) [field k] (l : ℕ) (hl : (l : k) ≠ 0)
noncomputable theory
open intermediate_field

abbreviation separable_closure :=
Sup { F : intermediate_field k (algebraic_closure k) | is_separable k F }

def is_sep_closure (K : Type u) [field K] [algebra k K] [is_alg_closure k K]
  (F : intermediate_field k K) [is_separable k F] : Prop :=
∀ L : intermediate_field k K, is_separable k L → L ≤ F

local notation k`ˢ`:80 := separable_closure k

abbreviation abs_gal := kˢ ≃ₐ[k] (kˢ)

variables (A : Type u) [topological_space A] [discrete_topology A] [add_comm_group A]
  [distrib_mul_action (abs_gal k) A] [has_continuous_smul (abs_gal k) A]

abbreviation gal_coh (n : ℕ) := (cochain_cx (abs_gal k) A).homology n

abbreviation gal_invariants := invariants (abs_gal k) A

abbreviation first_gal_coh := firstcoh (abs_gal k) A

abbreviation wtf := (additive (roots_of_unity
  (⟨l, zero_lt_iff.2 $ λ h, hl $ by rw h; refl⟩) (kˢ)))

instance sfsfs (K : Type u) [field K] [algebra k K]
  (l : ℕ+) : distrib_mul_action (K ≃ₐ[k] K) (additive (roots_of_unity l K)) :=
{ smul := λ f, ((units.map (f.to_alg_hom : K →* K)).comp (roots_of_unity l K).subtype).cod_restrict _ sorry,
  one_smul := sorry,
  mul_smul := sorry,
  smul_add := sorry,
  smul_zero := sorry }

variables [topological_space (wtf k l hl)] [discrete_topology (wtf k l hl)]
instance : has_continuous_smul (abs_gal k) (wtf k l hl) := sorry

-- def/lemma timeout lol
lemma kummer :
  first_gal_coh k (wtf k l hl) ≃+ additive (kˣ ⧸ (@pow_monoid_hom kˣ _ l).range) := sorry
