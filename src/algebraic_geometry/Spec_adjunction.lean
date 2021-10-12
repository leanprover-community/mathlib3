/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import algebraic_geometry.Scheme
import ring_theory.ideal.operations

/-!

# Adjunction between `Spec` and `Γ`

-/

noncomputable theory

open category_theory
open topological_space
open opposite

namespace algebraic_geometry

namespace LocallyRingedSpace

variables (X : LocallyRingedSpace)

def to_prime_spectrum : X → prime_spectrum (Γ.obj (op X)) := λ x,
⟨ideal.comap (X.presheaf.germ (⟨x, trivial⟩ : (⊤ : opens X)))
  (local_ring.maximal_ideal (X.stalk x)),
begin
  haveI : ideal.is_prime (local_ring.maximal_ideal (X.stalk x)), apply_instance,
  apply ideal.is_prime.comap,
end⟩

@[simp]
lemma mem_to_prime_spectrum (f : Γ.obj (op X)) (x : X) :
  f ∈ (X.to_prime_spectrum x).as_ideal ↔
  ¬is_unit (X.presheaf.germ (⟨x, trivial⟩ : (⊤ : opens X)) f) :=
iff.rfl

lemma to_prime_spectrum_preim_basic_open (f : Γ.obj (op X)) :
  X.to_prime_spectrum ⁻¹' (prime_spectrum.basic_open f) = (X.to_RingedSpace.basic_open f).1 :=
set.ext $ λ x,
begin
  rw [set.mem_preimage, opens.mem_coe, prime_spectrum.mem_basic_open,
    mem_to_prime_spectrum, not_not],
  refl,
end

-- TODO: move this to topology/bases
lemma continuous_of_basis_is_open_preimage {α β : Type*} [topological_space α] [topological_space β]
  {B : set (set β)} (hB : is_topological_basis B) (f : α → β) (hf : ∀ s ∈ B, is_open (f ⁻¹' s)) :
  continuous f :=
begin rw hB.eq_generate_from, exact continuous_generated_from hf end

lemma continuous_to_prime_spectrum : continuous X.to_prime_spectrum :=
begin
  apply continuous_of_basis_is_open_preimage (prime_spectrum.is_topological_basis_basic_opens),
  rintros s ⟨f, rfl⟩,
  rw to_prime_spectrum_preim_basic_open,
  exact (X.to_RingedSpace.basic_open f).2,
end



end LocallyRingedSpace

end algebraic_geometry
