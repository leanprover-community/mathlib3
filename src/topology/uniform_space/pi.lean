/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import topology.uniform_space.cauchy
import topology.uniform_space.separation

/-!
# Indexed product of uniform spaces
-/

noncomputable theory

open_locale uniformity topological_space

section
open filter uniform_space function
universe u
variables {ι : Type*} (α : ι → Type u) [U : Πi, uniform_space (α i)]
include U

instance Pi.uniform_space : uniform_space (Πi, α i) :=
uniform_space.of_core_eq
  (⨅i, uniform_space.comap (λ a : Πi, α i, a i) (U i)).to_core
  Pi.topological_space $ eq.symm to_topological_space_infi

lemma Pi.uniform_space_eq :
  Pi.uniform_space α = (⨅i, uniform_space.comap (λ a : Πi, α i, a i) (U i)) :=
of_core_eq_to_core _ _ _

lemma Pi.uniformity :
  𝓤 (Π i, α i) = ⨅ i : ι, filter.comap (λ a, (a.1 i, a.2 i)) $ 𝓤 (α i) :=
infi_uniformity

variable {α}

lemma uniform_continuous_pi {β : Type*} [uniform_space β] {f : β → Π i, α i} :
  uniform_continuous f ↔ ∀ i, uniform_continuous (λ x, f x i) :=
by simp only [uniform_continuous, Pi.uniformity, tendsto_infi, tendsto_comap_iff]

variable (α)

lemma Pi.uniform_continuous_proj (i : ι) : uniform_continuous (λ (a : Π (i : ι), α i), a i) :=
uniform_continuous_pi.1 uniform_continuous_id i

lemma cauchy_pi [nonempty ι] {l : filter (Π i, α i)} :
  cauchy l ↔ ∀ i, cauchy (map (eval i) l) :=
by simp_rw [cauchy, forall_and_distrib, map_ne_bot_iff, forall_const ι, prod_map_map_eq,
            map_le_iff_le_comap, Pi.uniformity, le_infi_iff]

lemma cauchy_pi' {l : filter (Π i, α i)} [l.ne_bot] :
  cauchy l ↔ ∀ i, cauchy (map (eval i) l) :=
by simp_rw [cauchy_of_ne_bot, prod_map_map_eq, map_le_iff_le_comap, Pi.uniformity, le_infi_iff]

instance Pi.complete [∀ i, complete_space (α i)] : complete_space (Π i, α i) :=
⟨begin
  intros f hf,
  haveI := hf.1,
  have : ∀ i, ∃ x : α i, filter.map (λ a : Πi, α i, a i) f ≤ 𝓝 x,
  { intro i,
    have key : cauchy (map (λ (a : Π (i : ι), α i), a i) f),
      from hf.map (Pi.uniform_continuous_proj α i),
    exact cauchy_iff_exists_le_nhds.1 key },
  choose x hx using this,
  use x,
  rwa [nhds_pi, le_pi],
end⟩

instance Pi.separated [∀ i, separated_space (α i)] : separated_space (Π i, α i) :=
separated_def.2 $ assume x y H,
begin
  ext i,
  apply eq_of_separated_of_uniform_continuous (Pi.uniform_continuous_proj α i),
  apply H,
end
end
