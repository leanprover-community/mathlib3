/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Heather Macbeth
-/
import topology.uniform_space.pi
import data.matrix.basic

/-!
# Uniform space structure on matrices
-/

open_locale uniformity topology

variables (m n 𝕜 : Type*) [uniform_space 𝕜]

namespace matrix

instance : uniform_space (matrix m n 𝕜) :=
(by apply_instance : uniform_space (m → n → 𝕜))

lemma uniformity :
  𝓤 (matrix m n 𝕜) = ⨅ (i : m) (j : n), (𝓤 𝕜).comap (λ a, (a.1 i j, a.2 i j)) :=
begin
  erw [Pi.uniformity, Pi.uniformity],
  simp_rw [filter.comap_infi, filter.comap_comap],
  refl,
end

lemma uniform_continuous {β : Type*} [uniform_space β] {f : β → matrix m n 𝕜} :
  uniform_continuous f ↔ ∀ i j, uniform_continuous (λ x, f x i j) :=
by simp only [uniform_continuous, matrix.uniformity, filter.tendsto_infi, filter.tendsto_comap_iff]

instance [complete_space 𝕜] : complete_space (matrix m n 𝕜) :=
(by apply_instance : complete_space (m → n → 𝕜))

instance [separated_space 𝕜] : separated_space (matrix m n 𝕜) :=
(by apply_instance : separated_space (m → n → 𝕜))

end matrix
