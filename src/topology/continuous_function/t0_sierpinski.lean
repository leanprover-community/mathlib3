/-
Copyright (c) 2022 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
import topology.order
import topology.sets.opens
import topology.continuous_function.basic

/-!
# Any T0 space embeds in a product of copies of the Sierpinski space.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We consider `Prop` with the Sierpinski topology. If `X` is a topological space, there is a
continuous map `product_of_mem_opens` from `X` to `opens X → Prop` which is the product of the maps
`X → Prop` given by `x ↦ x ∈ u`.

The map `product_of_mem_opens` is always inducing. Whenever `X` is T0, `product_of_mem_opens` is
also injective and therefore an embedding.
-/

noncomputable theory

namespace topological_space

lemma eq_induced_by_maps_to_sierpinski (X : Type*) [t : topological_space X] :
  t = ⨅ (u : opens X), sierpinski_space.induced (∈ u) :=
begin
  apply le_antisymm,
  { rw [le_infi_iff],
    exact λ u, continuous.le_induced (is_open_iff_continuous_mem.mp u.2) },
  { intros u h,
    rw ← generate_from_Union_is_open,
    apply is_open_generate_from_of_mem,
    simp only [set.mem_Union, set.mem_set_of_eq, is_open_induced_iff],
    exact ⟨⟨u, h⟩, {true}, is_open_singleton_true, by simp [set.preimage]⟩ },
end

variables (X : Type*) [topological_space X]

/--
The continuous map from `X` to the product of copies of the Sierpinski space, (one copy for each
open subset `u` of `X`). The `u` coordinate of `product_of_mem_opens x` is given by `x ∈ u`.
-/
def product_of_mem_opens : C(X, opens X → Prop) :=
{ to_fun := λ x u, x ∈ u,
  continuous_to_fun := continuous_pi_iff.2 (λ u, continuous_Prop.2 u.is_open) }

lemma product_of_mem_opens_inducing : inducing (product_of_mem_opens X) :=
begin
  convert inducing_infi_to_pi (λ (u : opens X) (x : X), x ∈ u),
  apply eq_induced_by_maps_to_sierpinski,
end

lemma product_of_mem_opens_injective [t0_space X] : function.injective (product_of_mem_opens X) :=
begin
  intros x1 x2 h,
  apply inseparable.eq,
  rw [←inducing.inseparable_iff (product_of_mem_opens_inducing X), h],
 end

theorem product_of_mem_opens_embedding [t0_space X] : embedding (product_of_mem_opens X) :=
embedding.mk (product_of_mem_opens_inducing X) (product_of_mem_opens_injective X)

end topological_space
