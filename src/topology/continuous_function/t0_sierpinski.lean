/-
Copyright (c) 2022 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
import topology.order
import topology.continuous_function.basic

/-!
# Any T0 space embeds in a product of copies of the Sierpinski space

We consider `Prop` with the Sierpinski topology. If `(X, t)` is a topological space, there is a
continuous map `i : X → Π u ∈ t, Prop` defined as the product of the maps `iᵤ : X → Prop` defined by
`iᵤ x = x ∈ u`. The map `i` is always inducing. Whenever `X` is T0, `i` is also injective and
therefore an embedding.
-/

noncomputable theory

variables {X : Type*} [t : topological_space X] [t0 : t0_space X]

instance : topological_space (Π (u : {s : set X | t.is_open s}), Prop) :=
@Pi.topological_space _ (λ u, Prop) (λ u, sierpinski_space)

/--
  The continuous map from `X` to the product of copies of the Sierpinski space, (one copy for each
  open subset `u` of `X`). The `u` coordinate of  `i x` is given by `x ∈ u`.
-/
def i (X : Type*) [t : topological_space X] : continuous_map X
  (Π (u : {s : set X | t.is_open s}), Prop) :=
{ to_fun := λ x u, x ∈ (u : set X),
  continuous_to_fun := continuous_pi_iff.2 (λ u, continuous_Prop.2 (by simpa using subtype.mem u)) }

include t0
lemma i_injective : function.injective
  (λ (x : X) (u : {s : set X | t.is_open s}), x ∈ (u : set X)) :=
begin
  rw function.injective,
  intros x1 x2 h,
  by_contra' c,
  cases (t0_space_def X).1 t0 x1 x2 c with u hu,
  apply (xor_iff_not_iff _ _).1 hu.2,
  simpa only [eq_iff_iff, subtype.coe_mk] using congr_fun h ⟨u, hu.1⟩
 end
 omit t0

lemma eq_induced_by_maps_to_sierpinski : t = ⨅ (u : {s : set X | t.is_open s}),
   topological_space.induced (λ x, x ∈ (u : set X)) sierpinski_space :=
begin
  apply le_antisymm,
  { apply le_infi_iff.2 _,
    exact λ u, continuous.le_induced (is_open_iff_continuous_mem.1 u.2) },
  { apply is_open_implies_is_open_iff.mp,
    intros u h,
    apply is_open_implies_is_open_iff.mpr _ u _,
    { exact topological_space.induced (λ (x : X), x ∈ u) sierpinski_space },
    { exact infi_le_of_le ⟨u,h⟩ (by simp) },
    { apply is_open_induced_iff'.mpr,
      exact ⟨{true}, ⟨is_open_singleton_true,by simp [set.preimage]⟩⟩ } }
end

include t
lemma i_inducing : inducing (i X).to_fun :=
⟨(eq_induced_by_maps_to_sierpinski).trans begin
  erw induced_infi, -- same steps as in the proof of `inducing_infi_to_pi`
  congr' 1,
  funext,
  erw induced_compose,
  refl
end⟩

-- would `embedding_into_prod_sierpinski_of_t0` be a good name?
theorem i_embedding : embedding (i X) := embedding.mk (i_inducing) (@i_injective X t t0)
