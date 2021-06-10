/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import topology.category.Profinite

/-!
# Cofiltered limits of profinite sets.

This file contains some theorems about cofiltered limits of profinite sets.

## Main Results

- `exists_clopen_of_cofiltered` shows that any clopen set in a cofiltered limit of profinite
  sets is the pullback of a clopen set from one of the factors in the limit.
-/


namespace Profinite

open_locale classical
open category_theory
open category_theory.limits

universe u
variables {J : Type u} [small_category J] [is_cofiltered J]
  {F : J ⥤ Profinite.{u}} (C : cone F) (hC : is_limit C)

include hC

/--
If `X` is a cofiltered limit of profinite sets, then any clopen subset of `X` arises from
a clopen set in one of the terms in the limit.
-/
theorem exists_clopen_of_cofiltered {U : set C.X} (hU : is_clopen U) :
  ∃ (j : J) (V : set (F.obj j)) (hV : is_clopen V), U = C.π.app j ⁻¹' V :=
begin
  -- First, we have the topological basis of the cofiltered limit obtained by pulling back
  -- clopen sets from the factors in the limit. By continuity, all such sets are again clopen.
  have hB := Top.is_topological_basis_cofiltered_limit
    (F ⋙ Profinite_to_Top)
    (Profinite_to_Top.map_cone C)
    (is_limit_of_preserves _ hC)
    (λ j, {W | is_clopen W})
    _ (λ i, is_clopen_univ) (λ i U1 U2 hU1 hU2, hU1.inter hU2) _,
  rotate,
  { intros i,
    change topological_space.is_topological_basis
      {W : set (F.obj i) | is_clopen W},
    apply is_topological_basis_clopen },
  { rintros i j f V (hV : is_clopen _),
    refine ⟨hV.1.preimage _, hV.2.preimage _⟩;
    continuity },
  -- Using this, since `U` is open, we can write `U` as a union of clopen sets all of which
  -- are preimages of clopens from the factors in the limit.
  obtain ⟨S,hS,h⟩ := hB.open_eq_sUnion hU.1,
  clear hB,
  let j : S → J := λ s, (hS s.2).some,
  let V : Π (s : S), set (F.obj (j s)) := λ s, (hS s.2).some_spec.some,
  have hV : ∀ (s : S), is_clopen (V s) ∧ s.1 = C.π.app (j s) ⁻¹' (V s) :=
    λ s, (hS s.2).some_spec.some_spec,
  -- Since `U` is also closed, hence compact, it is covered by finitely many of the
  -- clopens constructed in the previous step.
  have := hU.2.is_compact.elim_finite_subcover (λ s : S, C.π.app (j s) ⁻¹' (V s)) _ _,
  rotate,
  { intros s,
    refine (hV s).1.1.preimage _,
    continuity },
  { dsimp only,
    rw h,
    rintro x ⟨T,hT,hx⟩,
    refine ⟨_,⟨⟨T,hT⟩,rfl⟩,_⟩,
    dsimp only,
    rwa ← (hV ⟨T,hT⟩).2 },
  -- We thus obtain a finite set `G : finset J` and a clopen set of `F.obj j` for each
  -- `j ∈ G` such that `U` is the union of the preimages of these clopen sets.
  obtain ⟨G,hG⟩ := this,
  -- Since `J` is cofiltered, we can find a single `j0` dominating all the `j ∈ G`.
  -- Pulling back all of the sets from the previous step to `F.obj j0` and taking a union,
  -- we obtain a clopen set in `F.obj j0` which works.
  obtain ⟨j0,hj0⟩ := is_cofiltered.inf_objs_exists (G.image j),
  let f : Π (s : S) (hs : s ∈ G), j0 ⟶ j s :=
    λ s hs, (hj0 (finset.mem_image.mpr ⟨s,hs,rfl⟩)).some,
  let W : S → set (F.obj j0) := λ s,
    if hs : s ∈ G then F.map (f s hs) ⁻¹' (V s) else set.univ,
  -- Conclude, using the `j0` and the clopen set of `F.obj j0` obtained above.
  refine ⟨j0, ⋃ (s : S) (hs : s ∈ G), W s, _, _⟩,
  { apply is_clopen_bUnion,
    intros s hs,
    dsimp only [W],
    rw dif_pos hs,
    refine ⟨(hV s).1.1.preimage _, (hV s).1.2.preimage _⟩;
    continuity },
  { ext x,
    split,
    { intro hx,
      simp_rw [set.preimage_Union, set.mem_Union],
      obtain ⟨_, ⟨s,rfl⟩, _, ⟨hs, rfl⟩, hh⟩ := hG hx,
      refine ⟨s, hs, _⟩,
      dsimp only [W] at hh ⊢,
      rwa [dif_pos hs, ← set.preimage_comp, ← Profinite.coe_comp, C.w] },
    { intro hx,
      simp_rw [set.preimage_Union, set.mem_Union] at hx,
      obtain ⟨s,hs,hx⟩ := hx,
      rw h,
      refine ⟨s.1,s.2,_⟩,
      rw (hV s).2,
      dsimp only [W] at hx,
      rwa [dif_pos hs, ← set.preimage_comp, ← Profinite.coe_comp, C.w] at hx } }
end

end Profinite
