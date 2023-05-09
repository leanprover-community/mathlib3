/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import topology.category.Top.limits.basic

/-!
# Cofiltered limits in Top.

Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/

open topological_space
open category_theory
open category_theory.limits

universes u v w

noncomputable theory

namespace Top

section cofiltered_limit

variables {J : Type v} [small_category J] [is_cofiltered J] (F : J ⥤ Top.{max v u})
  (C : cone F) (hC : is_limit C)

include hC

/--
Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/
theorem is_topological_basis_cofiltered_limit
  (T : Π j, set (set (F.obj j))) (hT : ∀ j, is_topological_basis (T j))
  (univ : ∀ (i : J), set.univ ∈ T i)
  (inter : ∀ i (U1 U2 : set (F.obj i)), U1 ∈ T i → U2 ∈ T i → U1 ∩ U2 ∈ T i)
  (compat : ∀ (i j : J) (f : i ⟶ j) (V : set (F.obj j)) (hV : V ∈ T j), (F.map f) ⁻¹' V ∈ T i) :
  is_topological_basis { U : set C.X | ∃ j (V : set (F.obj j)), V ∈ T j ∧ U = C.π.app j ⁻¹' V } :=
begin
  classical,
  -- The limit cone for `F` whose topology is defined as an infimum.
  let D := limit_cone_infi F,
  -- The isomorphism between the cone point of `C` and the cone point of `D`.
  let E : C.X ≅ D.X := hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit _),
  have hE : inducing E.hom := (Top.homeo_of_iso E).inducing,
  -- Reduce to the assertion of the theorem with `D` instead of `C`.
  suffices : is_topological_basis
    { U : set D.X | ∃ j (V : set (F.obj j)), V ∈ T j ∧ U = D.π.app j ⁻¹' V },
  { convert this.inducing hE,
    ext U0,
    split,
    { rintro ⟨j, V, hV, rfl⟩,
      refine ⟨D.π.app j ⁻¹' V, ⟨j, V, hV, rfl⟩, rfl⟩ },
    { rintro ⟨W, ⟨j, V, hV, rfl⟩, rfl⟩,
      refine ⟨j, V, hV, rfl⟩ } },
  -- Using `D`, we can apply the characterization of the topological basis of a
  -- topology defined as an infimum...
  convert is_topological_basis_infi hT (λ j (x : D.X), D.π.app j x),
  ext U0,
  split,
  { rintros  ⟨j, V, hV, rfl⟩,
    let U : Π i, set (F.obj i) := λ i, if h : i = j then (by {rw h, exact V}) else set.univ,
    refine ⟨U,{j},_,_⟩,
    { rintro i h,
      rw finset.mem_singleton at h,
      dsimp [U],
      rw dif_pos h,
      subst h,
      exact hV },
    { dsimp [U],
      simp } },
  { rintros ⟨U, G, h1, h2⟩,
    obtain ⟨j, hj⟩ := is_cofiltered.inf_objs_exists G,
    let g : ∀ e (he : e ∈ G), j ⟶ e := λ _ he, (hj he).some,
    let Vs : J → set (F.obj j) := λ e, if h : e ∈ G then F.map (g e h) ⁻¹' (U e) else set.univ,
    let V : set (F.obj j) := ⋂ (e : J) (he : e ∈ G), Vs e,
    refine ⟨j, V, _, _⟩,
    { -- An intermediate claim used to apply induction along `G : finset J` later on.
      have : ∀ (S : set (set (F.obj j))) (E : finset J) (P : J → set (F.obj j))
        (univ : set.univ ∈ S)
        (inter : ∀ A B : set (F.obj j), A ∈ S → B ∈ S → A ∩ B ∈ S)
        (cond : ∀ (e : J) (he : e ∈ E), P e ∈ S), (⋂ e (he : e ∈ E), P e) ∈ S,
      { intros S E,
        apply E.induction_on,
        { intros P he hh,
          simpa },
        { intros a E ha hh1 hh2 hh3 hh4 hh5,
          rw finset.set_bInter_insert,
          refine hh4 _ _ (hh5 _ (finset.mem_insert_self _ _)) (hh1 _ hh3 hh4 _),
          intros e he,
          exact hh5 e (finset.mem_insert_of_mem he) } },
      -- use the intermediate claim to finish off the goal using `univ` and `inter`.
      refine this _ _ _ (univ _) (inter _) _,
      intros e he,
      dsimp [Vs],
      rw dif_pos he,
      exact compat j e (g e he) (U e) (h1 e he), },
    { -- conclude...
      rw h2,
      dsimp [V],
      rw set.preimage_Inter,
      congr' 1,
      ext1 e,
      rw set.preimage_Inter,
      congr' 1,
      ext1 he,
      dsimp [Vs],
      rw [dif_pos he, ← set.preimage_comp],
      congr' 1,
      change _ = ⇑(D.π.app j ≫ F.map (g e he)),
      rw D.w } }
end

end cofiltered_limit

end Top
