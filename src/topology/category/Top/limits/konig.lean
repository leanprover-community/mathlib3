/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import topology.category.Top.limits.basic

/-!
# Topological Kőnig's lemma

A topological version of Kőnig's lemma is that the inverse limit of nonempty compact Hausdorff
spaces is nonempty.  (Note: this can be generalized further to inverse limits of nonempty compact
T0 spaces, where all the maps are closed maps; see [Stone1979] --- however there is an erratum
for Theorem 4 that the element in the inverse limit can have cofinally many components that are
not closed points.)

We give this in a more general form, which is that cofiltered limits
of nonempty compact Hausdorff spaces are nonempty
(`nonempty_limit_cone_of_compact_t2_cofiltered_system`).

This also applies to inverse limits, where `{J : Type u} [preorder J] [is_directed J (≤)]` and
`F : Jᵒᵖ ⥤ Top`.

The theorem is specialized to nonempty finite types (which are compact Hausdorff with the
discrete topology) in lemmas `nonempty_sections_of_finite_cofiltered_system` and
`nonempty_sections_of_finite_inverse_system` in the file `category_theory.cofiltered_system`.

(See <https://stacks.math.columbia.edu/tag/086J> for the Set version.)
-/

open category_theory
open category_theory.limits

universes u v w

noncomputable theory

namespace Top

section topological_konig

variables {J : Type u} [small_category J]
variables (F : J ⥤ Top.{u})

private abbreviation finite_diagram_arrow {J : Type u} [small_category J] (G : finset J) :=
Σ' (X Y : J) (mX : X ∈ G) (mY : Y ∈ G), X ⟶ Y
private abbreviation finite_diagram (J : Type u) [small_category J] :=
Σ (G : finset J), finset (finite_diagram_arrow G)

/--
Partial sections of a cofiltered limit are sections when restricted to
a finite subset of objects and morphisms of `J`.
-/
def partial_sections {J : Type u} [small_category J] (F : J ⥤ Top.{u})
  {G : finset J} (H : finset (finite_diagram_arrow G)) : set (Π j, F.obj j) :=
{ u | ∀ {f : finite_diagram_arrow G} (hf : f ∈ H), F.map f.2.2.2.2 (u f.1) = u f.2.1 }

lemma partial_sections.nonempty [is_cofiltered_or_empty J] [h : Π (j : J), nonempty (F.obj j)]
  {G : finset J} (H : finset (finite_diagram_arrow G)) :
  (partial_sections F H).nonempty :=
begin
  classical,
  casesI is_empty_or_nonempty J,
  { exact ⟨is_empty_elim, λ j, is_empty.elim' infer_instance j.1⟩ },
  haveI : is_cofiltered J := ⟨⟩,
  use λ (j : J), if hj : j ∈ G
                 then F.map (is_cofiltered.inf_to G H hj) (h (is_cofiltered.inf G H)).some
                 else (h _).some,
  rintros ⟨X, Y, hX, hY, f⟩ hf,
  dsimp only,
  rwa [dif_pos hX, dif_pos hY, ←comp_app, ←F.map_comp,
       @is_cofiltered.inf_to_commutes _ _ _ G H],
end

lemma partial_sections.directed :
  directed superset (λ (G : finite_diagram J), partial_sections F G.2) :=
begin
  classical,
  intros A B,
  let ιA : finite_diagram_arrow A.1 → finite_diagram_arrow (A.1 ⊔ B.1) :=
    λ f, ⟨f.1, f.2.1, finset.mem_union_left _ f.2.2.1, finset.mem_union_left _ f.2.2.2.1,
          f.2.2.2.2⟩,
  let ιB : finite_diagram_arrow B.1 → finite_diagram_arrow (A.1 ⊔ B.1) :=
    λ f, ⟨f.1, f.2.1, finset.mem_union_right _ f.2.2.1, finset.mem_union_right _ f.2.2.2.1,
          f.2.2.2.2⟩,
  refine ⟨⟨A.1 ⊔ B.1, A.2.image ιA ⊔ B.2.image ιB⟩, _, _⟩,
  { rintro u hu f hf,
    have : ιA f ∈ A.2.image ιA ⊔ B.2.image ιB,
    { apply finset.mem_union_left,
      rw finset.mem_image,
      refine ⟨f, hf, rfl⟩ },
    exact hu this },
  { rintro u hu f hf,
    have : ιB f ∈ A.2.image ιA ⊔ B.2.image ιB,
    { apply finset.mem_union_right,
      rw finset.mem_image,
      refine ⟨f, hf, rfl⟩ },
    exact hu this }
end

lemma partial_sections.closed [Π (j : J), t2_space (F.obj j)]
  {G : finset J} (H : finset (finite_diagram_arrow G)) :
  is_closed (partial_sections F H) :=
begin
  have : partial_sections F H =
    ⋂ {f : finite_diagram_arrow G} (hf : f ∈ H), { u | F.map f.2.2.2.2 (u f.1) = u f.2.1 },
  { ext1,
    simp only [set.mem_Inter, set.mem_set_of_eq],
    refl, },
  rw this,
  apply is_closed_bInter,
  intros f hf,
  apply is_closed_eq,
  continuity,
end

/--
Cofiltered limits of nonempty compact Hausdorff spaces are nonempty topological spaces.
-/
lemma nonempty_limit_cone_of_compact_t2_cofiltered_system
  [is_cofiltered_or_empty J]
  [Π (j : J), nonempty (F.obj j)]
  [Π (j : J), compact_space (F.obj j)]
  [Π (j : J), t2_space (F.obj j)] :
  nonempty (Top.limit_cone.{u} F).X :=
begin
  classical,
  obtain ⟨u, hu⟩ := is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
    (λ G, partial_sections F _)
    (partial_sections.directed F)
    (λ G, partial_sections.nonempty F _)
    (λ G, is_closed.is_compact (partial_sections.closed F _))
    (λ G, partial_sections.closed F _),
  use u,
  intros X Y f,
  let G : finite_diagram J :=
    ⟨{X, Y},
     {⟨X, Y,
      by simp only [true_or, eq_self_iff_true, finset.mem_insert],
      by simp only [eq_self_iff_true, or_true, finset.mem_insert, finset.mem_singleton],
      f⟩}⟩,
  exact hu _ ⟨G, rfl⟩ (finset.mem_singleton_self _),
end

end topological_konig

end Top
