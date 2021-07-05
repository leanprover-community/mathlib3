/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.pure

namespace affine
open set
variables {m n k : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E]
  {S : simplicial_complex E} {X Y : finset E} {A : set (finset E)}

/--
The k-skeleton of a simplicial complex is the simplicial complex made of its simplices of dimension
less than k.
-/
def simplicial_complex.skeleton (S : simplicial_complex E) (k : ℕ) :
  simplicial_complex E :=
simplicial_complex.of_surcomplex
  {X ∈ S.faces | finset.card X ≤ k + 1}
  (λ X ⟨hX, _⟩, hX)
  (λ X Y hX hY, ⟨S.down_closed hX.1 hY, le_trans (finset.card_le_of_subset hY) hX.2⟩)

lemma skeleton_subcomplex :
  (S.skeleton k).faces ⊆ S.faces :=
λ X ⟨hX, _⟩, hX

lemma skeleton_nonempty_iff :
  (S.skeleton k).faces.nonempty ↔ S.faces.nonempty :=
begin
  split,
  { apply nonempty.mono skeleton_subcomplex },
  { rintro ⟨X, hX⟩,
    exact ⟨∅, S.down_closed hX X.empty_subset, nat.zero_le _⟩ }
end

lemma pure_skeleton_of_pure [finite_dimensional ℝ E] (hS : S.pure_of n) :
  (S.skeleton k).pure_of (min n (k + 1)) :=
begin
  cases le_or_gt n (k + 1) with hmin hmin,
  { rw min_eq_left hmin,
    rintro X hXskel,
    obtain ⟨Y, hY, hXY⟩ := subfacet (skeleton_subcomplex (facets_subset hXskel)),
    have hYskel : Y ∈ (S.skeleton k).faces,
    { use facets_subset hY,
      simp,
      rw hS hY,
      exact hmin, },
    rw hXskel.2 hYskel hXY,
    exact hS hY },
  { rw min_eq_right (le_of_lt hmin),
    rintro X ⟨⟨hX, hXcard⟩, hXmax⟩,
    obtain ⟨Y, hY, hXY⟩ := subfacet hX,
    have : k + 1 - X.card + X.card ≤ Y.card,
    { rw hS hY,
      rw nat.sub_add_cancel hXcard,
      exact le_of_lt hmin, },
    obtain ⟨Z, hXZ, hZY, hZcard⟩ := finset.exists_intermediate_set (k + 1 - X.card) this hXY,
      rw nat.sub_add_cancel hXcard at hZcard,
    rw hXmax ⟨S.down_closed (facets_subset hY) hZY, le_of_eq hZcard⟩ hXZ,
    exact hZcard, }
end

lemma skeleton_pureness_eq_min_pureness_dimension [finite_dimensional ℝ E] (hS : S.pure)
  (hS' : S.faces.nonempty) :
  (S.skeleton k).pureness = min S.pureness (k + 1) :=
begin
  rcases hS with ⟨n, hn⟩,
  rw [pureness_def' hS' hn, pureness_def'],
  { rwa skeleton_nonempty_iff },
  { apply pure_skeleton_of_pure hn },
end

end affine
