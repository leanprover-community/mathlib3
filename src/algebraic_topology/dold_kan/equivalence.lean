/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.equivalence_pseudoabelian
import algebraic_topology.dold_kan.normalized

/-!

# The Dold-Kan correspondence

The Dold-Kan correspondence states that for any abelian category `A`, there is
an equivalence between the category of simplicial objects in `A` and the
category of chain complexes in `A` (with degrees indexed by `ℕ` and the
homological convention that the degree is decreased by the differentials).

In this file, we finish the construction of this equivalence by providing
`category_theory.abelian.dold_kan.equivalence` which is of type
`simplicial_object A ≌ chain_complex A ℕ` for any abelian category `A`.
The functor `simplicial_object A ⥤ chain_complex A ℕ` of this equivalence is
definitionally equal to `normalized_Moore_complex A`.

## Overall strategy of the proof of the correspondence

Before starting the implementation of the proof in Lean, the author noticed
that the Dold-Kan equivalence not only applies to abelian categories, but
should also hold generally for any pseudoabelian category `C`
(i.e. a category with instances `[preadditive C]`
`[has_finite_coproducts C]` and `[is_idempotent_complete C]`): this is
`category_theory.idempotents.dold_kan.equivalence`.

When the alternating face map complex `K[X]` of a simplicial object `X` in an
abelian is studied, it is shown that it decomposes as a direct sum of the
normalized subcomplex and of the degenerate subcomplex. The crucial observation
is that in this decomposition, the projection on the normalized subcomplex can
be defined in each degree using simplicial operators. Then, the definition
of this projection `P_infty : K[X] ⟶ K[X]` can be carried for any
`X : simplicial_object C` when `C` is a preadditive category.

The construction of the endomorphism `P_infty` is done in the files
`homotopies.lean`, `faces.lean`, `projections.lean` and `p_infty.lean`.
Eventually, as we would also like to show that the inclusion of the normalized
Moore complex is an homotopy equivalence (cf. file `homotopy_equivalence.lean`),
this projection `P_infty` needs to be homotopic to the identity. In our
construction, we get this for free because `P_infty` is obtained by altering
the identity endomorphism by null homotopic maps. More details about this
aspect of the proof are in the file `homotopies.lean`.

When the alternating face map complex `K[X]` is equipped with the idempotent
endomorphism `P_infty`, it becomes an object in `karoubi (chain_complex C ℕ)`
which is the idempotent completion of the category `chain_complex C ℕ`. In `functor_n.lean`,
we obtain this functor `N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)`,
which is formally extended as
`N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)`. (Here, some functors
have an index which is the number of occurrences of `karoubi` at the source or the
target.)

In `functor_gamma.lean`, assuming that the category `C` is additive,
we define the functor in the other direction
`Γ₂ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C)` as the formal
extension of a functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C` which is
defined similarly as in *Simplicial Homotopy Theory* by Goerss-Jardine.
In `degeneracies.lean`, we show that `P_infty` vanishes on the image of degeneracy
operators, which is one of the key properties that makes possible to contruct
the isomorphism `N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (karoubi (chain_complex C ℕ))`.

The rest of the proof follows the strategy in the original paper by Dold. We show
that the functor `N₂` reflects isomorphisms in `n_reflects_iso.lean`: this relies on a
decomposition of the identity of `X _[n]` using `P_infty.f n` and degeneracies obtained in
`decomposition.lean`. Then, in `n_comp_gamma.lean`, we construct a natural transformation
`Γ₂N₂.trans : N₂ ⋙ Γ₂ ⟶ 𝟭 (karoubi (simplicial_object C))`. It is shown that it is an
isomorphism using the fact thet `N₂` reflects isomorphisms, and because we can show
that the composition `N₂ ⟶ N₂ ⋙ Γ₂ ⋙ N₂ ⟶ N₂` is the identity (see `identity_N₂`). The fact
that `N₂` is defined as a formal direct factor makes the proof easier because we only
have to compare endomorphisms of an alternating face map complex `K[X]` and we do not
have to worry with inclusions of kernel subobjects.

In `equivalence_additive.lean`, we obtain
the equivalence `equivalence : karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ)`.
It is in the namespace `category_theory.preadditive.dold_kan`. The functors in this
equivalence are named `N` and `Γ`: by definition, they are `N₂` and `Γ₂`.

In `equivalence_pseudoabelian.lean`, assuming `C` is idempotent complete,
we obtain `equivalence : simplicial_object C ≌ chain_complex C ℕ`
in the namespace `category_theory.idempotents.dold_kan`. This could be roughly
obtained by composing the previous equivalence with the equivalences
`simplicial_object C ≌ karoubi (simplicial_object C)` and
`karoubi (chain_complex C ℕ) ≌ chain_complex C ℕ`. Instead, we polish this construction
in `compatibility.lean` by ensuring good definitional properties of the equivalence (e.g.
the inverse functor is definitionallly equal to
`Γ₀' : chain_complex C ℕ ⥤ simplicial_object C`) and
showing compatibilities for the unit and counit isomorphisms.

In this file `equivalence.lean`, assuming the category `A` is abelian, we obtain
`equivalence : simplicial_object A ≌ chain_complex A ℕ` in the namespace
`category_theory.abelian.dold_kan`. This is obtained by replacing the functor
`category_theory.idempotents.dold_kan.N` of the equivalence in the pseudoabelian case
with the isomorphic functor `normalized_Moore_complex A` thanks to the isomorphism
obtained in `normalized.lean`.

TODO: Show functoriality properties of the three equivalences above. More precisely,
for example in the case of abelian categories `A` and `B`, if `F : A ⥤ B` is an
additive functor, we can show that the functor `N` for `A` and `B` are compatible
with the functors `simplicial_object A ⥤ simplicial_object B` and
`chain_complex A ℕ ⥤ chain_complex B ℕ` induced by `F`. (Note that this does not
require that `F` is an exact functor!)

TODO: Introduce the degenerate subcomplex `D[X]` which is generated by
degenerate simplices, show that the projector `P_infty` corresponds to
a decomposition `K[X] ≅ N[X] ⊞ D[X]`.

TODO: dualise all of this as `cosimplicial_object A ⥤ cochain_complex A ℕ`. (It is unclear
what is the best way to do this. The exact design may be decided when it is needed.)

## References
* Albrecht Dold, Homology of Symmetric Products and Other Functors of Complexes,
Annals of Mathematics, Second Series, Vol. 68 No. 1 (Jul. 1958), pp. 54-80.
* Paul G. Goerss, John F. Jardine, Simplicial Homotopy Theory, Modern Birkhäuser Classics,
Reprint of the 1999 edition.

-/

noncomputable theory

open category_theory
open category_theory.category
open category_theory.idempotents

variables {A : Type*} [category A] [abelian A]

namespace category_theory

namespace abelian

namespace dold_kan

open algebraic_topology.dold_kan

/-- The functor `N` for the equivalence is `normalized_Moore_complex A` -/
def N : simplicial_object A ⥤ chain_complex A ℕ := algebraic_topology.normalized_Moore_complex A

/-- The functor `Γ` for the equivalence is the same as in the pseudoabelian case. -/
def Γ : chain_complex A ℕ ⥤ simplicial_object A := idempotents.dold_kan.Γ

/-- The comparison isomorphism between `normalized_Moore_complex A` and
the functor `idempotents.dold_kan.N` from the pseudoabelian case -/
@[simps]
def comparison_N : (N : simplicial_object A ⥤ _) ≅ idempotents.dold_kan.N :=
calc N ≅ N ⋙ 𝟭 _ : functor.left_unitor N
... ≅ N ⋙ ((to_karoubi_equivalence _).functor ⋙ (to_karoubi_equivalence _).inverse) :
  iso_whisker_left _ (to_karoubi_equivalence _).unit_iso
... ≅ (N ⋙ (to_karoubi_equivalence _).functor) ⋙ (to_karoubi_equivalence _).inverse :
  iso.refl _
... ≅ N₁ ⋙ (to_karoubi_equivalence _).inverse : iso_whisker_right
  (N₁_iso_normalized_Moore_complex_comp_to_karoubi A).symm _
... ≅ idempotents.dold_kan.N : by refl

/-- The Dold-Kan equivalence for abelian categories -/
@[simps functor]
def equivalence : simplicial_object A ≌ chain_complex A ℕ :=
begin
  let F : simplicial_object A ⥤ _ := idempotents.dold_kan.N,
  let hF : is_equivalence F := is_equivalence.of_equivalence idempotents.dold_kan.equivalence,
  letI : is_equivalence (N : simplicial_object A ⥤ _ ) :=
    is_equivalence.of_iso comparison_N.symm hF,
  exact N.as_equivalence,
end

lemma equivalence_inverse : (equivalence : simplicial_object A ≌ _).inverse = Γ := rfl

end dold_kan

end abelian

end category_theory
