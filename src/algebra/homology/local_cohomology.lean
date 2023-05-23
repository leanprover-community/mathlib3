/-
Copyright (c) 2023 Emily Witt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Witt, Scott Morrison, Jake Levinson, Sam van Gool
-/
import ring_theory.ideal.basic
import algebra.category.Module.colimits
import algebra.category.Module.projective
import category_theory.abelian.ext
import ring_theory.finiteness

/-!
# Local cohomology.

This file defines the `i`-th local cohomology module of an `R`-module `M` with support in an
ideal `I` of `R`, where `R` is a commutative ring, as the direct limit of Ext modules:

Given a collection of ideals cofinal with the powers of `I`, consider the directed system of
quotients of `R` by these ideals, and take the direct limit of the system induced on the `i`-th
Ext into `M`.  One can, of course, take the collection to simply be the integral powers of `I`.

## References

* [M. Hochster, *Local cohomology*][hochsterunpublished]
  <https://dept.math.lsa.umich.edu/~hochster/615W22/lcc.pdf>
* [R. Hartshorne, *Local cohomology: A seminar given by A. Grothendieck*][hartshorne61]
* [M. Brodmann and R. Sharp, *Local cohomology: An algebraic introduction with geometric
  applications*][brodmannsharp13]
* [S. Iyengar, G. Leuschke, A. Leykin, Anton, C. Miller, E. Miller, A. Singh, U. Walther,
  *Twenty-four hours of local cohomology*][iyengaretal13]

## Tags

local cohomology, local cohomology modules

## Future work

* Prove that this definition is equivalent to:
    * the right-derived functor definition
    * the characterization as the limit of Koszul homology
    * the characterization as the cohomology of a Cech-like complex
* Prove that local cohomology depends only on the radical of the ideal
* Establish long exact sequence(s) in local cohomology
-/

open opposite
open category_theory
open category_theory.limits

noncomputable theory

universes u v

/- We define local cohomology, implemented as a direct limit of Ext(R/J, --). -/
namespace local_cohomology

section
variables {R : Type u} [comm_ring R] {D : Type v} [small_category D]

/--  The directed system of `R`-modules of the form `R/J`, where `J` is an ideal of `R`,
determined by the functor `I`  -/
def ring_mod_ideals (I : D ⥤ ideal R) : D ⥤ Module.{u} R :=
{ obj := λ t, Module.of R $ R ⧸ (I.obj t),
  map := λ s t w, submodule.mapq _ _ (linear_map.id) (I.map w).down.down }

/-- The diagram we will take the colimit of to define local cohomology, corresponding to the
directed system determined by the functor `I` -/
def diagram (I : D ⥤ ideal R) (i : ℕ) : Dᵒᵖ ⥤ Module.{u} R ⥤ Module.{u} R :=
(ring_mod_ideals I).op ⋙ Ext R (Module.{u} R) i

end

section
-- We momentarily need to work with a type inequality, as later we will take colimits
-- along diagrams either in Type, or in the same universe as the ring, and we need to cover both.
variables {R : Type max u v} [comm_ring R] {D : Type v} [small_category D]

/-- `local_cohomology.of_diagram I i` is the the functor sending an module `M` over a commutative
ring `R` to the direct limit of `Ext^i(R/J, M)`, where `J` ranges over a collection of ideals
of `R`, represented as a functor `I`. -/
/-
In this definition we do not assume any special property of the diagram `I`, but the relevant case
will be where `I` is (cofinal with) the diagram of powers of a single given ideal.

Below, we give two equivalent (to be shown) definitions of the usual local cohomology with support
in an ideal `J`, `local_cohomology` and `local_cohomology.of_radical_eq_radical`.

TODO: Show that any functor cofinal with `I` gives the same result.
 -/
def of_diagram (I : D ⥤ ideal R) (i : ℕ) :
  Module.{max u v} R ⥤ Module.{max u v} R :=
colimit (diagram.{(max u v) v} I i)

end

section diagrams

variables {R : Type u} [comm_ring R]

/-- The functor sending a natural number `i` to the `i`-th power of the ideal `J` -/
def ideal_powers (J : ideal R) : ℕᵒᵖ ⥤ ideal R :=
{ obj := λ t, J^(unop t),
  map := λ s t w, ⟨⟨ideal.pow_le_pow w.unop.down.down⟩⟩, }

/-- The full subcategory of all ideals with the same radical as a given ideal `J` -/
@[reducible] def ideals_with_same_radical (J : ideal R) : Type u :=
full_subcategory (λ J' : ideal R, J.radical ≤ J'.radical)

/-- The diagram of all ideals with the same radical as `J`, represented as a functor.
This is the "largest" diagram that computes local cohomology with support in `J`. -/
def same_radical_diagram (J : ideal R) : (ideals_with_same_radical J) ⥤ ideal R :=
full_subcategory_inclusion _

end diagrams

end local_cohomology

/- We give two models for the local cohomology with support in an ideal `J`: first in terms of
the powers of `J` (`local_cohomology`), then in terms of all ideals with the same radical
as `J` (`local_cohomology.of_radical_eq_radical`). -/
section models_for_local_cohomology

open local_cohomology

variables {R : Type u} [comm_ring R]

/-- `local_cohomology J i` is `i`-th the local cohomology module of a module `M` over
a commutative ring `R` with support in the ideal `J` of `R`, defined as the direct limit
of Ext(R/J^t, M) over all powers `t`. -/
def local_cohomology (J : ideal R) (i : ℕ) : Module.{u} R ⥤ Module.{u} R :=
  of_diagram (ideal_powers J) i

/-- Local cohomology as the direct limit of Ext(R/J, M) over *all* ideals with the same radical
as `J`. -/
def of_radical_eq_radical (J : ideal R) (i : ℕ) :
  Module.{u} R ⥤ Module.{u} R :=
of_diagram.{u} (same_radical_diagram.{u} J) i
-- TODO: Construct `local_cohomology J i ≅ local_cohomology.of_radical_eq_radical J i`

end models_for_local_cohomology


section local_cohomology_equiv

open local_cohomology

variables {R : Type u} [comm_ring R] (I J : ideal R)

/-- Lifting the `ideal_powers J` diagram from a diagram valued in `ideals R` to a diagram
valued in `ideals_with_same_radical J`. -/
def ideal_powers_same_radical (J : ideal R) : ℕᵒᵖ ⥤ ideals_with_same_radical J :=
full_subcategory.lift _ (ideal_powers J)
(λ k, begin
  change _ ≤ (J^(unop k)).radical,
  cases (unop k),
  { simp only [ideal.radical_mono, pow_zero, ideal.one_eq_top, le_top] },
  { calc J.radical ≤ J.radical            : le_refl _
              ...  = (J ^ n.succ).radical : (J.radical_pow _ n.succ_pos).symm },
end)

/-- The composition with the inclusion into `ideals R` is isomorphic to `ideal_powers J`. -/
def ideal_powers_same_radical_lift_comp_inclusion (J : ideal R) :
ideal_powers_same_radical J ⋙ same_radical_diagram J ≅ ideal_powers J :=
  full_subcategory.lift_comp_inclusion _ _ _

/-- For our purposes, the lemma below essentially says that `ideal_powers_same_radical I` is
initial in `same_radical_diagram I`.

PORTING NOTE: This lemma should probably be moved to `ring_theory/finiteness.lean`
to be near `ideal.exists_radical_pow_le_of_fg` -/
lemma exists_pow_le_of_radical_le_of_fg (hIJ : I.radical ≤ J.radical) (hJ : J.radical.fg) :
  ∃ (k : ℕ), I^k ≤ J :=
begin
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ,
  use k,
  calc I^k ≤ I.radical^k : ideal.pow_mono (ideal.le_radical) _
       ... ≤ J.radical^k : ideal.pow_mono hIJ _
       ... ≤ J           : hk,
end

end local_cohomology_equiv
