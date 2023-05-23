/-
Copyright (c) 2023 Emily Witt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Witt, Scott Morrison
-/
import ring_theory.ideal.basic
import algebra.category.Module.colimits
import algebra.category.Module.projective
import category_theory.abelian.ext
import category_theory.limits.final

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

section local_cohomology

variables {R : Type} [comm_ring R] {D : Type} [category.{0} D]

local attribute [ext] quiver.hom.unop_inj

/--  The directed system of `R`-modules of the form `R/J`, where `J` is an ideal of `R`,
determined by the functor `I`, represented as a functor  -/
def ring_mod_ideals (I : D ⥤ ideal R) : D ⥤ Module.{0} R :=
{ obj := λ t, Module.of R $ R ⧸ (I.obj t),
  map := λ s t w, submodule.mapq _ _ (linear_map.id) (I.map w).down.down }

/-- The diagram we will take the colimit of to define local cohomology, corresponding to the
directed system determined by the functor `I` -/
def local_cohomology_diagram (I : D ⥤ ideal R) (i : ℕ) : Dᵒᵖ ⥤ Module.{0} R ⥤ Module.{0} R :=
(ring_mod_ideals I).op ⋙ Ext R (Module.{0} R) i

/-- `local_cohomology I i` is `i`-th the local cohomology module of a module `M` over a
commutative ring `R` with support in an ideal whose powers are cofinal with a collection of ideals
of `R` that is represented as a functor `I` -/
def local_cohomology (I : D ⥤ ideal R) (i : ℕ) : Module.{0} R ⥤ Module.{0} R :=
colimit (local_cohomology_diagram I i)

/-- The functor sending a natural number `i` to the `i`-th power of the ideal `J` -/
def ideal_powers (J : ideal R) : ℕᵒᵖ ⥤ ideal R := {
  obj := λ t, J^(unop t),
  map := λ s t w, ⟨⟨ideal.pow_le_pow w.unop.down.down⟩⟩, }

set_option pp.universes true
/-- `local_cohomology_powers J i` is `i`-th the local cohomology module of a module `M` over
a commutative ring `R` with support in the ideal `J` of `R` -/
def local_cohomology_powers (J : ideal R) (i : ℕ) : Module.{0} R ⥤ Module.{0} R :=
  local_cohomology (ideal_powers J) i

/-- The directed system of all ideals with the same radical as a given ideal -/
@[reducible] def ideals_with_same_radical (J : ideal R) :=
full_subcategory (λ J' : ideal R, J'.radical = J.radical)
/-- The diagram of all ideals with the same radical as a given ideal -/
def same_radical_diagram (J : ideal R) : (ideals_with_same_radical J) ⥤ ideal R :=
full_subcategory_inclusion _

/-- The diagram of all ideals with the same radical as `J`. This is the "largest" diagram that
computes local cohomology with support in `J`. -/
def local_cohomology_univ_diagram (J : ideal R) (i : ℕ) :
  (ideals_with_same_radical J)ᵒᵖ ⥤ Module.{0} R ⥤ Module.{0} R :=
local_cohomology_diagram (same_radical_diagram J) i

/-- Local cohomology as the direct limit of Ext(R/J, M) over all ideals with the same radical
as `J`. -/
def local_cohomology_univ (J : ideal R) (i : ℕ) : Module.{0} R ⥤ Module.{0} R :=
colimit (local_cohomology_univ_diagram J i)
-- TODO: Construct `local_cohomology_powers J i ≅ local_cohomology_univ J i`

end local_cohomology
