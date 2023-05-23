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

universes u v w

section local_cohomology

variables {R : Type u} [comm_ring R]

variables {D : Type} [small_category D] (I : Dᵒᵖ ⥤ ideal R)

local attribute [ext] quiver.hom.unop_inj

/--  The directed system of `R`-modules of the form `R/J`, where `J` is an ideal of `R`,
determined by the functor `I`, represented as a functor  -/
def ring_mod_ideals : D ⥤ (Module.{u} R)ᵒᵖ :=
{ obj := λ t, op $ Module.of R $ R ⧸ (I.obj (op t)),
  map := λ s t w, quiver.hom.op $
  submodule.mapq (I.obj (op t)) (I.obj (op s)) (linear_map.id)
  $ (I.map w.op).down.down }

/-- The diagram we will take the colimit of to define local cohomology, corresponding to the
directed system determined by the functor `I` -/
def local_cohomology_diagram (i : ℕ) :
   D ⥤ Module.{u} R ⥤ Module.{u} R :=
ring_mod_ideals I ⋙ Ext R (Module.{u} R) i

/-- local_cohomology `R` `I` `i` is `i`-th the local cohomology module of a module `M` over a
commutative ring `R` with support in an ideal whose powers are cofinal with a collection of ideals
of `R` that is represented as a functor `I` -/
def local_cohomology (i : ℕ) : Module.{u} R ⥤ Module.{u} R :=
colimit (local_cohomology_diagram I i)

/-- The functor sending a natural number `i` to the `i`-th power of the ideal `J` -/
def ideal_powers (J : ideal R) : ℕᵒᵖ ⥤ ideal R := {
  obj := λ t, J^(unop t),
  map := λ s t w, ⟨⟨ideal.pow_le_pow w.unop.down.down⟩⟩, }

/-- local_cohomology_powers `R` `J` `i` is `i`-th the local cohomology module of a module `M` over
a commutative ring `R` with support in the ideal `J` of `R` -/
def local_cohomology_powers (J : ideal R) (M : Module.{} R) :=
  local_cohomology (ideal_powers J)

end local_cohomology
