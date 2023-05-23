/-
Copyright (c) 2023 Emily Witt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Witt, Scott Morrison, Jake Levinson, Sam van Gool
-/
import ring_theory.ideal.basic
import algebra.category.Module.colimits
import algebra.category.Module.projective
import category_theory.abelian.ext
import category_theory.limits.final
import ring_theory.noetherian

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

section local_cohomology

section
variables {R : Type u} [comm_ring R] {D : Type v} [small_category D]

local attribute [ext] quiver.hom.unop_inj

/--  The directed system of `R`-modules of the form `R/J`, where `J` is an ideal of `R`,
determined by the functor `I`, represented as a functor  -/
def ring_mod_ideals (I : D ⥤ ideal R) : D ⥤ Module.{u} R :=
{ obj := λ t, Module.of R $ R ⧸ (I.obj t),
  map := λ s t w, submodule.mapq _ _ (linear_map.id) (I.map w).down.down }

/-- The diagram we will take the colimit of to define local cohomology, corresponding to the
directed system determined by the functor `I` -/
def local_cohomology_diagram (I : D ⥤ ideal R) (i : ℕ) : Dᵒᵖ ⥤ Module.{u} R ⥤ Module.{u} R :=
(ring_mod_ideals I).op ⋙ Ext R (Module.{u} R) i

end

section
-- We momentarily need to work with a type inequality, as later we will take colimits
-- along diagrams either in Type, or in the same universe as the ring, and we need to cover both.
variables {R : Type max u v} [comm_ring R] {D : Type v} [small_category D]

/-- `local_cohomology I i` is `i`-th the local cohomology module of a module `M` over a
commutative ring `R` with support in an ideal whose powers are cofinal with a collection of ideals
of `R` that is represented as a functor `I` -/
def local_cohomology_of_diagram (I : D ⥤ ideal R) (i : ℕ) : Module.{max u v} R ⥤ Module.{max u v} R :=
colimit (local_cohomology_diagram.{(max u v) v} I i)

end

section
variables {R : Type u} [comm_ring R]

/-- The functor sending a natural number `i` to the `i`-th power of the ideal `J` -/
def ideal_powers (J : ideal R) : ℕᵒᵖ ⥤ ideal R :=
{ obj := λ t, J^(unop t),
  map := λ s t w, ⟨⟨ideal.pow_le_pow w.unop.down.down⟩⟩, }

/-- `local_cohomology_powers J i` is `i`-th the local cohomology module of a module `M` over
a commutative ring `R` with support in the ideal `J` of `R` -/
def local_cohomology_powers (J : ideal R) (i : ℕ) : Module.{u} R ⥤ Module.{u} R :=
  local_cohomology_of_diagram (ideal_powers J) i

/-- The directed system of all ideals with the same radical as a given ideal -/
@[reducible] def ideals_with_same_radical (J : ideal R) : Type u :=
full_subcategory (λ J' : ideal R, J'.radical = J.radical)

/-- The diagram of all ideals with the same radical as `J`. This is the "largest" diagram
that computes local cohomology with support in `J`. -/
def same_radical_diagram (J : ideal R) : (ideals_with_same_radical J) ⥤ ideal R :=
full_subcategory_inclusion _

/-- Local cohomology as the direct limit of Ext(R/J, M) over all ideals with the same radical
as `J`. -/
def local_cohomology_univ (J : ideal R) (i : ℕ) :
  Module.{u} R ⥤ Module.{u} R :=
local_cohomology_of_diagram.{u} (same_radical_diagram.{u} J) i
-- TODO: Construct `local_cohomology_powers J i ≅ local_cohomology_univ J i`

end

section local_cohomology_powers_equiv_univ

variables {R : Type} [comm_ring R] (I J : ideal R)

/-- This lemma essentially says that `ideal_powers I` is final in `same_radical_diagram I`.

Porting note: This lemma should probably be moved to `ring_theory/finiteness.lean`
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

end local_cohomology_powers_equiv_univ

section

variables {R : Type u} [comm_ring R]

def P (J : ideal R) : ℕᵒᵖ ⥤ ideals_with_same_radical J := sorry
def e (J : ideal R) : P J ⋙ same_radical_diagram J ≅ ideal_powers J := sorry
theorem P_final (J : ideal R) : functor.final (P J) := sorry

-- This is timing out, even with the proof by `sorry`!?
def foo (J : ideal R) (i : ℕ) :
  local_cohomology_powers J i ≅ local_cohomology_univ J i :=
sorry

def bar {I J : ideal R} (w : I.radical = J.radical) (i : ℕ) :
  local_cohomology_univ I i ≅ local_cohomology_univ J i :=
sorry

end

end local_cohomology
