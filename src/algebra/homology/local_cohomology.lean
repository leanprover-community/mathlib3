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
* Establish long exact sequence(s) in local cohomology
-/

open opposite
open category_theory
open category_theory.limits

noncomputable theory

universes u v v'

namespace local_cohomology

/- We define local cohomology, implemented as a direct limit of `Ext(R/J, -)`. -/
section
variables {R : Type u} [comm_ring R] {D : Type v} [small_category D]

/--  The directed system of `R`-modules of the form `R/J`, where `J` is an ideal of `R`,
determined by the functor `I`  -/
def ring_mod_ideals (I : D ⥤ ideal R) : D ⥤ Module.{u} R :=
{ obj := λ t, Module.of R $ R ⧸ (I.obj t),
  map := λ s t w, submodule.mapq _ _ (linear_map.id) (I.map w).down.down }

/- TODO:  Once this file is ported, move this file to the right location. -/
instance Module_enough_projectives' : enough_projectives (Module.{u} R) :=
  Module.Module_enough_projectives.{u}

/-- The diagram we will take the colimit of to define local cohomology, corresponding to the
directed system determined by the functor `I` -/
def diagram (I : D ⥤ ideal R) (i : ℕ) : Dᵒᵖ ⥤ Module.{u} R ⥤ Module.{u} R :=
(ring_mod_ideals I).op ⋙ Ext R (Module.{u} R) i

end

section
-- We momentarily need to work with a type inequality, as later we will take colimits
-- along diagrams either in Type, or in the same universe as the ring, and we need to cover both.
variables {R : Type max u v} [comm_ring R] {D : Type v} [small_category D]

/-- `local_cohomology.of_diagram I i` is the the functor sending a module `M` over a commutative
ring `R` to the direct limit of `Ext^i(R/J, M)`, where `J` ranges over a collection of ideals
of `R`, represented as a functor `I`. -/
/-
In this definition we do not assume any special property of the diagram `I`, but the relevant case
will be where `I` is (cofinal with) the diagram of powers of a single given ideal.

Below, we give two equivalent definitions of the usual local cohomology with support
in an ideal `J`, `local_cohomology` and `local_cohomology.of_self_le_radical`.

 -/
def of_diagram (I : D ⥤ ideal R) (i : ℕ) :
  Module.{max u v} R ⥤ Module.{max u v} R :=
colimit (diagram.{(max u v) v} I i)

end

section
variables {R : Type max u v v'} [comm_ring R] {D : Type v} [small_category D]

variables {E : Type v'} [small_category E]
  (I' : E ⥤ D) (I : D ⥤ ideal R)

/-- Local cohomology along a composition of diagrams. -/
def diagram_comp (i : ℕ) : diagram (I' ⋙ I) i ≅ I'.op ⋙ (diagram I i) := iso.refl _

/-- Local cohomology agrees along precomposition with a cofinal diagram. -/
def iso_of_final [functor.initial I'] (i : ℕ) :
  of_diagram.{(max u v) v'} (I' ⋙ I) i ≅ of_diagram.{(max u v') v} I i :=
(has_colimit.iso_of_nat_iso (diagram_comp _ _ _))
≪≫ (functor.final.colimit_iso _ _)

end

section diagrams

variables {R : Type u} [comm_ring R]

/-- The functor sending a natural number `i` to the `i`-th power of the ideal `J` -/
def ideal_powers_diagram (J : ideal R) : ℕᵒᵖ ⥤ ideal R :=
{ obj := λ t, J^(unop t),
  map := λ s t w, ⟨⟨ideal.pow_le_pow w.unop.down.down⟩⟩, }

/-- The full subcategory of all ideals with radical containing `J` -/
@[derive category] def self_le_radical (J : ideal R) : Type u :=
full_subcategory (λ J' : ideal R, J ≤ J'.radical)

instance self_le_radical.inhabited (J : ideal R) : inhabited (self_le_radical J) :=
{ default := ⟨J, ideal.le_radical⟩ }

/-- The diagram of all ideals with radical containing `J`, represented as a functor.
This is the "largest" diagram that computes local cohomology with support in `J`. -/
def self_le_radical_diagram (J : ideal R) : (self_le_radical J) ⥤ ideal R :=
full_subcategory_inclusion _

end diagrams

end local_cohomology

/-! We give two models for the local cohomology with support in an ideal `J`: first in terms of
the powers of `J` (`local_cohomology`), then in terms of *all* ideals with radical
containing `J` (`local_cohomology.of_self_le_radical`). -/
section models_for_local_cohomology

open local_cohomology

variables {R : Type u} [comm_ring R]

/-- `local_cohomology J i` is `i`-th the local cohomology module of a module `M` over
a commutative ring `R` with support in the ideal `J` of `R`, defined as the direct limit
of `Ext^i(R/J^t, M)` over all powers `t : ℕ`. -/
def local_cohomology (J : ideal R) (i : ℕ) : Module.{u} R ⥤ Module.{u} R :=
of_diagram (ideal_powers_diagram J) i

/-- Local cohomology as the direct limit of `Ext^i(R/J', M)` over *all* ideals `J'` with radical
containing `J`. -/
def local_cohomology.of_self_le_radical (J : ideal R) (i : ℕ) : Module.{u} R ⥤ Module.{u} R :=
of_diagram.{u} (self_le_radical_diagram.{u} J) i

end models_for_local_cohomology

namespace local_cohomology

/-!
Showing equivalence of different definitions of local cohomology.
  * `local_cohomology.iso_self_le_radical` gives the isomorphism
      `local_cohomology J i ≅ local_cohomology.of_self_le_radical J i`
  * `local_cohomology.iso_of_same_radical` gives the isomorphism
      `local_cohomology J i ≅ local_cohomology K i` when `J.radical = K.radical`.
-/
section local_cohomology_equiv

variables {R : Type u} [comm_ring R]

/-- Lifting `ideal_powers_diagram J` from a diagram valued in `ideals R` to a diagram
valued in `self_le_radical J`. -/
def ideal_powers_to_self_le_radical (J : ideal R) : ℕᵒᵖ ⥤ self_le_radical J :=
full_subcategory.lift _ (ideal_powers_diagram J)
(λ k, begin
  change _ ≤ (J^(unop k)).radical,
  cases (unop k),
  { simp only [ideal.radical_top, pow_zero, ideal.one_eq_top, le_top] },
  { simp only [J.radical_pow _ n.succ_pos, ideal.le_radical] },
end)

variables {I J K : ideal R}

/--
PORTING NOTE: This lemma should probably be moved to `ring_theory/finiteness.lean`
to be near `ideal.exists_radical_pow_le_of_fg`, which it generalizes.
-/
lemma ideal.exists_pow_le_of_le_radical_of_fg (hIJ : I ≤ J.radical) (hJ : J.radical.fg) :
  ∃ (k : ℕ), I^k ≤ J :=
begin
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ,
  use k,
  calc I^k ≤ J.radical^k : ideal.pow_mono hIJ _
       ... ≤ J           : hk,
end

/-- The diagram of powers of `J` is initial in the diagram of all ideals with
radical containing `J`. This uses noetherianness. -/
instance ideal_powers_initial [hR : is_noetherian R R] :
  functor.initial (ideal_powers_to_self_le_radical J) :=
{ out := λ J', begin
  apply @zigzag_is_connected _ _ _,
  { intros j1 j2,
    apply relation.refl_trans_gen.single,
    -- The inclusions `J^n1 ≤ J'` and `J^n2 ≤ J'` always form a triangle, based on
    -- which exponent is larger.
    cases le_total (unop j1.left) (unop j2.left) with h,
      right, exact ⟨costructured_arrow.hom_mk (hom_of_le h).op (of_as_true trivial)⟩,
      left, exact ⟨costructured_arrow.hom_mk (hom_of_le h).op (of_as_true trivial)⟩ },
  { obtain ⟨k, hk⟩ := ideal.exists_pow_le_of_le_radical_of_fg J'.2
      (is_noetherian_def.mp hR _),
    exact ⟨costructured_arrow.mk (⟨⟨hk⟩⟩ : (ideal_powers_to_self_le_radical J).obj (op k) ⟶ J')⟩},
  end }

/-- Local cohomology (defined in terms of powers of `J`) agrees with local
cohomology computed over all ideals with radical containing `J`. -/
def iso_self_le_radical (J : ideal R) [is_noetherian R R] (i : ℕ) :
  local_cohomology.of_self_le_radical J i ≅ local_cohomology J i :=
(local_cohomology.iso_of_final.{u u 0}
  (ideal_powers_to_self_le_radical J) (self_le_radical_diagram J) i).symm
≪≫ has_colimit.iso_of_nat_iso (iso.refl _)

/-- Casting from the full subcategory of ideals with radical containing `J` to the full
subcategory of ideals with radical containing `K`. -/
def self_le_radical.cast (hJK : J.radical = K.radical) :
  self_le_radical J ⥤ self_le_radical K :=
full_subcategory.map (λ L hL, begin
                        rw ← ideal.radical_le_radical_iff at ⊢ hL,
                        exact hJK.symm.trans_le hL,
                      end)

instance self_le_radical.cast_is_equivalence (hJK : J.radical = K.radical) :
  is_equivalence (self_le_radical.cast hJK) :=
{ inverse := self_le_radical.cast hJK.symm,
  unit_iso := by tidy,
  counit_iso := by tidy }

/-- The natural isomorphism between local cohomology defined using the `of_self_le_radical`
diagram, assuming `J.radical = K.radical`. -/
def self_le_radical.iso_of_same_radical (hJK : J.radical = K.radical)  (i : ℕ) :
  of_self_le_radical J i ≅ of_self_le_radical K i :=
(iso_of_final.{u u u} (self_le_radical.cast hJK.symm) _ _).symm

/-- Local cohomology agrees on ideals with the same radical. -/
def iso_of_same_radical [is_noetherian R R] (hJK : J.radical = K.radical) (i : ℕ) :
  local_cohomology J i ≅ local_cohomology K i :=
(iso_self_le_radical J i).symm
≪≫ self_le_radical.iso_of_same_radical hJK i
≪≫ iso_self_le_radical K i

end local_cohomology_equiv

end local_cohomology
